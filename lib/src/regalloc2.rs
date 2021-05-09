//! Compatibility layer that allows us to use regalloc2.

#![allow(dead_code)]

use crate::analysis_main::AnalysisError;
use crate::checker::{CheckerContext, CheckerErrors};
use crate::data_structures::RegVecs;
use crate::inst_stream::{ExtPoint, InstExtPoint, InstToInsert, InstToInsertAndExtPoint};
use crate::{
    BlockIx, Function, InstIx, RealReg, RealRegUniverse, Reg, RegAllocError, RegAllocResult,
    RegClass, RegUsageCollector, RegUsageMapper, Set, SpillSlot, StackmapRequestInfo, TypedIxVec,
    VirtualReg, Writable,
};
use smallvec::{smallvec, SmallVec};

pub struct Shim<'a, F: Function> {
    // Register environment state. TODO: factor this out and allow
    // client to compute the converted env only once.
    rru: &'a RealRegUniverse,
    rregs_by_preg_index: Vec<RealReg>,
    pregs_by_rreg_index: Vec<regalloc2::PReg>,
    extra_scratch_by_class: Vec<regalloc2::PReg>,
    vreg_offset: usize,

    // Function-specific state.
    func: &'a mut F,
    succs: Vec<regalloc2::Block>,
    succ_ranges: Vec<(u32, u32)>,
    preds: Vec<regalloc2::Block>,
    pred_ranges: Vec<(u32, u32)>,
    operands: Vec<regalloc2::Operand>,
    operand_ranges: Vec<(u32, u32)>,
    reftype_vregs: Vec<regalloc2::VReg>,
    safepoints: regalloc2::bitvec::BitVec,
}

fn build_machine_env(
    rru: &RealRegUniverse,
    opts: &Regalloc2Options,
) -> (
    regalloc2::MachineEnv,
    Vec<RealReg>,
    Vec<regalloc2::PReg>,
    Vec<regalloc2::PReg>,
) {
    let mut regs = vec![];
    let mut preferred_regs_by_class = vec![vec![], vec![]];
    let mut non_preferred_regs_by_class = vec![vec![], vec![]];
    let mut scratch_by_class = vec![regalloc2::PReg::invalid(), regalloc2::PReg::invalid()];

    // For each reg in the RRU, create a PReg. Its hw_enc index is its
    // index in the class; note that we must have <= 32 regs per class
    // due to the bitpacking internal to regalloc2.

    // We only support I64 and V128 regclasses in this shim.
    assert_eq!(crate::NUM_REG_CLASSES, 5);
    assert!(rru.allocable_by_class[RegClass::rc_to_usize(RegClass::I32)].is_none());
    assert!(rru.allocable_by_class[RegClass::rc_to_usize(RegClass::F32)].is_none());
    assert!(rru.allocable_by_class[RegClass::rc_to_usize(RegClass::F64)].is_none());

    // PReg is limited to 64 (32 int, 32 float) regs due to
    // bitpacking, so just build full lookup tables in both
    // directions.
    let mut rregs_by_preg_idx = vec![RealReg::invalid(); 64];
    let mut pregs_by_rreg_idx = vec![regalloc2::PReg::invalid(); 64];

    let int_info = rru.allocable_by_class[RegClass::rc_to_usize(RegClass::I64)]
        .as_ref()
        .unwrap();
    assert!(int_info.suggested_scratch.is_some());
    let float_info = rru.allocable_by_class[RegClass::rc_to_usize(RegClass::V128)]
        .as_ref()
        .unwrap();
    assert!(float_info.suggested_scratch.is_some());

    let mut int_idx = 0;
    let mut float_idx = 0;
    for (rreg, _) in &rru.regs {
        let preg = match rreg.get_class() {
            RegClass::I64 => {
                let i = int_idx;
                int_idx += 1;
                regalloc2::PReg::new(i, regalloc2::RegClass::Int)
            }
            RegClass::V128 => {
                let i = float_idx;
                float_idx += 1;
                regalloc2::PReg::new(i, regalloc2::RegClass::Float)
            }
            _ => unreachable!(),
        };

        // We'll sort these by index below.
        regs.push(preg);

        rregs_by_preg_idx[preg.index()] = *rreg;
        pregs_by_rreg_idx[rreg.get_index()] = preg;

        if rreg.get_index() == int_info.suggested_scratch.unwrap() {
            scratch_by_class[0] = preg;
        } else if rreg.get_index() == float_info.suggested_scratch.unwrap() {
            scratch_by_class[1] = preg;
        } else if rreg.get_index() < rru.allocable {
            match preg.class() {
                regalloc2::RegClass::Int => {
                    if int_idx <= opts.num_int_preferred {
                        preferred_regs_by_class[0].push(preg);
                    } else {
                        non_preferred_regs_by_class[0].push(preg);
                    }
                }
                regalloc2::RegClass::Float => {
                    if float_idx <= opts.num_float_preferred {
                        preferred_regs_by_class[1].push(preg);
                    } else {
                        non_preferred_regs_by_class[1].push(preg);
                    }
                }
            }
        }
    }

    regs.sort_by_key(|preg| preg.index());

    // Grab an extra scratch reg for each class; we need this in the
    // (rare but possible) case that we need to do a stack-to-stack
    // move.
    let mut extra_scratch_by_class = vec![];
    extra_scratch_by_class.push(non_preferred_regs_by_class[0].pop().unwrap());
    extra_scratch_by_class.push(non_preferred_regs_by_class[1].pop().unwrap());

    let env = regalloc2::MachineEnv {
        regs,
        preferred_regs_by_class,
        non_preferred_regs_by_class,
        scratch_by_class,
    };
    (
        env,
        rregs_by_preg_idx,
        pregs_by_rreg_idx,
        extra_scratch_by_class,
    )
}

pub(crate) fn create_shim_and_env<'a, F: Function>(
    func: &'a mut F,
    rru: &'a RealRegUniverse,
    _sri: Option<&StackmapRequestInfo>,
    opts: &Regalloc2Options,
) -> (Shim<'a, F>, regalloc2::MachineEnv) {
    let (env, rregs_by_preg_index, pregs_by_rreg_index, extra_scratch_by_class) =
        build_machine_env(rru, opts);
    let vreg_offset = rregs_by_preg_index.len();
    let mut shim = Shim {
        rru,
        rregs_by_preg_index,
        pregs_by_rreg_index,
        vreg_offset,
        extra_scratch_by_class,

        func,
        succs: vec![],
        succ_ranges: vec![],
        preds: vec![],
        pred_ranges: vec![],
        operands: vec![],
        operand_ranges: vec![],
        reftype_vregs: vec![],
        safepoints: regalloc2::bitvec::BitVec::new(),
    };

    // Compute preds and succs in a regalloc2-compatible format.
    let mut edges: Vec<(usize, usize)> = vec![];
    for block in shim.func.blocks() {
        let start = shim.succs.len();
        for &succ in shim.func.block_succs(block).iter() {
            shim.succs.push(regalloc2::Block::new(succ.get() as usize));
            edges.push((block.get() as usize, succ.get() as usize));
        }
        // Remove duplicates.
        let end = shim.succs.len();
        shim.succs[start..end].sort_unstable();
        let mut out = start;
        for i in start..end {
            if i == start || shim.succs[i] != shim.succs[i - 1] {
                shim.succs[out] = shim.succs[i];
                out += 1;
            }
        }
        shim.succs.truncate(out);
        let end = shim.succs.len();
        shim.succ_ranges.push((start as u32, end as u32));
    }
    edges.sort_unstable_by_key(|(_from, to)| *to);
    let mut i = 0;
    for block in shim.func.blocks() {
        while i < edges.len() && edges[i].1 < block.get() as usize {
            i += 1;
        }
        let first_edge = i;
        while i < edges.len() && edges[i].1 == block.get() as usize {
            i += 1;
        }
        let edges = &edges[first_edge..i];

        let start = shim.preds.len();
        let mut last = None;
        for &(from, _) in edges {
            if Some(from) == last {
                continue;
            }
            shim.preds.push(regalloc2::Block::new(from));
            last = Some(from);
        }
        let end = shim.preds.len();
        shim.pred_ranges.push((start as u32, end as u32));
    }

    // Create a virtual entry instruction with livein defs.
    for &livein in shim.func.func_liveins().iter() {
        shim.operands.push(regalloc2::Operand::reg_def(
            shim.translate_realreg_to_vreg(livein),
        ));
    }
    shim.operand_ranges.push((0, shim.operands.len() as u32));

    // Create Operands for each reg use/def/mod in the function.
    let mut reg_vecs = RegVecs::new(false);
    let mut moves = 0;
    for (i, insn) in shim.func.insns().iter().enumerate() {
        reg_vecs.clear();
        let mut coll = RegUsageCollector::new(&mut reg_vecs);
        F::get_regs(insn, &mut coll);
        let start = shim.operands.len();
        if shim.func.is_move(insn).is_some() {
            moves += 1;
            // Moves are handled specially by the regalloc.
            shim.operand_ranges.push((start as u32, start as u32));
            continue;
        }
        for &u in &reg_vecs.uses {
            let vreg = shim.translate_reg_to_vreg(u);
            let policy = shim.translate_reg_to_policy(u);
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                policy,
                regalloc2::OperandKind::Use,
                regalloc2::OperandPos::Before,
            ));
        }
        for &d in &reg_vecs.defs {
            let vreg = shim.translate_reg_to_vreg(d);
            let policy = shim.translate_reg_to_policy(d);
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                policy,
                regalloc2::OperandKind::Def,
                regalloc2::OperandPos::After,
            ));
        }
        for &m in &reg_vecs.mods {
            let vreg = shim.translate_reg_to_vreg(m);
            let policy = shim.translate_reg_to_policy(m);
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                policy,
                regalloc2::OperandKind::Mod,
                regalloc2::OperandPos::Before,
            ));
        }
        // If this is a return, use all liveouts.
        if shim.func.is_ret(InstIx::new(i as u32)) {
            for &liveout in shim.func.func_liveouts().iter() {
                shim.operands.push(regalloc2::Operand::reg_use(
                    shim.translate_realreg_to_vreg(liveout),
                ));
            }
        }
        let end = shim.operands.len();
        log::debug!(
            "operands for inst {}: {:?}",
            shim.operand_ranges.len(),
            &shim.operands[start..end]
        );
        shim.operand_ranges.push((start as u32, end as u32));
    }

    log::info!(
        "regalloc2-to-regalloc shim: insns = {} moves = {}",
        shim.func.insns().len(),
        moves
    );

    // Compute safepoint map.
    // TODO

    log::debug!("env = {:?}", env);

    (shim, env)
}

fn edit_insts<'a, F: Function>(
    shim: &Shim<'a, F>,
    from: regalloc2::Allocation,
    to: regalloc2::Allocation,
) -> SmallVec<[InstToInsert; 2]> {
    if from.is_reg() && to.is_reg() {
        assert_eq!(to.as_reg().unwrap().class(), from.as_reg().unwrap().class());
        let to = shim.rregs_by_preg_index[to.as_reg().unwrap().index()];
        let from = shim.rregs_by_preg_index[from.as_reg().unwrap().index()];
        assert_eq!(to.get_class(), from.get_class());
        smallvec![InstToInsert::Move {
            to_reg: Writable::from_reg(to),
            from_reg: from,
            for_vreg: None
        }]
    } else if from.is_reg() && to.is_stack() {
        let from = shim.rregs_by_preg_index[from.as_reg().unwrap().index()];
        let to = SpillSlot::new(to.as_stack().unwrap().index() as u32);
        smallvec![InstToInsert::Spill {
            to_slot: to,
            from_reg: from,
            for_vreg: None
        }]
    } else if from.is_stack() && to.is_reg() {
        let to = shim.rregs_by_preg_index[to.as_reg().unwrap().index()];
        let from = SpillSlot::new(from.as_stack().unwrap().index() as u32);
        smallvec![InstToInsert::Reload {
            to_reg: Writable::from_reg(to),
            from_slot: from,
            for_vreg: None
        }]
    } else {
        let rc = from.class();
        let from = SpillSlot::new(from.as_stack().unwrap().index() as u32);
        let to = SpillSlot::new(to.as_stack().unwrap().index() as u32);
        let scratch =
            shim.rregs_by_preg_index[shim.extra_scratch_by_class[rc as u8 as usize].index()];
        smallvec![
            InstToInsert::Reload {
                to_reg: Writable::from_reg(scratch),
                from_slot: from,
                for_vreg: None
            },
            InstToInsert::Spill {
                to_slot: to,
                from_reg: scratch,
                for_vreg: None,
            },
        ]
    }
}

struct Mapper<'a, 'b, F: Function> {
    shim: &'b Shim<'a, F>,
    operands: &'b [regalloc2::Operand],
    allocs: &'b [regalloc2::Allocation],
}

impl<'a, 'b, F: Function> std::fmt::Debug for Mapper<'a, 'b, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "mapper({:?}, {:?})", self.operands, self.allocs)
    }
}

impl<'a, 'b, F: Function> Mapper<'a, 'b, F> {
    fn get_vreg_at_point(&self, vreg: VirtualReg, pos: regalloc2::OperandPos) -> Option<RealReg> {
        let vreg = self.shim.translate_virtualreg_to_vreg(vreg);
        for (i, op) in self.operands.iter().enumerate() {
            if op.vreg() == vreg && op.pos() == pos {
                if self.allocs[i].is_reg() {
                    return Some(
                        self.shim.rregs_by_preg_index[self.allocs[i].as_reg().unwrap().index()],
                    );
                } else {
                    return None;
                }
            }
        }
        None
    }
}

impl<'a, 'b, F: Function> RegUsageMapper for Mapper<'a, 'b, F> {
    fn get_use(&self, vreg: VirtualReg) -> Option<RealReg> {
        self.get_vreg_at_point(vreg, regalloc2::OperandPos::Before)
    }

    fn get_def(&self, vreg: VirtualReg) -> Option<RealReg> {
        self.get_vreg_at_point(vreg, regalloc2::OperandPos::After)
    }

    fn get_mod(&self, vreg: VirtualReg) -> Option<RealReg> {
        self.get_vreg_at_point(vreg, regalloc2::OperandPos::Before)
    }
}

fn edit_insn_registers<'a, F: Function>(
    bix: BlockIx,
    iix: InstIx,
    insn: &mut F::Inst,
    shim: &Shim<'a, F>,
    out: &regalloc2::Output,
    clobbers: &mut Set<RealReg>,
    checker: &mut Option<CheckerContext>,
) -> Result<(), CheckerErrors> {
    let (op_start, op_end) = shim.operand_ranges[(iix.get() + 1) as usize];
    let operands = &shim.operands[op_start as usize..op_end as usize];
    let allocs = &out.allocs[op_start as usize..op_end as usize];
    let mapper = Mapper {
        shim,
        operands,
        allocs,
    };
    F::map_regs(insn, &mapper);

    if let Some(checker) = checker.as_mut() {
        checker.handle_insn(shim.rru, shim.func, bix, iix, &mapper)?;
    }

    if shim.func.is_included_in_clobbers(insn) {
        for (op, alloc) in operands.iter().zip(allocs.iter()) {
            if op.kind() != regalloc2::OperandKind::Use && alloc.is_reg() {
                let rreg = shim.rregs_by_preg_index[alloc.as_reg().unwrap().index()];
                assert!(rreg.is_valid());
                clobbers.insert(rreg);
            }
        }
    }

    Ok(())
}

fn compute_insts_to_add<'a, F: Function>(
    shim: &Shim<'a, F>,
    out: &regalloc2::Output,
) -> Vec<InstToInsertAndExtPoint> {
    let mut ret = vec![];
    for (pos, edit) in &out.edits {
        let pos = if pos.inst().index() == 0 {
            InstExtPoint::new(InstIx::new(0), ExtPoint::Reload)
        } else {
            InstExtPoint::new(
                InstIx::new((pos.inst().index() - 1) as u32),
                match pos.pos() {
                    regalloc2::InstPosition::Before => ExtPoint::Reload,
                    regalloc2::InstPosition::After => ExtPoint::Spill,
                },
            )
        };
        match edit {
            &regalloc2::Edit::Move { from, to } => {
                for edit in edit_insts(shim, from, to) {
                    ret.push(InstToInsertAndExtPoint::new(edit, pos.clone()));
                }
            }
            _ => {}
        }
    }
    ret
}

pub(crate) fn finalize<'a, F: Function>(
    shim: Shim<'a, F>,
    out: regalloc2::Output,
    run_checker: bool,
) -> Result<RegAllocResult<F>, RegAllocError> {
    let mut checker = if run_checker {
        Some(CheckerContext::new(
            shim.func,
            shim.rru,
            &compute_insts_to_add(&shim, &out),
            /* TODO stackmap_info */ None,
        ))
    } else {
        None
    };

    let mut new_insns = vec![];
    let nop = shim.func.gen_zero_len_nop();
    let mut edit_idx = 0;
    let mut target_map: TypedIxVec<BlockIx, InstIx> = TypedIxVec::new();
    let mut orig_insn_map: TypedIxVec<InstIx, InstIx> = TypedIxVec::new();
    let mut clobbers = Set::empty();
    for block in shim.func.blocks() {
        target_map.push(InstIx::new(new_insns.len() as u32));
        for iix in shim.func.block_insns(block) {
            let i = iix.get() as usize;
            let mut insn = std::mem::replace(&mut shim.func.insns_mut()[i], nop.clone());

            // i + 1 because of entry inst.
            let pos = regalloc2::ProgPoint::before(regalloc2::Inst::new(i + 1));
            while edit_idx < out.edits.len() && out.edits[edit_idx].0 <= pos {
                assert_eq!(out.edits[edit_idx].0, pos);
                match &out.edits[edit_idx].1 {
                    &regalloc2::Edit::Move { from, to } => {
                        for inst in edit_insts(&shim, from, to) {
                            new_insns.push(inst.construct(shim.func).unwrap());
                            orig_insn_map.push(InstIx::invalid_value());
                        }
                    }
                    _ => {}
                }
                edit_idx += 1;
            }

            // regalloc2 handles moves on its own -- we do not need to
            // edit them here (and in fact it will fail, as there will
            // be no corresponding operands).
            if shim.func.is_move(&insn).is_none() {
                edit_insn_registers(
                    block,
                    iix,
                    &mut insn,
                    &shim,
                    &out,
                    &mut clobbers,
                    &mut checker,
                )
                .map_err(|err| RegAllocError::RegChecker(err))?;
                orig_insn_map.push(iix);
                new_insns.push(insn);
            }

            let pos = regalloc2::ProgPoint::after(regalloc2::Inst::new(i + 1));
            while edit_idx < out.edits.len() && out.edits[edit_idx].0 <= pos {
                assert_eq!(out.edits[edit_idx].0, pos);
                match &out.edits[edit_idx].1 {
                    &regalloc2::Edit::Move { from, to } => {
                        for inst in edit_insts(&shim, from, to) {
                            new_insns.push(inst.construct(shim.func).unwrap());
                            orig_insn_map.push(InstIx::invalid_value());
                        }
                    }
                    _ => {}
                }
                edit_idx += 1;
            }
        }
    }

    if let Some(checker) = checker.take() {
        checker
            .run()
            .map_err(|err| RegAllocError::RegChecker(err))?;
    }

    Ok(RegAllocResult {
        insns: new_insns,
        target_map,
        orig_insn_map,
        clobbered_registers: clobbers,
        num_spill_slots: out.num_spillslots as u32,
        block_annotations: None,
        stackmaps: vec![],
        new_safepoint_insns: vec![],
    })
}

fn translate_rc(rc: RegClass) -> regalloc2::RegClass {
    match rc {
        RegClass::I64 => regalloc2::RegClass::Int,
        RegClass::V128 => regalloc2::RegClass::Float,
        _ => unimplemented!("Only I64 and V128 regclasses are used"),
    }
}

fn translate_to_rc(rc: regalloc2::RegClass) -> RegClass {
    match rc {
        regalloc2::RegClass::Int => RegClass::I64,
        regalloc2::RegClass::Float => RegClass::V128,
    }
}

impl<'a, F: Function> Shim<'a, F> {
    fn translate_realreg_to_preg(&self, reg: RealReg) -> regalloc2::PReg {
        self.pregs_by_rreg_index[reg.get_index()]
    }

    fn translate_realreg_to_vreg(&self, reg: RealReg) -> regalloc2::VReg {
        let preg = self.translate_realreg_to_preg(reg);
        regalloc2::VReg::new(preg.index(), preg.class())
    }

    fn translate_virtualreg_to_vreg(&self, reg: VirtualReg) -> regalloc2::VReg {
        let rc = reg.get_class();
        let trc = translate_rc(rc);
        regalloc2::VReg::new(reg.get_index() + self.vreg_offset, trc)
    }

    fn translate_reg_to_vreg(&self, reg: Reg) -> regalloc2::VReg {
        if reg.is_real() {
            self.translate_realreg_to_vreg(reg.to_real_reg())
        } else {
            self.translate_virtualreg_to_vreg(reg.to_virtual_reg())
        }
    }

    fn translate_vreg_to_reg(&self, vreg: regalloc2::VReg) -> Reg {
        if vreg.vreg() >= self.vreg_offset {
            let idx = vreg.vreg() - self.vreg_offset;
            Reg::new_virtual(translate_to_rc(vreg.class()), idx as u32)
        } else {
            let idx = vreg.vreg();
            self.rregs_by_preg_index[idx].to_reg()
        }
    }

    fn translate_reg_to_policy(&self, _reg: Reg) -> regalloc2::OperandPolicy {
        // We use the pinned-register mechanism to pin RealReg vregs,
        // so we don't need a fixed-reg policy here.
        regalloc2::OperandPolicy::Reg
    }
}

impl<'a, F: Function> regalloc2::Function for Shim<'a, F> {
    fn insts(&self) -> usize {
        // Add 1 for the virtual entry instruction.
        self.func.insns().len() + 1
    }

    fn blocks(&self) -> usize {
        self.func.blocks().len()
    }

    fn entry_block(&self) -> regalloc2::Block {
        // Only 0 is supported, to keep the virtual entry instruction
        // handling simple.
        assert_eq!(self.func.entry_block().get(), 0);
        regalloc2::Block::new(0)
    }

    fn block_insns(&self, block: regalloc2::Block) -> regalloc2::InstRange {
        let range = self.func.block_insns(BlockIx::new(block.index() as u32));
        let mut start = regalloc2::Inst::new(range.first().get() as usize);
        let mut end = regalloc2::Inst::new(range.first().get() as usize + range.len());
        // Virtual entry instruction offsets by 1.
        if block.index() > 0 {
            start = start.next();
        }
        end = end.next();
        regalloc2::InstRange::forward(start, end)
    }

    fn block_succs(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        let (start, end) = self.succ_ranges[block.index()];
        &self.succs[start as usize..end as usize]
    }

    fn block_preds(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        let (start, end) = self.pred_ranges[block.index()];
        &self.preds[start as usize..end as usize]
    }

    fn block_params(&self, _block: regalloc2::Block) -> &[regalloc2::VReg] {
        // We don't use blockparams.
        &[]
    }

    fn is_call(&self, _insn: regalloc2::Inst) -> bool {
        // We don't have this info in regalloc1 interface, but it is
        // just for heuristics, not strictly needed.
        false
    }

    fn is_ret(&self, insn: regalloc2::Inst) -> bool {
        if insn.index() == 0 {
            false
        } else {
            self.func.is_ret(InstIx::new((insn.index() as u32) - 1))
        }
    }

    fn is_branch(&self, _insn: regalloc2::Inst) -> bool {
        // Only needed if we use blockparams.
        false
    }

    fn branch_blockparam_arg_offset(
        &self,
        _block: regalloc2::Block,
        _insn: regalloc2::Inst,
    ) -> usize {
        // We don't use blockparams.
        0
    }

    fn is_safepoint(&self, insn: regalloc2::Inst) -> bool {
        self.safepoints.get(insn.index())
    }

    fn is_move(&self, insn: regalloc2::Inst) -> Option<(regalloc2::VReg, regalloc2::VReg)> {
        if insn.index() == 0 {
            return None;
        }
        let insn = insn.index() - 1;
        let inst = &self.func.insns()[insn];
        self.func
            .is_move(inst)
            .map(|(dst, src)| {
                (
                    self.translate_reg_to_vreg(src),
                    self.translate_reg_to_vreg(dst.to_reg()),
                )
            })
            .filter(|(dst, src)| dst.class() == src.class())
    }

    // --------------------------
    // Instruction register slots
    // --------------------------

    fn inst_operands(&self, insn: regalloc2::Inst) -> &[regalloc2::Operand] {
        let (start, end) = self.operand_ranges[insn.index()];
        &self.operands[start as usize..end as usize]
    }

    fn inst_clobbers(&self, _insn: regalloc2::Inst) -> &[regalloc2::PReg] {
        // We don't use clobbers; we translate the regalloc1 func's
        // never-used defs.
        &[]
    }

    fn num_vregs(&self) -> usize {
        self.vreg_offset + self.func.get_num_vregs()
    }

    fn reftype_vregs(&self) -> &[regalloc2::VReg] {
        &self.reftype_vregs[..]
    }

    fn spillslot_size(&self, regclass: regalloc2::RegClass, _for_vreg: regalloc2::VReg) -> usize {
        let regclass = match regclass {
            regalloc2::RegClass::Int => RegClass::I64,
            regalloc2::RegClass::Float => RegClass::V128,
        };
        self.func.get_spillslot_size(regclass, None) as usize
    }

    fn multi_spillslot_named_by_last_slot(&self) -> bool {
        false
    }

    fn is_pinned_vreg(&self, vreg: regalloc2::VReg) -> Option<regalloc2::PReg> {
        if vreg.vreg() < self.vreg_offset {
            Some(regalloc2::PReg::from_index(vreg.vreg()))
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub struct Regalloc2Options {
    pub num_int_preferred: usize,
    pub num_float_preferred: usize,
}

impl std::default::Default for Regalloc2Options {
    fn default() -> Self {
        Self {
            num_int_preferred: 8,
            num_float_preferred: 8,
        }
    }
}

pub(crate) fn run<F: Function>(
    func: &mut F,
    rreg_universe: &RealRegUniverse,
    stackmap_info: Option<&StackmapRequestInfo>,
    run_checker: bool,
    opts: &Regalloc2Options,
) -> Result<RegAllocResult<F>, RegAllocError> {
    let (ra2_func, env) = create_shim_and_env(func, rreg_universe, stackmap_info, opts);
    let result = regalloc2::run(&ra2_func, &env).map_err(|err| match err {
        regalloc2::RegAllocError::CritEdge(from, to) => {
            RegAllocError::Analysis(AnalysisError::CriticalEdge {
                from: BlockIx::new(from.index() as u32),
                to: BlockIx::new(to.index() as u32),
            })
        }
        _ => RegAllocError::Other(format!("{:?}", err)),
    })?;
    finalize(ra2_func, result, run_checker)
}
