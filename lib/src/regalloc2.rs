//! Compatibility layer that allows us to use regalloc2.

use crate::{
    BlockIx, Function, InstIx, RealReg, RealRegUniverse, Reg, RegAllocError, RegAllocResult,
    RegClass, RegUsageCollector, RegVecs, StackmapRequestInfo, VirtualReg,
};

#[derive(Debug)]
pub struct Shim<'a, F: Function> {
    func: &'a F,
    rru: &'a RealRegUniverse,
    succs: Vec<regalloc2::Block>,
    succ_ranges: Vec<(u32, u32)>,
    preds: Vec<regalloc2::Block>,
    pred_ranges: Vec<(u32, u32)>,
    operands: Vec<regalloc2::Operand>,
    operand_ranges: Vec<(u32, u32)>,
    rregs_by_preg_index: Vec<RealReg>,
    vreg_offset: usize,
    reftype_vregs: Vec<regalloc2::VReg>,
    safepoints: regalloc2::bitvec::BitVec,
}

fn build_machine_env(
    rru: &RealRegUniverse,
    opts: &Regalloc2Options,
) -> (regalloc2::MachineEnv, Vec<RealReg>) {
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

    let mut rregs_by_preg_idx = vec![RealReg::invalid(); 64];

    let int_info = rru.allocable_by_class[RegClass::rc_to_usize(RegClass::I64)]
        .as_ref()
        .unwrap();
    assert!(int_info.suggested_scratch.is_some());
    for i in int_info.first..int_info.last {
        let idx = i - int_info.first;
        let rreg = rru.regs[i].0;
        let preg = regalloc2::PReg::new(idx, regalloc2::RegClass::Int);
        rregs_by_preg_idx[preg.index()] = rreg;
        regs.push(preg);
        if i == int_info.suggested_scratch.unwrap() {
            scratch_by_class[0] = preg;
        } else if i < rru.allocable {
            if idx < opts.num_int_preferred {
                preferred_regs_by_class[0].push(preg);
            } else {
                non_preferred_regs_by_class[0].push(preg);
            }
        }
    }

    let float_info = rru.allocable_by_class[RegClass::rc_to_usize(RegClass::V128)]
        .as_ref()
        .unwrap();
    assert!(float_info.suggested_scratch.is_some());
    for i in float_info.first..float_info.last {
        let idx = i - float_info.first;
        let rreg = rru.regs[i].0;
        let preg = regalloc2::PReg::new(idx, regalloc2::RegClass::Float);
        rregs_by_preg_idx[preg.index()] = rreg;
        regs.push(preg);
        if i == float_info.suggested_scratch.unwrap() {
            scratch_by_class[1] = preg;
        } else if i < rru.allocable {
            if idx < opts.num_float_preferred {
                preferred_regs_by_class[1].push(preg);
            } else {
                non_preferred_regs_by_class[1].push(preg);
            }
        }
    }

    let env = regalloc2::MachineEnv {
        regs,
        preferred_regs_by_class,
        non_preferred_regs_by_class,
        scratch_by_class,
    };
    (env, rregs_by_preg_idx)
}

pub(crate) fn create_shim_and_env<'a, F: Function>(
    func: &'a F,
    rru: &'a RealRegUniverse,
    sri: Option<&StackmapRequestInfo>,
    opts: &Regalloc2Options,
) -> (Shim<'a, F>, regalloc2::MachineEnv) {
    let (env, rregs_by_preg_index) = build_machine_env(rru, opts);
    let vreg_offset = rregs_by_preg_index.len();
    let mut shim = Shim {
        func,
        rru,
        succs: vec![],
        succ_ranges: vec![],
        preds: vec![],
        pred_ranges: vec![],
        operands: vec![],
        operand_ranges: vec![],
        rregs_by_preg_index,
        vreg_offset,
        reftype_vregs: vec![],
        safepoints: regalloc2::bitvec::BitVec::new(),
    };

    // Compute preds and succs in a regalloc2-compatible format.
    let mut edges: Vec<(usize, usize)> = vec![];
    for block in func.blocks() {
        let start = shim.succs.len();
        for &succ in func.block_succs(block).iter() {
            shim.succs.push(regalloc2::Block::new(succ.get() as usize));
            edges.push((block.get() as usize, succ.get() as usize));
        }
        let end = shim.succs.len();
        shim.succ_ranges.push((start as u32, end as u32));
    }
    edges.sort_unstable_by_key(|(_from, to)| *to);
    let mut i = 0;
    for block in func.blocks() {
        while i < edges.len() && edges[i].1 < block.get() as usize {
            i += 1;
        }
        let first_edge = i;
        while i < edges.len() && edges[i].1 == block.get() as usize {
            i += 1;
        }
        let edges = &edges[first_edge..i];

        let start = shim.preds.len();
        for &(from, _) in edges {
            shim.preds.push(regalloc2::Block::new(from));
        }
        let end = shim.preds.len();
        shim.pred_ranges.push((start as u32, end as u32));
    }

    // Create Operands for each reg use/def/mod in the function.  (Add
    // additional Operands for RealReg vregs based on liveins at
    // entry, and liveouts at return points.)
    let mut reg_vecs = RegVecs::new(false);
    for insn in func.insns() {
        reg_vecs.clear();
        let mut coll = RegUsageCollector::new(&mut reg_vecs);
        F::get_regs(insn, &mut coll);
        let start = shim.operands.len();
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
            let vreg = shim.translate_reg_to_vreg(d.to_reg());
            let policy = shim.translate_reg_to_policy(d.to_reg());
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                policy,
                regalloc2::OperandKind::Def,
                regalloc2::OperandPos::After,
            ));
        }
        for &m in &reg_vecs.mods {
            let idx = shim.operands.len() - start;
            let vreg = shim.translate_reg_to_vreg(m.to_reg());
            let use_policy = shim.translate_reg_to_policy(m.to_reg());
            let def_policy = regalloc2::OperandPolicy::Reuse(idx);
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                use_policy,
                regalloc2::OperandKind::Use,
                regalloc2::OperandPos::Before,
            ));
            shim.operands.push(regalloc2::Operand::new(
                vreg,
                def_policy,
                regalloc2::OperandKind::Def,
                regalloc2::OperandPos::After,
            ));
        }
    }

    // Compute safepoint map.
    // TODO

    (shim, env)
}

pub(crate) fn update_func<'a, F: Function>(
    shim: Shim<'a, F>,
    out: regalloc2::Output,
) -> RegAllocResult<F> {
    todo!()
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
        let rc = reg.get_class();
        let trc = translate_rc(rc);
        let info = &self.rru.allocable_by_class[rc as usize].as_ref().unwrap();
        let idx = reg.get_index() - info.first;
        regalloc2::PReg::new(idx, trc)
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
        let rc = reg.get_class();
        let trc = translate_rc(rc);
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

    fn translate_reg_to_policy(&self, reg: Reg) -> regalloc2::OperandPolicy {
        if reg.is_real() {
            regalloc2::OperandPolicy::FixedReg(self.translate_realreg_to_preg(reg.to_real_reg()))
        } else {
            regalloc2::OperandPolicy::Reg
        }
    }
}

impl<'a, F: Function> regalloc2::Function for Shim<'a, F> {
    fn insts(&self) -> usize {
        self.func.insns().len()
    }

    fn blocks(&self) -> usize {
        self.func.blocks().len()
    }

    fn entry_block(&self) -> regalloc2::Block {
        regalloc2::Block::new(self.func.entry_block().get() as usize)
    }

    fn block_insns(&self, block: regalloc2::Block) -> regalloc2::InstRange {
        let range = self.func.block_insns(BlockIx::new(block.index() as u32));
        let start = regalloc2::Inst::new(range.first().get() as usize);
        let end = regalloc2::Inst::new(range.first().get() as usize + range.len());
        regalloc2::InstRange::forward(start, end)
    }

    fn block_succs(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        let (start, end) = self.succ_ranges[block.index()];
        &self.succs[start as usize..end as usize]
    }

    fn block_preds(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        let (start, end) = self.succ_ranges[block.index()];
        &self.succs[start as usize..end as usize]
    }

    fn block_params(&self, block: regalloc2::Block) -> &[regalloc2::VReg] {
        // We don't use blockparams.
        &[]
    }

    fn is_call(&self, insn: regalloc2::Inst) -> bool {
        // We don't have this info in regalloc1 interface, but it is
        // just for heuristics, not strictly needed.
        false
    }

    fn is_ret(&self, insn: regalloc2::Inst) -> bool {
        self.func.is_ret(InstIx::new(insn.index() as u32))
    }

    fn is_branch(&self, insn: regalloc2::Inst) -> bool {
        // Only needed if we use blockparams.
        false
    }

    fn branch_blockparam_arg_offset(
        &self,
        block: regalloc2::Block,
        insn: regalloc2::Inst,
    ) -> usize {
        // We don't use blockparams.
        0
    }

    fn is_safepoint(&self, insn: regalloc2::Inst) -> bool {
        self.safepoints.get(insn.index())
    }

    fn is_move(&self, insn: regalloc2::Inst) -> Option<(regalloc2::VReg, regalloc2::VReg)> {
        let inst = &self.func.insns()[insn.index()];
        self.func.is_move(inst).map(|(dst, src)| {
            (
                self.translate_reg_to_vreg(src),
                self.translate_reg_to_vreg(dst.to_reg()),
            )
        })
    }

    // --------------------------
    // Instruction register slots
    // --------------------------

    fn inst_operands(&self, insn: regalloc2::Inst) -> &[regalloc2::Operand] {
        let (start, end) = self.operand_ranges[insn.index()];
        &self.operands[start as usize..end as usize]
    }

    fn inst_clobbers(&self, insn: regalloc2::Inst) -> &[regalloc2::PReg] {
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

    fn spillslot_size(&self, regclass: regalloc2::RegClass, for_vreg: regalloc2::VReg) -> usize {
        let regclass = match regclass {
            regalloc2::RegClass::Int => RegClass::I64,
            regalloc2::RegClass::Float => RegClass::V128,
        };
        let for_vreg = self.translate_vreg_to_reg(for_vreg).to_virtual_reg();
        self.func.get_spillslot_size(regclass, for_vreg) as usize
    }

    fn multi_spillslot_named_by_last_slot(&self) -> bool {
        false
    }
}

#[derive(Clone, Debug)]
pub struct Regalloc2Options {
    num_int_preferred: usize,
    num_float_preferred: usize,
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
    let result = regalloc2::run(&ra2_func, &env)
        .map_err(|err| RegAllocError::Other(format!("{:?}", err)))?;
    Ok(update_func(ra2_func, result))
}
