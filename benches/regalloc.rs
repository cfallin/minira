//! Criterion-based benchmark target that computes insts/second for
//! arbitrary inputs.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use minira::{self, test_cases, test_framework as ir};
use regalloc;

fn create_func() -> ir::Func {
    test_cases::find_func("qsort").unwrap()
}

fn try_alloc(func: &ir::Func) -> bool {
    let num_regs = minira::fuzzing::NUM_REAL_REGS_PER_RC as usize;
    let reg_universe = ir::make_universe(num_regs, num_regs);
    let mut func = func.clone();
    let opts = regalloc::Options {
        run_checker: false,
        algorithm: regalloc::Algorithm::Backtracking(Default::default()),
    };
    let sri = func.get_stackmap_request();
    regalloc::allocate_registers_with_opts(&mut func, &reg_universe, sri.as_ref(), opts).is_ok()
}

fn run_regalloc(c: &mut Criterion) {
    let mut group = c.benchmark_group("benches");
    for iter in 0..10 {
        let func = create_func();
        eprintln!("==== {} instructions", func.insns.len());
        group.throughput(Throughput::Elements(func.insns.len() as u64));
        group.bench_with_input(BenchmarkId::from_parameter(iter), &iter, move |b, _| {
            b.iter(|| {
                try_alloc(&func);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, run_regalloc);
criterion_main!(benches);
