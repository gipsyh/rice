use logicrs::{Lit, satif::Satif};
use rIC3::{
    config::PreprocConfig,
    frontend::frontend_from_model,
    transys::{Transys, TransysIf, certify::Restore},
};
use std::{path::PathBuf, time::Instant};

fn verify_merges(original: &Transys, restore: &Restore) -> anyhow::Result<()> {
    let mut init = cadical::CaDiCaL::new();
    original.load_trans(&mut init, true);
    original.load_init(&mut init);
    let mut step = cadical::CaDiCaL::new();
    original.load_trans(&mut step, true);
    let equalities = restore.eq_invariant();
    for pair in equalities.chunks_exact(2) {
        let (x, y) = (pair[0][0], !pair[0][1]);
        anyhow::ensure!(
            !init.solve(&[x, !y]) && !init.solve(&[!x, y]),
            "initial condition does not imply {x} = {y}"
        );
        let next = |lit: Lit| {
            if lit.var().is_constant() {
                lit
            } else {
                original.next(lit)
            }
        };
        let (xn, yn) = (next(x), next(y));
        for value in [false, true] {
            let (a, b) = (x.not_if(!value), y.not_if(!value));
            anyhow::ensure!(
                !step.solve(&[a, b, xn, !yn]) && !step.solve(&[a, b, !xn, yn]),
                "induction does not preserve {x} = {y}"
            );
        }
    }
    println!(
        "profile: independently verified {} register merges against the original model",
        equalities.len() / 2
    );
    Ok(())
}

fn main() -> anyhow::Result<()> {
    env_logger::Builder::from_default_env().init();
    let mut args = std::env::args().skip(1);
    let path = PathBuf::from(args.next().expect("model path"));
    let flags: Vec<_> = args.collect();
    let verify = flags.iter().any(|a| a == "--verify");
    let mut frontend = frontend_from_model(&path)?;
    let (mut ts, _) = frontend.ts();
    ts.compress_bads();
    let original = verify.then(|| ts.clone());
    let rst = Restore::new(&ts);
    let cfg = PreprocConfig {
        frts: flags.iter().any(|a| a == "--frts"),
        ..PreprocConfig::default()
    };
    let start = Instant::now();
    let (ts, rst) = ts.preproc(&cfg, rst);
    println!(
        "profile: preprocessing {:.3}s: {}",
        start.elapsed().as_secs_f64(),
        ts.statistic()
    );
    if let Some(original) = original {
        verify_merges(&original, &rst)?;
    }
    Ok(())
}
