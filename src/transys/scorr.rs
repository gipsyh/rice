use crate::{
    config::PreprocConfig,
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf, certify::Restore},
};
use giputils::{bitvec::BitVec, hash::GHashMap};
use log::{debug, info};
use logicrs::{Lit, LitVec, Var, VarLMap, satif::Satif};
use std::time::Instant;

pub struct Scorr {
    ts: Box<Transys>,
    rst: Restore,
    ind_slv: DagCnfSolver,
    cfg: PreprocConfig,
    start: Instant,
}

impl Scorr {
    pub fn new(ts: Transys, cfg: &PreprocConfig, rst: Restore) -> Self {
        let start = Instant::now();
        let ts = Box::new(ts);
        let mut ind_slv = DagCnfSolver::new(&ts.rel);
        for c in ts.constraint.iter() {
            ind_slv.add_clause(&[*c]);
        }
        Self {
            ts,
            rst,
            ind_slv,
            cfg: cfg.clone(),
            start,
        }
    }

    fn check_scorr(&mut self, x: Lit, y: Lit) -> bool {
        let xn = self.ts.next(x);
        let yn = if y.var().is_constant() {
            y
        } else {
            self.ts.next(y)
        };
        self.ind_slv
            .solve_with_restart_limit(
                &[],
                vec![
                    LitVec::from([x, !y]),
                    LitVec::from([!x, y]),
                    LitVec::from([xn, yn]),
                    LitVec::from([!xn, !yn]),
                ],
                10,
            )
            .is_some_and(|r| !r)
    }

    pub fn scorr(mut self) -> (Transys, Restore) {
        let start = Instant::now();
        let latch: Vec<_> = self
            .ts
            .latch()
            .filter(|&v| {
                self.ts
                    .init(v)
                    .and_then(|init| init.try_constant())
                    .is_some()
            })
            .collect();
        info!(
            "scorr profile: setup {:.3}s, init {:.3}s, {} initialized latches",
            self.start.elapsed().as_secs_f64() - start.elapsed().as_secs_f64(),
            start.elapsed().as_secs_f64(),
            latch.len()
        );
        if latch.is_empty() {
            return (*self.ts, self.rst);
        }
        info!("scorr: sampling with random inputs");
        let rt = self.ts.random_rt_simulation(64);
        info!(
            "scorr profile: simulations {:.3}s, {} samples",
            start.elapsed().as_secs_f64(),
            rt.bv_len()
        );
        debug!("scorr: rt simulation size: {}", rt.bv_len());
        let mut cand: GHashMap<BitVec, LitVec> = GHashMap::new();
        cand.insert(rt[Var::CONST].clone(), LitVec::from([Lit::FALSE]));
        for &v in latch.iter() {
            let l = v.lit();
            if let Some(c) = cand.get_mut(&rt[v]) {
                c.push(l);
            } else if let Some(c) = cand.get_mut(&rt.val(!l)) {
                c.push(!l);
            } else {
                cand.insert(rt[v].clone(), LitVec::from([l]));
            }
        }
        cand.retain(|_, eqc| eqc.len() > 1);
        let mut scorr = VarLMap::new();
        info!(
            "scorr profile: candidates {:.3}s, {} classes, max class {}",
            start.elapsed().as_secs_f64(),
            cand.len(),
            cand.values().map(|c| c.len()).max().unwrap_or(0)
        );
        let checking_start = Instant::now();
        let mut classes: Vec<_> = cand.into_iter().map(|(_, eqc)| eqc).collect();
        for eqc in &mut classes {
            eqc.sort_unstable_by_key(|l| l.var());
        }
        classes.sort_unstable_by_key(|eqc| eqc[0].var());
        'm: for mut eqc in classes {
            let mut representatives = 0;
            let mut class_size = eqc.len();
            'members: for index in 0..eqc.len() {
                let x = eqc[index];
                for (i, &y) in eqc[..representatives].iter().enumerate() {
                    if i > (10000 / class_size).max(1) {
                        break;
                    }
                    if start.elapsed().as_secs() > self.cfg.scorr_tl {
                        info!("scorr: timeout");
                        break 'm;
                    }
                    if self.check_scorr(x, y) {
                        debug!("scorr: {x} -> {y}");
                        scorr.insert_lit(x, y);
                        class_size -= 1;
                        continue 'members;
                    }
                }
                eqc[representatives] = x;
                representatives += 1;
            }
        }
        info!(
            "scorr profile: checking {:.3}s, {} induction solves",
            checking_start.elapsed().as_secs_f64(),
            self.ind_slv.statistic().num_solve
        );
        info!(
            "scorr: eliminates {} latchs out of {} in {:.2}s",
            scorr.len(),
            self.ts.latch.len(),
            start.elapsed().as_secs_f32()
        );
        // for (x, r) in scorr.clone().iter() {
        //     let mut xn = self.ts.next(x.lit());
        //     let mut rn = if r.var().is_constant() {
        //         *r
        //     } else {
        //         self.ts.next(*r)
        //     };
        //     if xn.var() == rn.var() {
        //         continue;
        //     }
        //     if xn.var() < rn.var() {
        //         (xn, rn) = (rn, xn);
        //     }
        //     trace!("scorr: {xn} -> {rn}");
        //     scorr.insert_lit(xn, rn);
        // }
        // let mut vars: Vec<Var> = scorr.keys().copied().collect();
        // vars.sort();
        // for v in vars {
        //     let r = scorr[&v];
        //     if let Some(rr) = scorr.map_lit(r) {
        //         if rr.var() != r.var() {
        //             scorr.insert_lit(v.lit(), rr);
        //         }
        //     }
        // }
        let ind_solves = self.ind_slv.statistic().num_solve;
        drop(self.ind_slv);
        self.ts.replace(&scorr, &mut self.rst);
        self.ts.simplify(&mut self.rst);
        info!("scorr: simplified ts: {}", self.ts.statistic());
        info!(
            "scorr profile: total {:.3}s, induction solves {}",
            self.start.elapsed().as_secs_f64(),
            ind_solves
        );
        (*self.ts, self.rst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_scan_preserves_surviving_representatives_and_polarity() {
        let mut ts = Transys::new();
        let source = ts.new_var();
        let x = ts.new_var();
        let y = ts.new_var();
        let inverted = ts.new_var();
        ts.add_latch(source, Some(Lit::FALSE), source.lit());
        ts.add_latch(x, Some(Lit::FALSE), source.lit());
        ts.add_latch(y, Some(Lit::FALSE), source.lit());
        ts.add_latch(inverted, Some(Lit::TRUE), !source.lit());
        ts.latch.reverse();
        ts.bad = LitVec::from([x.lit(), y.lit(), inverted.lit()]);

        let restore = Restore::new(&ts);
        let (_, restore) = Scorr::new(ts, &PreprocConfig::default(), restore).scorr();
        let equalities = restore.eq_invariant();
        assert_eq!(equalities.len(), 6);
        for clause in [
            [Lit::FALSE, !source.lit()],
            [Lit::TRUE, source.lit()],
            [x.lit(), !y.lit()],
            [!x.lit(), y.lit()],
            [x.lit(), inverted.lit()],
            [!x.lit(), !inverted.lit()],
        ] {
            assert!(equalities.iter().any(|actual| actual.as_slice() == clause));
        }
    }
}
