use crate::{
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf},
};
use giputils::bitvec::BitVec;
use logicrs::{LitVec, Var, VarBitVec, satif::Satif};
use rand::{SeedableRng, rngs::StdRng};

struct Simulate<'t> {
    ts: &'t Transys,
    sim: VarBitVec,
    slv: DagCnfSolver,
    consider: Vec<Var>,
    num_word: usize,
    domain: Vec<Var>,
    _rng: StdRng,
}

impl Simulate<'_> {
    fn rt_dfs_simulate(&mut self, from: usize) {
        let assump = self.sim.assign(from, Some(self.consider.iter().copied()));
        loop {
            if self.sim.bv_len() >= self.num_word * BitVec::WORD_SIZE {
                return;
            }
            if !self
                .slv
                .solve_with_param(&assump, vec![], self.domain.iter().copied(), Some(5))
                .is_some_and(|r| r)
            {
                return;
            }
            self.sim[Var::CONST].push(false);
            let mut block = LitVec::new();
            for &v in self.consider.iter() {
                let n = self.ts.next(v.lit());
                let va = self.slv.sat_value(n).unwrap();
                let na = self.slv.sat_value_lit(n.var()).unwrap();
                self.sim[v].push(va);
                block.push(!na);
            }
            self.slv.add_clause(&block);
            self.rt_dfs_simulate(self.sim.bv_len() - 1);
        }
    }
}

impl Transys {
    pub fn init_simulation(&self, num_word: usize) -> VarBitVec {
        let mut slv = DagCnfSolver::new(&self.rel);
        for cls in self.constraint() {
            slv.add_clause(&cls.cube());
        }
        self.load_init(&mut slv);
        let mut sim = VarBitVec::new();
        sim.extend_to(self.max_var());
        while sim.bv_len() < num_word * BitVec::WORD_SIZE {
            if !slv.solve(&[]) {
                break;
            }
            let mut block = LitVec::new();
            for &v in self.latch.iter() {
                if let Some(a) = slv.sat_value(v.lit()) {
                    block.push(!slv.sat_value_lit(v).unwrap());
                    sim[v].push(a);
                } else {
                    sim[v].clear();
                }
            }
            if block.is_empty() {
                break;
            }
            sim[Var::CONST].push(false);
            slv.add_clause(&block);
        }
        sim
    }

    // pub fn rt_simulation(&self, init: &VarBitVec, num_word: usize) -> VarBitVec {
    //     assert!(init.bv_len() > 0);
    //     let mut sim = VarBitVec::new();
    //     sim.extend_to(self.max_var());
    //     let mut slv = DagCnfSolver::new(&self.rel);
    //     for cls in self.constraint() {
    //         slv.add_clause(&cls.cube());
    //     }
    //     for i in 0..init.bv_len() {
    //         let block = !init.assign(i, Some(self.latch().filter(|v| !init[*v].is_empty())));
    //         let block = self.lits_next(block.iter());
    //         slv.add_clause(&block);
    //     }
    //     let domain: Vec<_> = self.next.values().map(|l| l.var()).collect();
    //     let mut rng = StdRng::seed_from_u64(0);
    //     let mut num_fail = 0;
    //     while sim.bv_len() < BitVec::WORD_SIZE {
    //         let from = rng.random_range(0..init.bv_len());
    //         let assump = init.assign(from, Some(self.latch().filter(|v| !init[*v].is_empty())));
    //         slv.clear_phase();
    //         if !slv.solve_with_domain(&assump, domain.iter().copied()) {
    //             num_fail += 1;
    //             if num_fail > 100 {
    //                 break;
    //             }
    //             continue;
    //         }
    //         sim[Var::CONST].push(false);
    //         let mut block = LitVec::new();
    //         for &v in self.latch.iter() {
    //             let n = self.next(v.lit());
    //             let va = slv.sat_value(n).unwrap();
    //             let na = slv.sat_value_lit(n.var()).unwrap();
    //             sim[v].push(va);
    //             block.push(!na);
    //         }
    //         slv.add_clause(&block);
    //     }
    //     num_fail = 0;
    //     while sim.bv_len() < num_word * BitVec::WORD_SIZE {
    //         let from = rng.random_range(0..sim.bv_len());
    //         let assump = sim.assign(from, Some(self.latch()));
    //         slv.clear_phase();
    //         if !slv.solve_with_domain(&assump, domain.iter().copied()) {
    //             num_fail += 1;
    //             if num_fail > 100 {
    //                 break;
    //             }
    //             continue;
    //         }
    //         sim[Var::CONST].push(false);
    //         let mut block = LitVec::new();
    //         for &v in self.latch.iter() {
    //             let n = self.next(v.lit());
    //             let va = slv.sat_value(n).unwrap();
    //             let na = slv.sat_value_lit(n.var()).unwrap();
    //             sim[v].push(va);
    //             block.push(!na);
    //         }
    //         slv.add_clause(&block);
    //     }
    //     sim
    // }

    pub fn rt_simulation(&self, init: &VarBitVec, num_word: usize) -> VarBitVec {
        assert!(init.bv_len() > 0);
        let mut sim = VarBitVec::new();
        let consider: Vec<_> = self.latch().filter(|v| !init[*v].is_empty()).collect();
        sim.extend_to(self.max_var());
        let mut slv = DagCnfSolver::new(&self.rel);
        for cls in self.constraint() {
            slv.add_clause(&cls.cube());
        }
        for i in 0..init.bv_len() {
            let block = !init.assign(i, Some(consider.iter().copied()));
            let block = self.lits_next(block.iter());
            slv.add_clause(&block);
        }
        slv.cfg.phase_saving = false;
        // Only read successors of the observed registers. The solver expands
        // these roots to their dependency closure; add_clause also keeps the
        // cones of permanent constraints and blocking clauses in its domain.
        let mut domain: Vec<_> = consider
            .iter()
            .flat_map(|&v| [v, self.next(v.lit()).var()])
            .chain(self.constraint().map(|l| l.var()))
            .collect();
        domain.sort_unstable();
        domain.dedup();
        let mut simulate = Simulate {
            ts: self,
            sim,
            slv,
            num_word,
            domain,
            consider,
            _rng: StdRng::seed_from_u64(0),
        };

        for from in 0..init.bv_len() {
            let assump = init.assign(from, Some(self.latch().filter(|v| !init[*v].is_empty())));
            loop {
                if simulate.sim.bv_len() >= num_word * BitVec::WORD_SIZE {
                    return simulate.sim;
                }
                if !simulate
                    .slv
                    .solve_with_domain(&assump, simulate.domain.iter().copied())
                {
                    break;
                }
                simulate.sim[Var::CONST].push(false);
                let mut block = LitVec::new();
                for &v in simulate.consider.iter() {
                    let n = simulate.ts.next(v.lit());
                    let va = simulate.slv.sat_value(n).unwrap();
                    let na = simulate.slv.sat_value_lit(n.var()).unwrap();
                    simulate.sim[v].push(va);
                    block.push(!na);
                }
                simulate.slv.add_clause(&block);
                simulate.rt_dfs_simulate(simulate.sim.bv_len() - 1);
            }
        }
        simulate.sim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use logicrs::Lit;
    use std::collections::{BTreeSet, VecDeque};

    fn check_projected_successors(ts: &Transys, initial: &[(Var, bool)]) {
        let mut init = VarBitVec::new();
        init.reserve(ts.max_var());
        init[Var::CONST].push(false);
        for &(v, value) in initial {
            init[v].push(value);
        }
        // Enumerate the small projected transition graph with an independent
        // full-CNF solver, including constraints outside the observed cones.
        let mut reference = cadical::CaDiCaL::new();
        ts.load_trans(&mut reference, true);
        let first: Vec<_> = initial.iter().map(|&(_, value)| value).collect();
        let mut reached = BTreeSet::from([first.clone()]);
        let mut queue = VecDeque::from([first.clone()]);
        while let Some(source) = queue.pop_front() {
            for bits in 0..1usize << initial.len() {
                let target: Vec<_> = (0..initial.len()).map(|i| bits & (1 << i) != 0).collect();
                if reached.contains(&target) {
                    continue;
                }
                let mut assignment = LitVec::new();
                for (i, &(v, _)) in initial.iter().enumerate() {
                    assignment.push(Lit::new(v, source[i]));
                    assignment.push(ts.next(v.lit()).not_if(!target[i]));
                }
                if reference.solve(&assignment) {
                    reached.insert(target.clone());
                    queue.push_back(target);
                }
            }
        }
        reached.remove(&first);
        let sim = ts.rt_simulation(&init, 1);
        let actual: BTreeSet<Vec<_>> = (0..sim.bv_len())
            .map(|i| initial.iter().map(|&(v, _)| sim[v].get(i)).collect())
            .collect();
        assert_eq!(
            actual.len(),
            sim.bv_len(),
            "blocking must prevent duplicate samples"
        );
        assert_eq!(actual, reached);
        for v in ts.latch() {
            if !initial.iter().any(|&(observed, _)| observed == v) {
                assert!(sim[v].is_empty());
            }
        }
    }

    #[test]
    fn retains_constraints_outside_the_observed_next_cones() {
        let mut ts = Transys::default();
        let a = ts.new_var();
        let b = ts.new_var();
        let x = ts.new_var();
        let y = ts.new_var();
        let hidden = ts.new_var();
        ts.input = vec![a, b];
        ts.add_latch(x, Some(Lit::FALSE), a.lit());
        ts.add_latch(y, Some(Lit::FALSE), b.lit());
        ts.add_latch(hidden, None, !hidden.lit());
        let left = ts.rel.new_or([!a.lit(), hidden.lit()]);
        let right = ts.rel.new_or([!hidden.lit(), !b.lit()]);
        ts.constraint.extend([left, right]);
        // The unobserved hidden register connects the constraints, ruling out
        // next(x) = next(y) = true even though their own cones are disjoint.
        check_projected_successors(&ts, &[(x, false), (y, false)]);
    }

    #[test]
    fn retains_current_state_dependencies_across_recursive_samples() {
        let mut ts = Transys::default();
        let input = ts.new_var();
        let x = ts.new_var();
        let y = ts.new_var();
        ts.input.push(input);
        let yn = ts.rel.new_xor(x.lit(), input.lit());
        ts.add_latch(x, Some(Lit::FALSE), !x.lit());
        ts.add_latch(y, Some(Lit::FALSE), yn);
        for _ in 0..16 {
            let hidden = ts.new_var();
            let next = ts.rel.new_xor(hidden.lit(), input.lit());
            ts.add_latch(hidden, None, next);
        }
        check_projected_successors(&ts, &[(x, false), (y, false)]);
    }

    #[test]
    fn blocks_shared_inverted_and_constant_successors() {
        let mut ts = Transys::default();
        let input = ts.new_var();
        let x = ts.new_var();
        let y = ts.new_var();
        let z = ts.new_var();
        ts.input.push(input);
        ts.add_latch(x, Some(Lit::FALSE), input.lit());
        ts.add_latch(y, Some(Lit::FALSE), !input.lit());
        ts.add_latch(z, Some(Lit::TRUE), Lit::TRUE);
        check_projected_successors(&ts, &[(x, false), (y, false), (z, true)]);
    }

    #[test]
    fn empty_observation_set_produces_no_new_projected_state() {
        let mut ts = Transys::default();
        let hidden = ts.new_var();
        ts.add_latch(hidden, None, !hidden.lit());
        check_projected_successors(&ts, &[]);
    }
}
