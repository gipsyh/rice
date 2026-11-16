use crate::{
    config::PreprocConfig,
    gipsat::DagCnfSolver,
    transys::{Transys, TransysIf, certify::Restore},
};
use giputils::hash::GHashMap;
use log::{debug, info, trace};
use logicrs::{Lit, LitVec, Var, VarLMap, VarMap, satif::Satif};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use std::time::Instant;

pub struct FrTs {
    cfg: PreprocConfig,
    // DagCnfSolver borrows rel through a raw pointer. Keep its address stable
    // when FrTs is moved into fr().
    ts: Box<Transys>,
    candidate: VarMap<Vec<Lit>>,
    class: VarMap<Var>,
    phase: VarMap<bool>,
    solver: DagCnfSolver,
    model: VarMap<bool>,
    model_round: VarMap<usize>,
    round: usize,
    rng: StdRng,
    rst: Restore,
    start: Instant,
}

impl FrTs {
    pub fn new(ts: Transys, cfg: &PreprocConfig, mut rst: Restore) -> Self {
        let start = Instant::now();
        let mut ts = Box::new(ts);
        ts.topsort(&mut rst);
        // Simulation only proposes candidates; SAT proves every replacement.
        // Refine collisions with counterexamples instead of storing 64,000
        // random bits for every variable up front.
        let sim = ts.rel.simulation(64);
        let mut signatures = GHashMap::new();
        let mut candidate: VarMap<Vec<Lit>> = VarMap::new_with(ts.max_var());
        let mut class = VarMap::new_with(ts.max_var());
        let mut phase = VarMap::new_with(ts.max_var());
        for v in ts.rel.var_iter() {
            let lv = v.lit();
            let signature = sim.val(lv);
            let (root, lit) = if let Some(&root) = signatures.get(&signature) {
                (root, lv)
            } else if let Some(&root) = signatures.get(&sim.val(!lv)) {
                (root, !lv)
            } else {
                signatures.insert(signature, v);
                (v, lv)
            };
            candidate[root].push(lit);
            class[v] = root;
            phase[v] = lit.polarity();
        }
        drop(signatures);
        drop(sim);
        let model = VarMap::new_with(ts.max_var());
        let model_round = VarMap::new_with(ts.max_var());
        let solver = DagCnfSolver::new(&ts.rel);
        info!(
            "frts: initialized in {:.3}s, {} candidates",
            start.elapsed().as_secs_f64(),
            candidate
                .iter()
                .map(|c| c.len().saturating_sub(1))
                .sum::<usize>()
        );
        Self {
            ts,
            cfg: cfg.clone(),
            candidate,
            class,
            phase,
            solver,
            model,
            model_round,
            round: 0,
            rst,
            rng: StdRng::seed_from_u64(0),
            start,
        }
    }

    // Complete the SAT solver's local, partial assignment by evaluating only
    // the cones needed by this candidate class. Use the same leaf assignment
    // for all members, including those outside the solver's current domain.
    fn model_value(&mut self, lit: Lit) -> bool {
        if self.model_round[lit.var()] == self.round {
            return self.model[lit.var()] == lit.polarity();
        }
        let mut stack = vec![lit.var()];
        while let Some(&v) = stack.last() {
            if self.model_round[v] == self.round {
                stack.pop();
                continue;
            }
            if let Some(value) = self.solver.sat_value(v.lit()) {
                self.model[v] = value;
            } else if self.ts.rel.is_leaf(v) {
                self.model[v] = self.rng.random_bool(0.5);
            } else if let Some(&d) = self
                .ts
                .rel
                .dep(v)
                .iter()
                .find(|&&d| self.model_round[d] != self.round)
            {
                stack.push(d);
                continue;
            } else {
                let mut value = false;
                for clause in &self.ts.rel[v] {
                    let (output, inputs) = clause.split_last().unwrap();
                    debug_assert_eq!(output.var(), v);
                    if inputs.iter().all(|l| self.model[l.var()] != l.polarity()) {
                        value = output.polarity();
                        break;
                    }
                }
                self.model[v] = value;
            }
            self.model_round[v] = self.round;
            stack.pop();
        }
        self.model[lit.var()] == lit.polarity()
    }

    fn refine(&mut self, root: Var, replace: &VarLMap) {
        self.round += 1;
        self.model[Var::CONST] = false;
        self.model_round[Var::CONST] = self.round;
        let mut split = [Vec::new(), Vec::new()];
        for lit in std::mem::take(&mut self.candidate[root]) {
            if !replace.contains_key(&lit.var()) {
                split[self.model_value(lit) as usize].push(lit);
            }
        }
        for members in split {
            if let Some(first) = members.first() {
                let root = first.var();
                for lit in &members {
                    self.class[lit.var()] = root;
                }
                self.candidate[root] = members;
            }
        }
    }

    pub fn fr(mut self) -> (Transys, Restore) {
        let check_start = Instant::now();
        let before = self.ts.max_var();
        let mut replace = VarLMap::new();
        let mut results = [0usize; 3];
        let mut refine_time = std::time::Duration::ZERO;
        'vars: for v in self.ts.rel.var_iter_woc() {
            if self.ts.rel.is_leaf(v) {
                continue;
            }
            let lv = Lit::new(v, self.phase[v]);
            let mut index = 0;
            let mut attempts = 0;
            loop {
                if self.start.elapsed().as_secs_f64() >= self.cfg.frts_tl as f64 {
                    info!("frts: timeout");
                    break 'vars;
                }
                let root = self.class[v];
                let members = &self.candidate[root];
                let Some(&m) = members.get(index) else { break };
                index += 1;
                if m.var() >= v || attempts >= 8 {
                    break;
                }
                if replace.contains_key(&m.var()) {
                    continue;
                }
                attempts += 1;
                trace!("frts: checking {lv} with {m}");
                let result = if let Some(value) = m.try_constant() {
                    // Constant candidates need just one assumption, with no
                    // temporary XOR clauses or activation literal to clean.
                    self.solver
                        .solve_with_restart_limit(&[lv.not_if(value)], vec![], 2)
                } else {
                    self.solver.solve_with_restart_limit(
                        &[],
                        vec![LitVec::from([m, lv]), LitVec::from([!m, !lv])],
                        2,
                    )
                };
                match result {
                    Some(true) => {
                        results[0] += 1;
                        let refine_start = Instant::now();
                        self.refine(root, &replace);
                        debug_assert_ne!(self.class[lv.var()], self.class[m.var()]);
                        refine_time += refine_start.elapsed();
                        index = 0;
                    }
                    Some(false) => {
                        results[1] += 1;
                        debug!("frts: {lv} -> {m}");
                        replace.insert_lit(lv, m);
                        // Keep the solver's clauses and dependency cones in
                        // sync: rewriting just its clauses would make local
                        // SAT models unsuitable for counterexample refinement.
                        break;
                    }
                    None => {
                        results[2] += 1;
                        debug!("frts: checking {lv} with {m} timeout");
                    }
                }
            }
        }
        let check_time = check_start.elapsed();
        // Release the solver before rewriting rel; apply all proved, direct
        // replacements once and keep learned clauses throughout SAT checking.
        drop(self.solver);
        let simplify_start = Instant::now();
        self.ts.replace(&replace, &mut self.rst);
        self.ts.simplify(&mut self.rst);
        info!(
            "frts: proved {} equivalences; SAT/UNSAT/UNKNOWN: {:?}",
            replace.len(),
            results
        );
        info!("frts: refinement {:.3}s", refine_time.as_secs_f64());
        info!(
            "frts: eliminates {} out of {} vars in {:.3}s (checks {:.3}s, simplify {:.3}s)",
            *before - *self.ts.max_var(),
            *before,
            self.start.elapsed().as_secs_f64(),
            check_time.as_secs_f64(),
            simplify_start.elapsed().as_secs_f64()
        );
        info!("frts: simplified ts: {}", self.ts.statistic());
        (*self.ts, self.rst)
    }
}
