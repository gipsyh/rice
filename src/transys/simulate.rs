use crate::transys::{Transys, TransysIf};
use logicrs::{Lit, Var, VarBitVec, VarMap};
use rand::{RngExt, SeedableRng, rngs::StdRng};

struct RandomSimulate<'t> {
    ts: &'t Transys,
    latch: Vec<Var>,
    next: Vec<Lit>,
    input: Vec<Var>,
    order: Vec<Var>,
    value: VarMap<u64>,
    rng: StdRng,
}

impl<'t> RandomSimulate<'t> {
    fn new(ts: &'t Transys) -> Self {
        let latch: Vec<_> = ts.latch().collect();
        let mut seen = VarMap::new_with(ts.max_var());
        seen[Var::CONST] = true;
        for &v in &latch {
            seen[v] = true;
        }
        let mut input = Vec::new();
        for v in ts.input() {
            if !seen[v] {
                seen[v] = true;
                input.push(v);
            }
        }
        let next: Vec<_> = latch.iter().map(|&v| ts.next(v.lit())).collect();
        // Build only the combinational cones of the observed next functions.
        // All inputs and registers terminate traversal as state or random leaves.
        let mut order = Vec::new();
        let mut stack = Vec::new();
        for lit in &next {
            stack.push((lit.var(), false));
            while let Some((v, expanded)) = stack.pop() {
                if seen[v] {
                    continue;
                }
                if expanded {
                    seen[v] = true;
                    order.push(v);
                } else if ts.rel.is_leaf(v) {
                    seen[v] = true;
                    input.push(v);
                } else {
                    stack.push((v, true));
                    stack.extend(ts.rel.dep(v).iter().rev().map(|&dep| (dep, false)));
                }
            }
        }
        let mut rng = StdRng::seed_from_u64(0);
        let mut value = VarMap::new_with(ts.max_var());
        for &v in &latch {
            value[v] = match ts.init(v).and_then(|init| init.try_constant()) {
                Some(true) => u64::MAX,
                Some(false) => 0,
                None => rng.random::<u64>(),
            };
        }
        Self {
            ts,
            latch,
            next,
            input,
            order,
            value,
            rng,
        }
    }

    fn lit_value(&self, lit: Lit) -> u64 {
        if lit.polarity() {
            self.value[lit.var()]
        } else {
            !self.value[lit.var()]
        }
    }

    fn step(&mut self, next: &mut [u64]) {
        // Refresh primary inputs and other free leaves for every step.
        for &v in &self.input {
            self.value[v] = self.rng.random::<u64>();
        }
        for &v in &self.order {
            let mut result = 0;
            for clause in &self.ts.rel[v] {
                let (output, inputs) = clause.split_last().unwrap();
                debug_assert_eq!(output.var(), v);
                let inputs = inputs.iter().fold(0, |word, &l| word | self.lit_value(l));
                if output.polarity() {
                    result |= !inputs;
                } else {
                    result &= inputs;
                }
            }
            self.value[v] = result;
        }
        // Read every next value before writing any current-state value,
        // including next functions that are aliases of other registers.
        for (slot, &lit) in next.iter_mut().zip(&self.next) {
            *slot = self.lit_value(lit);
        }
        for (&v, &next) in self.latch.iter().zip(next.iter()) {
            self.value[v] = next;
        }
    }
}

impl Transys {
    /// Store num_word words for registers with constant initial values.
    /// The first word contains 64 states satisfying the constant initial values.
    /// Other registers start with independent random values in each lane.
    /// Later words advance these 64 complete states with fresh random inputs,
    /// using a DFS evaluation order built once for the required next-state cones.
    /// Constraints are ignored during sampling.
    pub fn random_rt_simulation(&self, num_word: usize) -> VarBitVec {
        let mut sim = VarBitVec::new();
        sim.extend_to(self.max_leaf_var());
        if num_word == 0 {
            return sim;
        }
        let consider: Vec<_> = self
            .latch()
            .filter(|&v| self.init(v).and_then(|init| init.try_constant()).is_some())
            .collect();
        let mut run = RandomSimulate::new(self);
        let mut next = vec![0; run.latch.len()];
        for word in 0..num_word {
            if word > 0 {
                run.step(&mut next);
            }
            for v in std::iter::once(Var::CONST).chain(consider.iter().copied()) {
                sim[v].push_word(run.value[v]);
            }
        }
        sim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use giputils::bitvec::BitVec;
    use logicrs::{Lit, LitVec, satif::Satif};

    #[test]
    fn random_dfs_traces_satisfy_the_full_transition_relation() {
        let mut ts = Transys::default();
        let input = ts.new_var();
        let a = ts.new_var();
        let b = ts.new_var();
        let c = ts.new_var();
        let d = ts.new_var();
        ts.input.push(input);
        let shared = ts.rel.new_xor(a.lit(), input.lit());
        let cn = ts.rel.new_and([shared, !b.lit()]);
        let dn = ts.rel.new_or([!shared, b.lit()]);
        ts.add_latch(a, Some(Lit::FALSE), b.lit());
        ts.add_latch(b, Some(Lit::TRUE), a.lit());
        ts.add_latch(c, Some(Lit::FALSE), cn);
        ts.add_latch(d, Some(Lit::TRUE), dn);
        let initial = [(a, false), (b, true), (c, false), (d, true)];
        let mut reference = cadical::CaDiCaL::new();
        ts.load_trans(&mut reference, false);
        for num_word in [0, 1, 3, 10, 65] {
            let samples = ts.random_rt_simulation(num_word);
            assert_eq!(samples.bv_len(), num_word * BitVec::WORD_SIZE);
            if num_word == 0 {
                continue;
            }
            assert!(samples[Var::CONST].is_zero());
            for &(v, value) in &initial {
                for lane in 0..BitVec::WORD_SIZE {
                    assert_eq!(samples[v].get(lane), value);
                }
            }
            for index in BitVec::WORD_SIZE..samples.bv_len() {
                let from = index - BitVec::WORD_SIZE;
                let next: Vec<_> = initial
                    .iter()
                    .map(|&(v, _)| samples[v].get(index))
                    .collect();
                let mut assignment = LitVec::new();
                for (i, &(v, _)) in initial.iter().enumerate() {
                    assignment.push(Lit::new(v, samples[v].get(from)));
                    assignment.push(ts.next(v.lit()).not_if(!next[i]));
                }
                assert!(reference.solve(&assignment), "from={from}, index={index}");
                assert_ne!(next[0], next[1], "register updates must be simultaneous");
                assert_ne!(
                    next[2], next[3],
                    "shared inputs must have one value per cycle"
                );
            }
        }
    }

    #[test]
    fn random_dfs_preserves_independently_initialized_hidden_state() {
        let mut ts = Transys::default();
        let observed = ts.new_var();
        let hidden = ts.new_var();
        let unrelated = ts.new_var();
        let inverted = ts.new_var();
        ts.add_latch(observed, Some(Lit::FALSE), hidden.lit());
        ts.add_latch(hidden, None, hidden.lit());
        ts.add_latch(unrelated, None, unrelated.lit());
        ts.add_latch(inverted, Some(Lit::TRUE), !hidden.lit());
        let samples = ts.random_rt_simulation(7);
        let repeated = ts.random_rt_simulation(7);
        assert_eq!(samples[observed], repeated[observed]);
        assert!(samples[hidden].is_empty());
        assert!(samples[unrelated].is_empty());
        let first_successors = samples[observed].slice(BitVec::WORD_SIZE..2 * BitVec::WORD_SIZE);
        assert!(!first_successors.is_zero());
        assert!(!first_successors.is_ones());
        for index in 0..samples.bv_len() {
            assert_ne!(samples[observed].get(index), samples[inverted].get(index));
        }
        for index in 2 * BitVec::WORD_SIZE..samples.bv_len() {
            assert_eq!(
                samples[observed].get(index),
                samples[observed].get(index - BitVec::WORD_SIZE)
            );
        }
        ts.next.insert(hidden, Lit::FALSE);
        let changed_next = ts.random_rt_simulation(7);
        assert!(
            changed_next[observed]
                .slice(2 * BitVec::WORD_SIZE..changed_next.bv_len())
                .is_zero()
        );
        assert_ne!(samples[observed], changed_next[observed]);
    }

    #[test]
    fn random_dfs_preserves_constant_and_inverted_outputs() {
        let mut ts = Transys::default();
        let input = ts.new_var();
        let zero = ts.new_var();
        let one = ts.new_var();
        let inverted = ts.new_var();
        ts.input.push(input);
        let contradiction = ts.rel.new_and([input.lit(), !input.lit()]);
        ts.add_latch(zero, Some(Lit::FALSE), contradiction);
        ts.add_latch(one, Some(Lit::TRUE), !contradiction);
        ts.add_latch(inverted, Some(Lit::FALSE), !one.lit());
        let samples = ts.random_rt_simulation(5);
        assert!(samples[zero].is_zero());
        assert!(samples[one].is_ones());
        assert!(samples[inverted].is_zero());
    }

    #[test]
    fn random_dfs_ignores_constraints_during_sampling() {
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
        let unconstrained = ts.random_rt_simulation(3);
        for constraints in [
            LitVec::from([a.lit()]),
            LitVec::from([left, right]),
            LitVec::from([Lit::FALSE]),
        ] {
            ts.constraint = constraints;
            let samples = ts.random_rt_simulation(3);
            assert_eq!(samples.bv_len(), 3 * BitVec::WORD_SIZE);
            for v in [Var::CONST, x, y] {
                assert_eq!(samples[v], unconstrained[v]);
            }
            assert!(samples[hidden].is_empty());
        }
    }

    #[test]
    fn random_dfs_supports_an_empty_observation_set() {
        let mut ts = Transys::default();
        let hidden = ts.new_var();
        ts.add_latch(hidden, None, !hidden.lit());
        ts.constraint.push(Lit::FALSE);
        for num_word in [0, 1, 3] {
            let samples = ts.random_rt_simulation(num_word);
            assert_eq!(samples.bv_len(), num_word * BitVec::WORD_SIZE);
            if num_word > 0 {
                assert!(samples[Var::CONST].is_zero());
            }
            assert!(samples[hidden].is_empty());
        }
    }
}
