
import _target.deps.mathlib.algebra.big_operators
import _target.deps.mathlib.algebra.field
import _target.deps.mathlib.algebra.functions
import _target.deps.mathlib.algebra.group
import _target.deps.mathlib.algebra.group_power
import _target.deps.mathlib.algebra.module
import _target.deps.mathlib.algebra.order
import _target.deps.mathlib.algebra.ordered_group
import _target.deps.mathlib.algebra.ordered_monoid
import _target.deps.mathlib.algebra.ordered_ring
import _target.deps.mathlib.algebra.ring
import _target.deps.mathlib.category.basic
import _target.deps.mathlib.data.array.lemmas
import _target.deps.mathlib.data.bool
import _target.deps.mathlib.data.encodable
import _target.deps.mathlib.data.equiv
import _target.deps.mathlib.data.fin
import _target.deps.mathlib.data.finset.basic
import _target.deps.mathlib.data.finset.default
import _target.deps.mathlib.data.finset.fold
import _target.deps.mathlib.data.fp.basic
import _target.deps.mathlib.data.hash_map
import _target.deps.mathlib.data.int.basic
import _target.deps.mathlib.data.int.order
import _target.deps.mathlib.data.list.basic
import _target.deps.mathlib.data.list.comb
import _target.deps.mathlib.data.list.default
import _target.deps.mathlib.data.list.perm
import _target.deps.mathlib.data.list.set
import _target.deps.mathlib.data.list.sort
import _target.deps.mathlib.data.nat.basic
import _target.deps.mathlib.data.nat.dist
import _target.deps.mathlib.data.nat.gcd
import _target.deps.mathlib.data.nat.pairing
import _target.deps.mathlib.data.nat.prime
import _target.deps.mathlib.data.nat.sqrt
import _target.deps.mathlib.data.num.basic
import _target.deps.mathlib.data.num.bitwise
import _target.deps.mathlib.data.num.lemmas
import _target.deps.mathlib.data.option
import _target.deps.mathlib.data.pfun
import _target.deps.mathlib.data.pnat
import _target.deps.mathlib.data.prod
import _target.deps.mathlib.data.rat
-- there's some name clash here?
/-import _target.deps.mathlib.data.seq.computation
import _target.deps.mathlib.data.seq.parallel
import _target.deps.mathlib.data.seq.seq
import _target.deps.mathlib.data.seq.wseq-/

import _target.deps.mathlib.data.set.basic
import _target.deps.mathlib.data.set.countable
import _target.deps.mathlib.data.set.default
import _target.deps.mathlib.data.set.enumerate
import _target.deps.mathlib.data.set.finite
import _target.deps.mathlib.data.set.lattice
import _target.deps.mathlib.data.set.prod
import _target.deps.mathlib.data.sigma.basic
import _target.deps.mathlib.data.sigma.default
import _target.deps.mathlib.logic.basic
import _target.deps.mathlib.logic.function_inverse
import _target.deps.mathlib.order.basic
import _target.deps.mathlib.order.boolean_algebra
import _target.deps.mathlib.order.bounded_lattice
import _target.deps.mathlib.order.bounds
import _target.deps.mathlib.order.complete_boolean_algebra
import _target.deps.mathlib.order.complete_lattice
import _target.deps.mathlib.order.default
import _target.deps.mathlib.order.filter
import _target.deps.mathlib.order.fixed_points
import _target.deps.mathlib.order.galois_connection
import _target.deps.mathlib.order.lattice
import _target.deps.mathlib.order.zorn
import _target.deps.mathlib.pending.default
import _target.deps.mathlib.tactic.alias
import _target.deps.mathlib.tactic.converter.binders
import _target.deps.mathlib.tactic.converter.interactive
import _target.deps.mathlib.tactic.converter.old_conv
import _target.deps.mathlib.tactic.default
import _target.deps.mathlib.tactic.finish
import _target.deps.mathlib.tactic.interactive
import _target.deps.mathlib.tactic.rcases
import _target.deps.mathlib.theories.set_theory
import _target.deps.mathlib.topology.continuity
import _target.deps.mathlib.topology.ennreal
import _target.deps.mathlib.topology.infinite_sum
import _target.deps.mathlib.topology.lebesgue_measure
import _target.deps.mathlib.topology.limits
import _target.deps.mathlib.topology.measurable_space
import _target.deps.mathlib.topology.measure
import _target.deps.mathlib.topology.metric_space
import _target.deps.mathlib.topology.outer_measure
import _target.deps.mathlib.topology.real
import _target.deps.mathlib.topology.topological_space
import _target.deps.mathlib.topology.topological_structures
import _target.deps.mathlib.topology.uniform_space

open tactic

-- builds the set of the names of all constants appearing in the expression e
meta def collect_consts (e : expr) : name_set :=
e.fold mk_name_set (λ e' _ l, if e'.is_constant then l.insert e'.const_name else l)

-- map takes names to lists of nats.
-- adds idx to map[n] for each n in refs
meta def update_const_map (map : rb_lmap name ℕ) (idx : ℕ) (refs : name_set) : rb_lmap name ℕ :=
refs.fold map (λ nm map', map'.insert nm idx)

-- produces an array containing the name, definition, and set of referenced constants for each declaration in the environment,
-- and a map taking every constant name to the list of indices of expressions that contain it
meta def get_all_decls : tactic (Σ n : ℕ, array (name×expr×name_set) n × rb_lmap name ℕ) :=
do env ← get_env,
   return $ env.fold
    ⟨_, (@array.nil (name×expr×name_set), mk_rb_map)⟩ 
    (λ dcl nat_arr,
        let consts := collect_consts dcl.value in
        match nat_arr with 
        | ⟨n, (arr, map)⟩ := ⟨_, (arr.push_back (dcl.to_name, dcl.value, consts), update_const_map map (n+1) consts)⟩ 
        end)

-- the command below takes ~10 seconds to run
#exit

run_cmd
do ⟨n, (arr, map)⟩ ← get_all_decls,
   trace "number of declarations in environment:", 
   trace n,
   trace "number of declarations whose proof contains the constant `nat`:",
   trace (map.find `nat).length

