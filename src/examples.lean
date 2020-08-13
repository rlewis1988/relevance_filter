-- import category.basic
-- import algebra.ordered_monoid
import algebra.big_operators
import algebra.ring
import algebra.group_power
import algebra.group
import algebra.module
import algebra.field
import set_theory.zfc
-- import pending.default
import tactic.finish
import tactic.alias
import tactic.rcases
import tactic.converter.old_conv
import tactic.converter.interactive
import tactic.converter.binders
import tactic.default
import tactic.interactive
import topology.basic
-- import topology.topological_space
-- import topology.topological_structures
-- import topology.measure
-- import topology.continuity
-- import topology.infinite_sum
-- import topology.ennreal
-- import topology.measurable_space
-- import topology.uniform_space
-- import topology.metric_space
-- import topology.real
import logic.basic
-- import logic.function_inverse
import data.seq.wseq
import data.seq.parallel
import data.seq.seq
import data.seq.computation
import data.fin
import data.hash_map
import data.nat.basic
import data.nat.sqrt
import data.nat.gcd
-- import data.nat.sub
import data.nat.pairing
-- import data.nat.bquant
-- import data.pnat
-- import data.encodable
import data.num.lemmas
import data.num.basic
import data.num.bitwise
import data.array.lemmas
import data.prod
import data.fp.basic
-- import data.option
import data.int.basic
-- import data.int.order
import data.finset.basic
import data.finset.fold
import data.finset.default
import data.rat
import data.set.enumerate
import data.set.basic
-- import data.set.prod
import data.set.lattice
import data.set.default
import data.set.countable
import data.set.finite
import data.equiv.basic
import data.bool
-- import data.list.set
import data.list.basic
-- import data.list.comb
import data.list.perm
import data.list.default
import data.list.sort
import data.sigma.basic
import data.sigma.default
import data.pfun
import order.zorn
import order.basic
import order.complete_boolean_algebra
import order.boolean_algebra
import order.bounds
import order.lattice
import order.galois_connection
import order.bounded_lattice
import order.default
import order.filter
import order.fixed_points
import order.complete_lattice

import .k_nn

open tactic expr

--set_option profiler true
-- the commands below are slow
/-
run_cmd
do (contents, features, ⟨n, names⟩) ← get_all_decls,
   trace n,
   trace $ name_distance features contents `list.append_nil `list.append_nil,
   trace $ name_distance features contents `list.append_nil `list.nil_append,
   trace $ name_distance features contents `list.append_nil `list.append_assoc,
   trace $ name_distance features contents `list.append_nil `hash_map.valid.as_list_length,
   trace $ name_distance features contents `list.append_nil `list.has_append,
   trace $ name_distance features contents `list.append_nil `linear_ordered_semiring.le_of_add_le_add_left,
   trace "the nearest 10 declarations to `list.append_nil`:",
   trace $ nearest_k_of_name `list.append_nil  contents features names 10,
   trace "the nearest 50 declarations to `add_le_add`:",
   trace $ nearest_k_of_name `add_le_add  contents features names 50,
   trace "the nearest 20 declarations to `(∀ x y : ℝ, x < y → ∃ z : ℝ, x < z ∧ z < y):",
   trace $ nearest_k_of_expr  `(∀ x y : ℝ, x < y → ∃ z : ℝ, x < z ∧ z < y) contents features names 20,
   trace "the most relevant facts to prove `(∀ x y : ℝ, x < y → ∃ z : ℝ, x < z ∧ z < y):",
   trace $ find_k_most_relevant_facts_to_expr `(∀ x y : ℝ, x < y → ∃ z : ℝ, x < z ∧ z < y) contents features names 20

run_cmd
do (contents, features, ⟨n, names⟩) ← get_all_decls,
   trace "number of declarations in environment:", 
   trace n,
   trace "number of constants appearing in the type of `list.append_nil`:",
   trace $ (contents.find' `list.append_nil).1.size,
   trace "number of constants appearing in the proof of `list.append_nil`:",
   trace $ (contents.find' `list.append_nil).2.size,
   trace "number of declarations whose proof contains the constant `nat`:",
   trace $ (features.find' `nat).size,
   trace "number of declarations whose proof contains the constant `real`:",
   trace $ (features.find' `real).size,
   trace "they are:",
   trace $ (features.find' `real)

-/
