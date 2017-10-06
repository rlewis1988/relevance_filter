import _target.deps.mathlib.category.basic
import _target.deps.mathlib.algebra.ordered_ring
import _target.deps.mathlib.algebra.ordered_monoid
import _target.deps.mathlib.algebra.big_operators
import _target.deps.mathlib.algebra.ring
import _target.deps.mathlib.algebra.ordered_group
import _target.deps.mathlib.algebra.group_power
import _target.deps.mathlib.algebra.group
import _target.deps.mathlib.algebra.default
import _target.deps.mathlib.algebra.module
import _target.deps.mathlib.algebra.order
import _target.deps.mathlib.algebra.functions
import _target.deps.mathlib.algebra.field
import _target.deps.mathlib.theories.set_theory
import _target.deps.mathlib.pending.default
import _target.deps.mathlib.tactic.finish
import _target.deps.mathlib.tactic.alias
import _target.deps.mathlib.tactic.rcases
import _target.deps.mathlib.tactic.converter.old_conv
import _target.deps.mathlib.tactic.converter.interactive
import _target.deps.mathlib.tactic.converter.binders
import _target.deps.mathlib.tactic.default
import _target.deps.mathlib.tactic.interactive
import _target.deps.mathlib.logic.basic
import _target.deps.mathlib.logic.function_inverse
import _target.deps.mathlib.data.seq.wseq
import _target.deps.mathlib.data.seq.parallel
import _target.deps.mathlib.data.seq.seq
import _target.deps.mathlib.data.seq.computation
import _target.deps.mathlib.data.fin
import _target.deps.mathlib.data.hash_map
import _target.deps.mathlib.data.nat.basic
import _target.deps.mathlib.data.nat.sqrt
import _target.deps.mathlib.data.nat.gcd
import _target.deps.mathlib.data.nat.dist
import _target.deps.mathlib.data.nat.prime
import _target.deps.mathlib.data.nat.pairing
import _target.deps.mathlib.data.pnat
import _target.deps.mathlib.data.encodable
import _target.deps.mathlib.data.num.lemmas
import _target.deps.mathlib.data.num.basic
import _target.deps.mathlib.data.num.bitwise
import _target.deps.mathlib.data.array.lemmas
import _target.deps.mathlib.data.prod
import _target.deps.mathlib.data.fp.basic
import _target.deps.mathlib.data.option
import _target.deps.mathlib.data.int.basic
import _target.deps.mathlib.data.int.order
import _target.deps.mathlib.data.finset.basic
import _target.deps.mathlib.data.finset.fold
import _target.deps.mathlib.data.finset.default
import _target.deps.mathlib.data.quot
import _target.deps.mathlib.data.rat
import _target.deps.mathlib.data.set.enumerate
import _target.deps.mathlib.data.set.basic
import _target.deps.mathlib.data.set.prod
import _target.deps.mathlib.data.set.lattice
import _target.deps.mathlib.data.set.intervals
import _target.deps.mathlib.data.set.default
import _target.deps.mathlib.data.set.disjointed
import _target.deps.mathlib.data.set.countable
import _target.deps.mathlib.data.set.finite
import _target.deps.mathlib.data.equiv
import _target.deps.mathlib.data.subtype
import _target.deps.mathlib.data.bool
import _target.deps.mathlib.data.list.set
import _target.deps.mathlib.data.list.basic
import _target.deps.mathlib.data.list.comb
import _target.deps.mathlib.data.list.perm
import _target.deps.mathlib.data.list.default
import _target.deps.mathlib.data.list.sort
import _target.deps.mathlib.data.sigma.basic
import _target.deps.mathlib.data.sigma.default
import _target.deps.mathlib.data.pfun
import _target.deps.mathlib.analysis.limits
import _target.deps.mathlib.analysis.measure_theory.lebesgue_measure
import _target.deps.mathlib.analysis.measure_theory.measure_space
import _target.deps.mathlib.analysis.measure_theory.measurable_space
import _target.deps.mathlib.analysis.measure_theory.borel_space
import _target.deps.mathlib.analysis.measure_theory.outer_measure
import _target.deps.mathlib.analysis.topology.topological_space
import _target.deps.mathlib.analysis.topology.topological_structures
import _target.deps.mathlib.analysis.topology.continuity
import _target.deps.mathlib.analysis.topology.infinite_sum
import _target.deps.mathlib.analysis.topology.uniform_space
import _target.deps.mathlib.analysis.ennreal
import _target.deps.mathlib.analysis.of_nat
import _target.deps.mathlib.analysis.metric_space
import _target.deps.mathlib.analysis.real
import _target.deps.mathlib.order.zorn
import _target.deps.mathlib.order.basic
import _target.deps.mathlib.order.complete_boolean_algebra
import _target.deps.mathlib.order.boolean_algebra
import _target.deps.mathlib.order.bounds
import _target.deps.mathlib.order.lattice
import _target.deps.mathlib.order.galois_connection
import _target.deps.mathlib.order.bounded_lattice
import _target.deps.mathlib.order.default
import _target.deps.mathlib.order.filter
import _target.deps.mathlib.order.fixed_points
import _target.deps.mathlib.order.complete_lattice
import float sort util




open tactic

/--
 builds the set of the names of all constants appearing in the expression e
-/
meta def collect_consts (e : expr) : name_set :=
e.fold mk_name_set 
  (λ e' _ l, match e' with
  | expr.const nm _ := l.insert nm 
  | _ := l
  end)

/--
 map sends a name to the set of names which reference it.
 update_features_map extends this map by adding idx to the set for each name in refs.
-/
meta def update_features_map (map : rb_map name name_set) (idx : name) (refs : name_set) : rb_map name name_set :=
refs.fold map (λ nm map', map'.insert nm ((map'.find' nm).insert idx))

/--
 Given a new declaration and the current collected data, adds the info from the new declaration.
 Returns (contents_map, features_map, names), where
  - contents_map maps a name dcl to a pair of name_sets (tp_consts, val_consts), where tp_consts contains
     the symbols appearing in the type of dcl and val_consts contains the symbols appearing in the type of dcl
  - features_map maps a name nm to the set of names for which nm appears in the value
  - names is a list of all declaration names that have appeared
-/
meta def update_name_maps (dcl_name : name) (dcl_type : expr) (dcl_value : expr) : 
     (rb_map name (name_set × name_set) × (rb_map name name_set) × Σ n, array name n) →  
         (rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array name n 
| (contents_map, features_map, ⟨n, names⟩):=
  let val_consts := collect_consts dcl_value,
      tp_consts := collect_consts dcl_type,
      contents_map' := contents_map.insert dcl_name (tp_consts, val_consts),
      features_map' := update_features_map features_map dcl_name tp_consts in
  (contents_map', features_map', ⟨_, names.push_back dcl_name⟩)

/--
 Maps update_name_maps over the whole environment, excluding meta definitions.
 Returns (contents_map, features_map, names), where
  - contents_map maps a name dcl to a pair of name_sets (tp_consts, val_consts), where tp_consts contains
     the symbols appearing in the type of dcl and val_consts contains the symbols appearing in the value of dcl
  - features_map maps a name nm to the set of names for which nm appears in the value
  - names is a list of all declaration names that have appeared 
-/
meta def get_all_decls : tactic ((rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array name n) :=
do env ← get_env,
   return $ env.fold
    (mk_rb_map, mk_rb_map, ⟨0, array.nil⟩) 
    (λ dcl nat_arr, 
     match dcl with
     | declaration.defn nm _ tp val _ tt := update_name_maps nm tp val nat_arr
     | declaration.thm nm _ tp val := update_name_maps nm tp val.get nat_arr
     | _ := nat_arr
     end)


section features_map
variable features_map : rb_map name name_set

meta def feature_weight (feature : name) : float :=
let l := float.float_of_int (features_map.find' feature).size in
if l > 0 then 1 + float.log l else 0

meta def feature_distance (f1 f2 : name_set) : float :=
let common := f1.inter f2 in
(common.to_list.map (λ n, float.pow (feature_weight features_map n) 6)).sum

/-meta def common_features (n1 n2 : name) : name_set := 
(features_map.find' n1).inter (features_map.find' n2)

meta def name_distance (n1 n2 : name) : float :=
let cf := common_features features_map n1 n2 in
(cf.to_list.map (feature_weight features_map)).sum

meta def name_distance_ordering_from (root : name) : has_ordering name :=
⟨λ n1 n2,
 let n1d := name_distance features_map n1 root,
     n2d := name_distance features_map n2 root in
 if n1d < n2d then ordering.lt else if n1d > n2d then ordering.gt else ordering.eq⟩-/

meta def name_distance (contents_map : rb_map name (name_set×name_set)) (n1 n2 : name) : float :=
let f1 := (contents_map.find' n1).1,
    f2 := (contents_map.find' n2).2 in
feature_distance features_map f1 f2

meta def name_feature_distance (contents_map : rb_map name (name_set×name_set)) (n1 : name) (f2 : name_set) : float :=
let f1 := (contents_map.find' n1).1 in
feature_distance features_map f1 f2


end features_map


meta def find_smallest_in_array {n α} [inhabited α] (a : array α n) (lt : α → α → bool) : list α :=
a.foldl [] (λ nm l, if lt nm (l.head) then [nm] else if lt l.head nm then l else nm::l)

meta def nearest_k (features : name_set) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let sorted := partial_quicksort
      (λ n1 n2, name_feature_distance features_map contents_map n2 features < name_feature_distance features_map contents_map n1 features)
       names k,
    name_list := if h : k ≤ n then (sorted.take k h).to_list else sorted.to_list in
name_list.map (λ n, (n, name_feature_distance features_map contents_map n features))

meta def nearest_k_of_expr (e : expr) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let features := collect_consts e in nearest_k features contents_map features_map names k

meta def nearest_k_of_name (nm : name) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let features := (contents_map.find' nm).1 in nearest_k features contents_map features_map names k


meta def relevance_to_feature (goal : name_set) (feature : name) (contents_map : rb_map name (name_set × name_set))
     (nearest : list (name × float)) : float :=
let nearest_map := rb_map.of_list nearest in
((27 : float) / 10)*((nearest.filter (λ b : name × float, (contents_map.find' b.1).2.contains feature)).map (λ nm_flt : name × float, nm_flt.2 / (float.float_of_int (contents_map.find' nm_flt.1).2.size))).sum + nearest_map.find' feature


meta def find_k_most_relevant_facts_to_goal (goal : name_set)  (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let nearest := nearest_k goal contents_map features_map names k,
    relevant := partial_quicksort (λ n1 n2, relevance_to_feature goal n2 contents_map nearest < relevance_to_feature goal n1 contents_map nearest) names k,
    name_list := if h : k ≤ n then (relevant.take k h).to_list else relevant.to_list in
name_list.map (λ n, (n, relevance_to_feature goal n contents_map nearest))


meta def find_k_most_relevant_facts_to_expr (goal : expr)  (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let features := collect_consts goal in
find_k_most_relevant_facts_to_goal features contents_map features_map names k

set_option profiler true
-- the commands below are slow
#exit
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
