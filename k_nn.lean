
import data.vector
import float sort util -- name clash: see https://github.com/leanprover/lean/issues/1841

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
let arr_val_pr : array (name × float) n := ⟨λ i, let v := names.read i in (v, name_feature_distance features_map contents_map v features)⟩, 
    sorted := partial_quicksort
      (λ n1 n2 : name × float, float.lt n2.2 n1.2)
       arr_val_pr k,
    name_list := if h : k ≤ n then (sorted.take k h).to_list else sorted.to_list in
name_list

meta def nearest_k_of_expr (e : expr) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let features := collect_consts e in nearest_k features contents_map features_map names k

meta def nearest_k_of_name (nm : name) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let features := (contents_map.find' nm).1 in nearest_k features contents_map features_map names k

def find_val_in_list {α β} [decidable_eq α] [inhabited β] (a : α) : list (α × β) → β 
| [] := default β
| ((a', b)::t) := if a = a' then b else find_val_in_list t

meta def relevance_to_feature (goal : name_set) (feature : name) (contents_map : rb_map name (name_set × name_set))
     (nearest : list (name × float)) : float :=
let --nearest_map := rb_map.of_list nearest,
    contains_feature := nearest.filter (λ b : name × float, (contents_map.find' b.1).2.contains feature),
    weighted_vals := (contains_feature.map
     (λ nm_flt : name × float, nm_flt.2 / (float.float_of_int (contents_map.find' nm_flt.1).2.size))) in
((27 : float) / 10)*weighted_vals.sum + find_val_in_list feature nearest  --nearest_map.find' feature


-- TODO: the k in nearest_k shouldn't be the same as the argument k
meta def find_k_most_relevant_facts_to_goal (goal : name_set)  (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let nearest := nearest_k goal contents_map features_map names k,
    name_val_prs : array (name × float) n := ⟨λ i, let v := names.read i in (v, relevance_to_feature goal v contents_map nearest)⟩,
    relevant := partial_quicksort (λ n1 n2 : name × float, float.lt n2.2 n1.2) name_val_prs k,
    name_list := if h : k ≤ n then (relevant.take k h).to_list else relevant.to_list in
name_list


meta def find_k_most_relevant_facts_to_expr (goal : expr)  (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array name n) (k : ℕ) : list (name × float) :=
let features := collect_consts goal in
find_k_most_relevant_facts_to_goal features contents_map features_map names k

