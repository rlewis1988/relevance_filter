
import data.vector data.hash_map meta.expr 
import float sort util -- name clash: see https://github.com/leanprover/lean/issues/1841

class {u} map_structure (α : Type u) (key value : Type) :=
(contains : α → key → bool)
(find : α → key → option value)
(insert : α → key → value → α)
(mk_empty : α)

class {u} set_structure (α : Type u) (key : Type) :=
(contains : α → key → bool)
(insert : α → key → α)
(mk_empty : α)
(mfold : Π {out : Type} {m : Type → Type} [monad m], α → out → (key → out → m out) → m out)

meta def set_structure.mfold' {α key} [set_structure α key] {m : Type → Type} [monad m] (a : α) (f : key → m unit) : m unit :=
set_structure.mfold a () (λ k _, f k)

class {u} has_hash (α : Type u) := 
(hash : α → ℕ)

instance : has_hash string := ⟨string.to_nat⟩

instance : has_hash name := ⟨string.to_nat ∘ name.to_string⟩

instance : has_hash ℕ := ⟨id⟩

open tactic native expr

meta instance rb_map_ms {α β} [has_lt α] [decidable_rel ((<) : α → α → Prop)] : map_structure (rb_map α β) α β :=
{ contains := rb_map.contains,
  find := rb_map.find,
  insert := rb_map.insert,
  mk_empty := mk_rb_map }

meta instance rbmap_ms {α β lt} [decidable_rel lt] : map_structure (rbmap α β lt) α β :=
{ contains := rbmap.contains,
  find := rbmap.find,
  insert := rbmap.insert,
  mk_empty := mk_rbtree _ _ }

meta instance hash_map_ms {α β} [decidable_eq α] [has_hash α] : map_structure (hash_map α (λ _, β)) α β :=
{ contains := hash_map.contains,
  find := hash_map.find,
  insert := hash_map.insert,
  mk_empty := mk_hash_map has_hash.hash }

meta instance rb_set_ss {α} [has_lt α] [decidable_rel ((<) : α → α → Prop)] : set_structure (rb_set α) α :=
{ contains := rb_set.contains,
  insert := rb_set.insert,
  mk_empty := mk_rb_set,
  mfold := @rb_set.mfold α }

meta instance name_set_ss : set_structure name_set name :=
{ contains := name_set.contains,
  insert := name_set.insert,
  mk_empty := mk_name_set,
  mfold := @name_set.mfold }

meta def hash_set_mfold {α} [decidable_eq α] {out : Type} {m : Type → Type} [monad m] 
     (map : hash_map α (λ _, unit)) (o : out) (f : α → out → m out) : m out :=
map.fold (return o) (λ o a _, o >>= f a)

meta instance hash_map_ss {α} [decidable_eq α] [has_hash α] : set_structure (hash_map α (λ _, unit)) α :=
{ contains := hash_map.contains,
  insert := λ map a, map.insert a (),
  mk_empty := mk_hash_map has_hash.hash,
  mfold := @hash_set_mfold α _ }
 

meta def environment.mfold {m : Type} {s : Type} 
    (a : s) (f : declaration → s → state m s) (env : environment) : state m s := 
λ st, env.fold (a, st) (λ dcl pr, f dcl pr.1 pr.2)

section
parameters (α : Type) [map_structure α name ℕ] (β : Type) [set_structure β ℕ]

meta structure builder_state :=
(name_lookup : α) -- maps a name to its location in names array
(dcls : ℕ) -- number of declarations
(names : array dcls name) -- array of declaration names
(appears_in_type : array dcls β) -- the ith entry is the set of indices of names that appear in the type of declaration i
/-(appears_in_value : array dcls β)
(referenced_from_type : array dcls β) -- the ith entry is the set of indices of declarations whose types contain constant i
(referenced_from_value : array dcls β)-/

meta def builder_state.format : builder_state → format
| ⟨_, _, names, _, /-_, _, _-/⟩ := to_fmt names

meta instance builder_state.has_to_format : has_to_format builder_state := ⟨builder_state.format⟩

@[reducible, inline] meta def mk_empty_builder_state : builder_state :=
{ name_lookup := map_structure.mk_empty _ name ℕ, 
  dcls := 0,
  names := array.nil,
  appears_in_type := array.nil,
/-  appears_in_value := array.nil,
  referenced_from_type := array.nil,
  referenced_from_value := array.nil -/}

meta def mk_empty_builder_state' : unit → builder_state := λ _,
⟨map_structure.mk_empty _ name ℕ, 0, array.nil, array.nil⟩

@[reducible] meta def builder := state builder_state
meta instance builder_monad : monad builder := by apply_instance



/-{ name_lookup := map_structure.insert nl nm n,
       dcls := n+1,
       names := nms.push_back nm,
       appears_in_type := ait.push_back (set_structure.mk_empty _ ℕ),
       appears_in_value := aiv.push_back (set_structure.mk_empty _ ℕ),
       referenced_from_type := rft.push_back (set_structure.mk_empty _ ℕ),
       referenced_from_value := rfv.push_back (set_structure.mk_empty _ ℕ) } )-/--in
    --(n, bs')   
  --end
  /-λ p, match map_structure.find ℕ p.name_lookup nm with
| some k := (k, mk_empty_builder_state)
| none := 
(p.dcls, { name_lookup := map_structure.insert p.name_lookup nm p.dcls,
       dcls := p.dcls+1,
       names := p.names.push_back nm,
       appears_in_type := p.appears_in_type.push_back (set_structure.mk_empty _ ℕ),
       appears_in_value := p.appears_in_value.push_back (set_structure.mk_empty _ ℕ),
       referenced_from_type := p.referenced_from_type.push_back (set_structure.mk_empty _ ℕ),
       referenced_from_value := p.referenced_from_value.push_back (set_structure.mk_empty _ ℕ) } )
end-/

@[reducible, inline] meta def insert_name (nm : name) : builder ℕ 
| ⟨nl, n, nms, ait/-, aiv, rft, rfv-/⟩ := 
/-match map_structure.find ℕ nl nm with 
  | some k := (k, mk_empty_builder_state)
  | none :=-/
    --let bs' : builder_state :=
    (n, 
⟨ map_structure.mk_empty _ name ℕ,--nl,--map_structure.insert nl nm n,
        n+1,
        nms.push_back nm,
        ait.push_back (set_structure.mk_empty _ ℕ)/-,
        aiv.push_back (set_structure.mk_empty _ ℕ),
        rft.push_back (set_structure.mk_empty _ ℕ),
        rfv.push_back (set_structure.mk_empty _ ℕ)-/ ⟩)
--end 
set_option pp.all true
#print insert_name

end

set_option profiler true
set_option trace.array.update true 
section
parameters (β : Type) [has_add β] (α : Type) [has_zero α]

structure mstr := 
(a : β) (k : ℕ) (arr1 : array k ℕ) (arr2 : array k α)

meta instance abc : has_to_format mstr := ⟨λ s, to_fmt s.k⟩-- ++ to_fmt s.arr1 ++ to_fmt s.arr2⟩

@[reducible] def my_monad := state mstr

meta instance ab : monad my_monad := by apply_instance

/-def mupd : my_monad unit :=
λ sk, ((), ⟨_, sk.arr1.push_back 1, sk.arr2.push_back 2⟩)-/


@[reducible, inline] def mupd2 (t : ℕ) : my_monad ℕ
| ⟨o, k, arr1, arr2⟩ := --match k+t with
--| 0 := (t, ⟨o, k, arr1, arr2⟩)
/-| nat.succ n := -/ (2, ⟨o+o, k+1, arr1.push_back t, arr2.push_back 0⟩)
--end
end
#print mupd2
@[inline] def empty_mstr : mstr ℕ ℕ := ⟨1, _, array.nil, array.nil⟩
run_cmd trace $ (mupd2 ℕ ℕ 5 >> mupd2 ℕ ℕ 2) ⟨1, _, array.nil, array.nil⟩
run_cmd trace $ mupd2 ℕ ℕ 5 (empty_mstr)


run_cmd 
-- let st := mk_empty_builder_state (rb_map name ℕ) (rb_set ℕ)-/ in
  trace $ (insert_name _ _ `hello >> insert_name _ _ `hello2)  
            (mk_empty_builder_state (rb_map name ℕ) (rb_set ℕ) 
  --(trace $ insert_name _ _ `hello (mk_empty_builder_state' (rb_map name ℕ) (rb_set ℕ) ()))

run_cmd 
-- let st := mk_empty_builder_state (rb_map name ℕ) (rb_set ℕ)-/ in
  trace $ insert_name (rb_map name ℕ) (rb_set ℕ) `hello ⟨mk_rb_map, 0, array.nil, @array.nil (rb_set ℕ)⟩
#print builder_state

def pb1 {k} (a : array k ℕ × array k ℕ) : array (k+1) ℕ := a.1.push_back 1

run_cmd 
trace $ pb1 (array.nil, array.nil)


run_cmd 
 --let st := mk_empty_builder_state (rb_map name ℕ) (rb_set ℕ) in
  trace $ insert_name _ _ `hello (mk_empty_builder_state (rb_map name ℕ) (rb_set ℕ))

#exit

meta def insert_name' (nm : name) : builder ℕ 
| p@⟨nl, n, nms, ait, aiv, rft, rfv⟩ := 
  match map_structure.find ℕ nl nm with 
  | some k := (k, p)
  | none := 
    --let bs' : builder_state :=
    (n, { name_lookup := map_structure.insert nl nm n,
       dcls := n+1,
       names := nms.push_back nm,
       appears_in_type := ait.push_back (set_structure.mk_empty _ ℕ),
       appears_in_value := aiv.push_back (set_structure.mk_empty _ ℕ),
       referenced_from_type := rft.push_back (set_structure.mk_empty _ ℕ),
       referenced_from_value := rfv.push_back (set_structure.mk_empty _ ℕ) } )--in
    --(n, bs')   
  end

meta def set_appears_in_type (idx : ℕ) (cset : β) : builder unit
| p := ((), {p with appears_in_type := p.appears_in_type.write' idx cset})

meta def set_appears_in_value (idx : ℕ) (cset : β) : builder unit
| p := ((), {p with appears_in_value := p.appears_in_type.write' idx cset})

meta def update_ns_array {n} (nsa : array n β) (idx nval : ℕ) : array n β := 
if h : idx < n then
 let idx' : fin n := fin.mk _ h in
 nsa.write idx' (set_structure.insert (nsa.read idx') nval)
else nsa

meta def add_idx_to_referenced_from_type (old_idx new_idx : ℕ) : builder unit
| p := ((), {p with referenced_from_type := update_ns_array p.referenced_from_type old_idx new_idx})

meta def add_idx_to_referenced_from_value (old_idx new_idx : ℕ) : builder unit
| p := ((), {p with referenced_from_value := update_ns_array p.referenced_from_type old_idx new_idx})


meta def get_idx (nm : name) : builder (option ℕ) := 
λ p, (map_structure.find ℕ p.name_lookup nm, p)

meta def collect_consts (e : expr) : builder β :=
e.mfold (set_structure.mk_empty _ ℕ) 
  (λ e' _ st, match e' with
  | expr.const nm _ := do n ← insert_name nm, return $ set_structure.insert st n
  | _ := return st
  end)

meta def process_dcl (dcl_name : name) (dcl_type dcl_value : expr) : builder unit :=
do idx ← insert_name dcl_name,
   tp_cnsts ← collect_consts dcl_type,
   set_appears_in_type idx tp_cnsts,
   val_cnsts ← collect_consts dcl_value,
   set_appears_in_value idx val_cnsts,
   set_structure.mfold' tp_cnsts (λ a, add_idx_to_referenced_from_type a idx),
   set_structure.mfold' val_cnsts (λ a, add_idx_to_referenced_from_value a idx)

meta def process_const_dcl (dcl_name : name) (dcl_type : expr) : builder unit :=
do idx ← insert_name dcl_name,
   tp_cnsts ← collect_consts dcl_type,
   set_appears_in_type idx tp_cnsts,
   set_structure.mfold' tp_cnsts (λ a, add_idx_to_referenced_from_type a idx)

meta def process_env (env : environment) : builder unit :=
env.mfold () 
  (λ dcl _, match dcl with
   | declaration.defn nm _ tp vl _ tt := process_dcl nm tp vl
   | declaration.thm nm _ tp vl := process_dcl nm tp vl.get
   | declaration.cnst nm _ tp tt := process_const_dcl nm tp
   | declaration.ax nm _ tp := process_const_dcl nm tp
   | _ := return () -- we can ignore meta decls
   end)

meta def create_builder_structures : tactic builder_state :=
do env ← get_env,
   return $ ((process_env env) mk_empty_builder_state).2
   
/-meta def const_cache := rb_map expr name_set 
@[reducible] meta def builder := state const_cache
meta instance : monad builder := by apply_instance

meta def get_cached_consts (e : expr) : builder (option name_set) :=
λ cache, (cache.find e, cache)

meta def update_cache (e : expr) (ns : name_set) : builder unit :=
λ cache, ((), cache.insert e ns)

private meta def collect_consts_aux (collect_consts : expr → builder name_set) : expr → builder name_set 
| (const nm _) := return $ mk_name_set.insert nm
| (app e1 e2) := do ns1 ← collect_consts e1, ns2 ← collect_consts e2, return $ ns1.union ns2
| (lam _ _ e1 e2) := do ns1 ← collect_consts e1, ns2 ← collect_consts e2, return $ ns1.union ns2
| (pi _ _ e1 e2) := do ns1 ← collect_consts e1, ns2 ← collect_consts e2, return $ ns1.union ns2
| (elet _ e1 e2 e3) := do ns1 ← collect_consts e1, ns2 ← collect_consts e2, ns3 ← collect_consts e3,
                           return $ (ns1.union ns2).union ns3
| _ := return mk_name_set


meta def collect_consts : expr → builder name_set :=
λ e,
do nso ← get_cached_consts e,
match nso with
| some ns := return ns 
| none := do ns ← collect_consts_aux collect_consts e, update_cache e ns, return ns
end-/

/--
 builds the set of the names of all constants appearing in the expression e
-/
meta def g''' := 0
/-meta def collect_consts (e : expr) : name_set :=
e.fold mk_name_set 
  (λ e' _ l, match e' with
  | expr.const nm _ := l.insert nm 
  | _ := l
  end)-/

/-
 Given a map of names to indices, builds a set of indices of the names of constants
 appearing in the expression e. Takes a buffer of names and extends it with new names, if found.

meta def collect_consts {α β : Type} [map_structure α name ℕ] [set_structure β ℕ] 
     (index_map : α) (e : expr) (name_array : buffer name) : α × β × buffer name :=
e.fold
  (index_map, set_structure.mk_empty β ℕ, name_array)
  (λ e' _ pr, match e', pr with
  | expr.const nm _, (a, b, p@⟨k, nar⟩) := 
    match map_structure.find ℕ a nm with
    | some n := (a, set_structure.insert b n, p)
    | none := (map_structure.insert a nm k, set_structure.insert b k, buffer.push_back p nm)
    end 
  | _, p := p
  end) 
-/

end 
namespace tests
set_option profiler true
set_option trace.array.update true 

run_cmd 
 let st := mk_empty_builder_state (rb_map name ℕ) (rb_set ℕ) in
  trace $ insert_name _ _ `hello (mk_empty_builder_state (rb_map name ℕ) (rb_set ℕ))

def pb1 {k} (a : array k ℕ × array k ℕ) : array (k+1) ℕ := a.1.push_back 1

run_cmd 
trace $ pb1 (array.nil, array.nil)

#exit
run_cmd 
 do bs ← create_builder_structures (rb_map name ℕ) (rb_set ℕ),
    trace $ bs.dcls 
#exit
run_cmd 
 do bs ← create_builder_structures (hash_map name (λ _, ℕ)) (hash_map ℕ (λ _, unit)),
    trace $ bs.dcls 
    
end tests

#exit

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
     (rb_map name (name_set × name_set) × (rb_map name name_set) × Σ n, array n name) →  
         builder ((rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array n name)
| (contents_map, features_map, ⟨n, names⟩):=
do val_consts ← collect_consts dcl_value,
   tp_consts ← collect_consts dcl_type,
let contents_map' := contents_map.insert dcl_name (tp_consts, val_consts),
let features_map' := update_features_map features_map dcl_name tp_consts,
return (contents_map', features_map', ⟨_, names.push_back dcl_name⟩)


/-meta def update_name_maps (dcl_name : name) (dcl_type : expr) (dcl_value : expr) : 
     (rb_map name (name_set × name_set) × (rb_map name name_set) × Σ n, array n name) →  
         (rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array n name 
| (contents_map, features_map, ⟨n, names⟩):=
  let val_consts := collect_consts dcl_value,
      tp_consts := collect_consts dcl_type,
      contents_map' := contents_map.insert dcl_name (tp_consts, val_consts),
      features_map' := update_features_map features_map dcl_name tp_consts in
  (contents_map', features_map', ⟨_, names.push_back dcl_name⟩)-/
#check @list.mfoldr

/--
 Maps update_name_maps over the whole environment, excluding meta definitions.
 Returns (contents_map, features_map, names), where
  - contents_map maps a name dcl to a pair of name_sets (tp_consts, val_consts), where tp_consts contains
     the symbols appearing in the type of dcl and val_consts contains the symbols appearing in the value of dcl
  - features_map maps a name nm to the set of names for which nm appears in the value
  - names is a list of all declaration names that have appeared 
-/
meta def environment.mfold {m : Type} {s : Type} 
    (a : s) (f : declaration → s → state m s) (env : environment) : state m s := 
λ st, env.fold (a, st) (λ dcl pr, f dcl pr.1 pr.2)

meta def name_map_of_env (env : environment) : 
     builder ((rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array n name) :=
env.mfold (mk_rb_map, mk_rb_map, ⟨0, array.nil⟩) 
 (λ dcl nat_arr,
  match dcl with
  | declaration.defn nm _ tp val _ tt := update_name_maps nm tp val nat_arr
  | declaration.thm nm _ tp val := update_name_maps nm tp val.get nat_arr
  | _ := return nat_arr
  end)

meta def get_all_decls : tactic ((rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array n name) :=
do env ← get_env,
   return $ (name_map_of_env env mk_rb_map).1

/-meta def get_all_decls : tactic ((rb_map name (name_set × name_set)) × (rb_map name name_set) × Σ n, array n name) :=
do env ← get_env,
   return $ env.fold
    (mk_rb_map, mk_rb_map, ⟨0, array.nil⟩) 
    (λ dcl nat_arr, 
     match dcl with
     | declaration.defn nm _ tp val _ tt := update_name_maps nm tp val nat_arr
     | declaration.thm nm _ tp val := update_name_maps nm tp val.get nat_arr
     | _ := nat_arr
     end)-/


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
    f2 := (contents_map.find' n2).1 in
feature_distance features_map f1 f2

meta def name_feature_distance (contents_map : rb_map name (name_set×name_set)) (n1 : name) (f2 : name_set) : float :=
let f1 := (contents_map.find' n1).1 in
feature_distance features_map f1 f2


end features_map


meta def find_smallest_in_array {n α} [inhabited α] (a : array n α) (lt : α → α → bool) : list α :=
a.foldl [] (λ nm l, if lt nm (l.head) then [nm] else if lt l.head nm then l else nm::l)

meta def nearest_k (features : name_set) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × float) :=
let arr_val_pr : array n (name × float) := ⟨λ i, let v := names.read i in (v, name_feature_distance features_map contents_map v features)⟩, 
    sorted := partial_quicksort
      (λ n1 n2 : name × float, float.lt n2.2 n1.2)
       arr_val_pr k,
    name_list := if h : k ≤ n then (sorted.take k h).to_list else sorted.to_list in
name_list

meta def nearest_k_of_expr (e : expr) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × float) :=
let features := collect_consts e in nearest_k features contents_map features_map names k

meta def nearest_k_of_name (nm : name) (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × float) :=
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
(2.7 : float)*weighted_vals.sum + find_val_in_list feature nearest  --nearest_map.find' feature


-- TODO: the k in nearest_k shouldn't be the same as the argument k
meta def find_k_most_relevant_facts_to_goal (goal : name_set)  (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × float) :=
let nearest := nearest_k goal contents_map features_map names k,
    name_val_prs : array n (name × float) := ⟨λ i, let v := names.read i in (v, relevance_to_feature goal v contents_map nearest)⟩,
    relevant := partial_quicksort (λ n1 n2 : name × float, float.lt n2.2 n1.2) name_val_prs k,
    name_list := if h : k ≤ n then (relevant.take k h).to_list else relevant.to_list in
name_list


meta def find_k_most_relevant_facts_to_expr (goal : expr)  (contents_map : rb_map name (name_set × name_set))
     (features_map : rb_map name name_set) {n} (names : array n name) (k : ℕ) : list (name × float) :=
let features := (collect_consts goal mk_rb_map).1 in
find_k_most_relevant_facts_to_goal features contents_map features_map names k

