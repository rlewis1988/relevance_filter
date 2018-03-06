import data.vector data.hash_map meta.expr 
import float sort util -- name clash: see https://github.com/leanprover/lean/issues/1841

open tactic native expr

/-class {u} map_structure (α : Type u) (key value : Type) :=
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
 
-/

/-meta def environment.mfold {m : Type} {s : Type} 
    (a : s) (f : declaration → s → state m s) (env : environment) : state m s := 
λ st, env.fold (a, st) (λ dcl pr, f dcl pr.1 pr.2)-/
meta def environment.mfold {m : Type → Type} [monad m] {s : Type} 
    (a : s) (f : declaration → s → m s) (env : environment) : m s := 
env.fold (return a) (λ dcl ms, ms >>= f dcl) 

meta def name_lt : has_lt name := ⟨λ n1 n2, n1.to_string.to_nat < n2.to_string.to_nat⟩
--def name_lt_dec (n1 n2 : name) : decidable (n1.to_string.to_nat < n2.to_string.to_nat) := by a 

--local attribute [instance] name_lt

section
--parameters (α : Type) [map_structure α name ℕ] (β : Type) [set_structure β ℕ]

meta structure builder_state :=
(name_lookup : rb_map name ℕ) -- maps a name to its location in names array
(dcls : ℕ) -- number of declarations
(names : array dcls name) -- array of declaration names
(appears_in_type : array dcls (rb_set ℕ)) -- the ith entry is the set of indices of names that appear in the type of declaration i
(appears_in_value : array dcls (rb_set ℕ))
(referenced_from_type : array dcls (rb_set ℕ)) -- the ith entry is the set of indices of declarations whose types contain constant i
(referenced_from_value : array dcls (rb_set ℕ))

meta def builder_state.format : builder_state → format
| ⟨_, _, names, _, _, _, _⟩ := to_fmt names

meta instance builder_state.has_to_format : has_to_format builder_state := ⟨builder_state.format⟩

@[reducible, inline] meta def mk_empty_builder_state : builder_state :=
{ name_lookup := mk_rb_map, 
  dcls := 0,
  names := array.nil,
  appears_in_type := array.nil,
  appears_in_value := array.nil,
  referenced_from_type := array.nil,
  referenced_from_value := array.nil }

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

/-@[reducible, inline] meta def insert_name (nm : name) : builder ℕ 
| p@⟨nl, n, nms, ait, aiv, rft, rfv⟩ :=
let opt := nl.find nm in 
if h : opt.is_some then 
  --(option.get h, p)
  (option.get h, mk_empty_builder_state)
else
    --let bs' : builder_state :=
    (n, 
⟨ nl.insert nm n,
        n+1,
        nms.push_back nm,
        ait.push_back mk_rb_set,
        aiv.push_back mk_rb_set,
        rft.push_back mk_rb_set,
        rfv.push_back mk_rb_set ⟩)
        -/

meta def find_in_name_list (nm : name) : builder (option ℕ) :=
λ p, (p.name_lookup.find nm, p)

meta def insert_name_aux (nm : name) : option ℕ → builder ℕ
| (some k) p := (k, p)
| none ⟨nl, n, nms, ait, aiv, rft, rfv⟩ :=     (n, 
⟨ nl.insert nm n,
        n+1,
        nms.push_back nm,
        ait.push_back mk_rb_set,
        aiv.push_back mk_rb_set,
        rft.push_back mk_rb_set,
        rfv.push_back mk_rb_set ⟩)

meta def insert_name (nm : name) : builder ℕ :=
do o ← find_in_name_list nm,
   insert_name_aux nm o


/-@[reducible, inline] meta def insert_name (nm : name) : builder ℕ 
| ⟨nl, n, nms, ait, aiv, rft, rfv⟩ := 
match nl.find nm with 
  | some k := (k, ⟨nl, n, nms, ait, aiv, rft, rfv⟩)--(k, mk_empty_builder_state)
  | none :=
    --let bs' : builder_state :=
    (n, 
⟨ nl.insert nm n,
        n+1,
        nms.push_back nm,
        ait.push_back mk_rb_set,
        aiv.push_back mk_rb_set,
        rft.push_back mk_rb_set,
        rfv.push_back mk_rb_set ⟩)
end-/



/-@[reducible, inline] meta def insert_name (nm : name) : builder ℕ 
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
  end-/

/-@[reducible, inline] -/meta def set_appears_in_type (idx : ℕ) (cset : rb_set ℕ) : builder unit
| ⟨nl, n, nms, ait, aiv, rft, rfv⟩ := ((), ⟨nl, n, nms, ait.write' idx cset, 
             aiv, rft, rfv ⟩ )
--{p with appears_in_type := p.appears_in_type.write' idx cset})

/-@[reducible, inline] -/meta def set_appears_in_value (idx : ℕ) (cset : rb_set ℕ) : builder unit
| ⟨nl, _, nms, ait, aiv, rft, rfv⟩ := ((), ⟨nl, _, nms, ait,
             aiv.write' idx cset, rft, rfv ⟩ )
--{p with appears_in_value := p.appears_in_type.write' idx cset})

/-@[reducible, inline] -/meta def update_ns_array {n} (nsa : array n (rb_set ℕ)) (idx nval : ℕ) : array n (rb_set ℕ) := 
if h : idx < n then
 let idx' : fin n := fin.mk _ h in
 nsa.write idx' (/-(nsa.read idx')-/mk_rb_set.insert nval)
else nsa

/-@[reducible, inline]-/ meta def add_idx_to_referenced_from_type (old_idx new_idx : ℕ) : builder unit
| ⟨nl, _, nms, ait, aiv, rft, rfv⟩ := ((), ⟨nl, _, nms, ait, 
             aiv, update_ns_array rft old_idx new_idx, rfv ⟩ )
             
--{p with referenced_from_type := update_ns_array p.referenced_from_type old_idx new_idx})

/-@[reducible, inline]-/ meta def add_idx_to_referenced_from_value (old_idx new_idx : ℕ) : builder unit
| ⟨nl, _, nms, ait, aiv, rft, rfv⟩ := ((), ⟨nl, _, nms, ait, 
             aiv, rft, update_ns_array rfv old_idx new_idx ⟩ )
            
            
--{p with referenced_from_value := update_ns_array p.referenced_from_type old_idx new_idx})


/-@[reducible, inline] -/meta def get_idx (nm : name) : builder (option ℕ) := 
λ p, (rb_map.find p.name_lookup nm, p)

meta def collect_consts_aux (e : expr) : builder (list ℕ) :=
e.mfold ([]) 
  (λ e' _ st, match e' with
  | expr.const nm _ := do n ← insert_name nm, return $  n::st
  | _ := return st
  end)

meta def collect_consts (e : expr) : builder (rb_set ℕ) :=
do l ← collect_consts_aux e,
   return $ rb_set.of_list l 

  


/-
-- we assume no mvars or local_consts or macros
meta def collect_consts_aux : expr → list ℕ → builder (list ℕ)
| (expr.const nm _) st := do n ← insert_name nm, return $ n::st
| (app e1 e2) st := do collect_consts_aux e1 st >>= collect_consts_aux e2
| (lam _ _ e1 e2) st := do collect_consts_aux e1 st >>= collect_consts_aux e2
| (pi _ _ e1 e2) st := do collect_consts_aux e1 st >>= collect_consts_aux e2
| (elet _ e1 e2 e3) st := do collect_consts_aux e1 st >>= collect_consts_aux e2 >>= collect_consts_aux e3
| _ st := return st

@[reducible, inline] meta def collect_consts (e : expr) : builder (rb_set ℕ) :=
do l ← collect_consts_aux e [],
   return $ rb_set.of_list l -/

#check @rb_set.mfold
meta def native.rb_set.mfold' {key : Type} {m : Type → Type} [monad m] (s : rb_set key) 
     (f : key → m unit) : m unit :=
s.mfold () (λ k _, f k)

meta def process_dcl (dcl_name : name) (dcl_type dcl_value : expr) : builder unit :=
do idx ← insert_name (/-trace_val-/ dcl_name),
   tp_cnsts ← collect_consts (/-trace_val-/ dcl_type),
   set_appears_in_type (/-trace_val-/ idx) tp_cnsts,
   val_cnsts ← collect_consts dcl_value,
   set_appears_in_value idx val_cnsts,
   native.rb_set.mfold' tp_cnsts (λ a, add_idx_to_referenced_from_type a idx),
   native.rb_set.mfold' val_cnsts (λ a, add_idx_to_referenced_from_value a idx)

meta def process_const_dcl (dcl_name : name) (dcl_type : expr) : builder unit :=
do idx ← insert_name dcl_name,
   tp_cnsts ← collect_consts dcl_type,
   set_appears_in_type idx tp_cnsts,
   native.rb_set.mfold' tp_cnsts (λ a, add_idx_to_referenced_from_type a idx)

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

end

namespace tests
--set_option trace.array.update true 
set_option profiler true 

run_cmd 
do dcl ← get_decl ``hash_map.find_erase_ne,
   trace $ (collect_consts dcl.value >> collect_consts dcl.type) mk_empty_builder_state

run_cmd  
 do bs ← create_builder_structures,
    return ()
    --trace $ bs.dcls 
end tests