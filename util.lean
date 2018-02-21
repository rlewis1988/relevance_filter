import float data.list
open native

meta instance : inhabited name_set := ⟨mk_name_set⟩

meta def native.rb_map.find' {α β} [inhabited β] (map : rb_map α β) (a : α) : β :=
match map.find a with
| some b := b
| none := default β
end

meta def declaration.is_defined : declaration → bool
| (declaration.defn _ _ _ _ _ _) := tt
| (declaration.thm _ _ _ _) := tt
| _ := ff

meta def name_set.inter (s1 s2 : name_set) : name_set :=
s1.fold mk_name_set (λ nm s, if s2.contains nm then s.insert nm else s)

meta def name_set.union (s1 s2 : name_set) : name_set :=
s1.fold s2 (λ nm s, s.insert nm)

meta def name_set.diff (s1 s2 : name_set) : name_set :=
s1.fold mk_name_set (λ nm s, if s2.contains nm then s else s.insert nm)

meta def native.rb_set.of_list {α : Type} [has_lt α] [decidable_rel ((<) : α → α → Prop)] : list α → rb_set α
| [] := mk_rb_set
| (h::t) := (native.rb_set.of_list t).insert h

--meta instance : has_lt float := ⟨λ a b, if a < b then ordering.lt else if a > b then ordering.gt else ordering.eq⟩

meta def native.rb_set.inth {α} [inhabited α] (s : rb_set α) (i : ℕ) : α :=
s.keys.inth i
