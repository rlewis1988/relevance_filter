import float data.list

meta instance : inhabited name_set := ⟨mk_name_set⟩


meta def rb_map.find' {α β} [inhabited β] (map : rb_map α β) (a : α) : β :=
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


meta def rb_set.of_list {α : Type} [has_ordering α] : list α → rb_set α
| [] := mk_rb_set
| (h::t) := (rb_set.of_list t).insert h

meta instance : has_ordering float := ⟨λ a b, if a < b then ordering.lt else if a > b then ordering.gt else ordering.eq⟩

meta def rb_set.inth {α} [inhabited α] (s : rb_set α) (i : ℕ) : α :=
s.keys.inth i
