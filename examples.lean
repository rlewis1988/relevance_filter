import imports

import k_nn

open tactic expr
set_option profiler true
-- the commands below are slow

open native

/-meta def nativemap : rb_map ℕ float := 
(list.iota 10000).foldl (λ map n, map.insert n float.random) mk_rb_map

meta def nonnativemap : rbmap ℕ float :=
(list.iota 10000).foldl (λ map n, map.insert n float.random) (mk_rbmap _ _)

run_cmd (list.iota 100).mmap' (λ n, trace (nativemap.find n))
run_cmd (list.iota 100).mmap' (λ n, trace (nonnativemap.find n))-/
run_cmd
do (contents, features, ⟨n, names⟩) ← get_all_decls,
   trace n
   #exit
   ,
   trace "the most relevant facts to prove `(∀ x y : ℝ, x < y → ∃ z : ℝ, x < z ∧ z < y):",
   (do trace $ find_k_most_relevant_facts_to_expr `(∀ x y : ℝ, x < y → ∃ z : ℝ, x < z ∧ z < y) contents features names 20)

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


