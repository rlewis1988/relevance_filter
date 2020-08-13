import .sort data.list.sort
open native

meta instance : inhabited float := ⟨0⟩

-- meta constant float.random : float

set_option profiler true
--set_option trace.array.update true

/-
all updates are destructive. I don't know why my array quicksort takes twice the time of list.qsort.
They seem to scale at the same rate.
-/

run_cmd 
--let arr := (mk_array 80 (1 : float)).map (λ _, float.random) in
do return $ quicksort (λ a b, float.lt a b) $ (mk_array 8000 (1 : float)).map (λ _, float.random)
  -- return $ list.qsort (λ a b, float.lt a b) ((mk_array 8000 (1 : float)).map (λ _, float.random)).to_list

#exit
run_cmd let a := (mk_array 800 (1 : float)).map (λ _, float.random) -- .55
in tactic.trace $ ((a.write' 10 50).read' 10) + (a.read' 1)


#exit
run_cmd return $ merge_sort $ (mk_array 20000 (1 : float)).map (λ _, float.random) -- 4 sec
run_cmd return $ quicksort (λ a b, a < b) $ (mk_array 20000 (1 : float)).map (λ _, float.random) -- .55
run_cmd return $ list.merge_sort (λ a b, a < b) ((list.repeat (0 : ℕ) 20000).map (λ _, float.random)) -- .24
run_cmd return $ list.qsort (λ a b, a < b) ((list.repeat (0 : ℕ) 20000).map (λ _, float.random)) -- .31
