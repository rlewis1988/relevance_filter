import float sort data.list.sort

set_option profiler true
#check list.qsort
#exit

run_cmd return $ merge_sort $ (mk_array 20000 (1 : float)).map (λ _, float.random) -- 4 sec
run_cmd return $ quicksort (λ a b, a < b) $ (mk_array 20000 (1 : float)).map (λ _, float.random) -- .55
run_cmd return $ list.merge_sort (λ a b, a < b) ((list.repeat (0 : ℕ) 20000).map (λ _, float.random)) -- .24
run_cmd return $ list.qsort (λ a b, a < b) ((list.repeat (0 : ℕ) 20000).map (λ _, float.random)) -- .31
