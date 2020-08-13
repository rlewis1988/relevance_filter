/-
Sorting on arrays.
-/

section quicksort

variables {α : Type}  [inhabited α] 
  (op : α → α → bool)
local infix `<` := op
variable  [has_to_format α]

meta def swap {n : ℕ} (A : array n α) (i j : ℕ) : array n α:=
let tmp_j := A.read' j,
    tmp_i := A.read' i in
(A.write' j tmp_i).write' i tmp_j 

meta def partition_aux (hi : ℕ) (pivot : α) {n : ℕ} : Π (A : array n α) (i j : ℕ), ℕ × array n α
| A i j :=
if j = hi then (i, A) else
let tmp_j := A.read' j in
if bnot (tmp_j < pivot) then partition_aux A i (j+1) else
  let tmp_i := A.read' i,
      A' := (A.write' j tmp_i).write' i tmp_j in
  partition_aux A' (i+1) (j+1)
--else
--  partition_aux A i (j+1) 

meta def partition {n : ℕ} (A : array n α) (lo hi : ℕ) : ℕ × array n α :=
let pivot := A.read' hi,
    i := lo,
    (i', A') := partition_aux op hi pivot A i lo,
    A'' := if A'.read' hi < A'.read' i' then swap A' i' hi else A' in
(i', A'')

meta def quicksort_aux {n : ℕ} : Π (A : array n α) (lo hi : ℕ), array n α
| A lo hi := 
if bnot (nat.lt lo hi) then A else
let (p, A') := partition op A lo hi in
quicksort_aux (quicksort_aux A' lo (p-1)) (p+1) hi


meta def quicksort {n : ℕ} (A : array n α) : array n α :=
quicksort_aux op A 0 (n-1)

meta def partial_quicksort_aux {n : ℕ} : Π (A : array n α) (lo hi k : ℕ), array n α
| A lo hi k := 
if nat.lt lo hi then
  let (p, A') := partition op A lo hi,
      A'' := partial_quicksort_aux A' lo (p-1) k in
  if nat.lt p (k-1) then partial_quicksort_aux A'' (p+1) hi k else A''
else A

meta def partial_quicksort {n : ℕ} (A : array n α) (k : ℕ) : array n α :=
partial_quicksort_aux op A 0 (n-1) k

end quicksort

-- super inefficient, for comparison
section mergesort

meta def merge {α : Type} [decidable_linear_order α] [inhabited α] [has_to_format α] {m n}
     (lhs : array m α) (rhs : array n α) : array (m + n) α:=
let bgn := mk_array (m+n) (default α),
    pr := bgn.iterate (0, 0, bgn) 
            (λ i a interm, match interm with
            | (ln, rn, arr) := 
             if (rn ≥ n) || ((ln < m) && (lhs.read' ln ≤ rhs.read' rn)) then 
                (ln+1, rn, arr.write i (lhs.read' ln)) 
             else (ln, rn+1, arr.write i (rhs.read' rn))
            end) in
pr.2.2

meta def merge_sort {α : Type} [decidable_linear_order α] [inhabited α] [has_to_format α] : Π {n}, array n α → array n α
| 0 a     := a
| 1 a     := a
| (n+2) a := 
  let lhs := merge_sort (a.slice 0 (n/2 + 1) undefined undefined),
      rhs := merge_sort (a.slice (n/2 + 1) (n+2) undefined undefined) in
  unchecked_cast $ merge lhs rhs

end mergesort
