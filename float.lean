-- this will only run on the hacked lean: https://github.com/rlewis1988/lean/floats

meta constant float : Type
meta constant float.to_string : float → string
meta constant float.add : float → float → float
meta constant float.sub : float → float → float
meta constant float.mul : float → float → float
meta constant float.div : float → float → float
meta constant float.lt : float → float → bool
meta constant float.log : float → float
meta constant float.pi : float 
meta constant float.float_of_int : int → float
meta constant float.random : float
meta constant float.dec_eq : decidable_eq float
meta constant float.pow : float → float → float

meta instance : has_add float := ⟨float.add⟩
meta instance : has_sub float := ⟨float.sub⟩
meta instance : has_mul float := ⟨float.mul⟩
meta instance : has_div float := ⟨float.div⟩
meta instance : has_lt float := ⟨λ x y, if float.lt x y then true else false⟩
meta instance : has_zero float := ⟨float.float_of_int 0⟩
meta instance : has_one float := ⟨float.float_of_int 1⟩

meta instance : has_to_string float := ⟨float.to_string⟩
meta instance : has_repr float := ⟨float.to_string⟩
meta instance : has_to_format float := ⟨λ f, repr f⟩

meta instance : inhabited float := ⟨0⟩

meta instance float.decidable_lt : decidable_rel (@has_lt.lt float _) :=
λ x y, begin
  change x < y with if float.lt x y then true else false,
  cases float.lt x y,
  apply decidable.is_false,
  rw if_neg,
  apply not_false,
  change ¬ ff = tt,
  simp,
  apply decidable.is_true,
  rw if_pos,
  trivial, apply rfl
  end 

attribute [instance] float.dec_eq

meta instance : decidable_linear_order float :=
{ le := λ x y, x < y ∨ x = y,
  decidable_le := by apply_instance,
  le_refl := undefined, le_trans := undefined, le_antisymm := undefined, le_total := undefined
}

open float array 


set_option unifier.nat_offset_cnstr_threshold 50000

/-#eval pi + pi
#eval pi*(10 - pi)
#eval float.lt (log pi) pi
#eval (90 : float)
#eval ([1, 2, 3, 4, 5] : list float).map log

meta def a := mk_array 10000 (2 : float)
--meta def b  := a.read 500
 
#eval a.read 1
-/
