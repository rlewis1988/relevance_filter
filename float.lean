-- this will only run on the hacked lean: https://github.com/rlewis1988/lean/floats

meta constant float : Type
meta constant float.to_string : float → string
meta constant float.add : float → float → float
meta constant float.sub : float → float → float
meta constant float.mul : float → float → float
meta constant float.lt : float → float → bool
meta constant float.log : float → float
meta constant float.pi : float 
meta constant float.float_of_int : int → float

meta instance : has_add float := ⟨float.add⟩
meta instance : has_sub float := ⟨float.sub⟩
meta instance : has_mul float := ⟨float.mul⟩
meta instance : has_lt float := ⟨λ x y, if float.lt x y then true else false⟩
meta instance : has_zero float := ⟨float.float_of_int 0⟩
meta instance : has_one float := ⟨float.float_of_int 1⟩

meta instance : has_to_string float := ⟨float.to_string⟩
meta instance : has_repr float := ⟨float.to_string⟩


open float array 


set_option unifier.nat_offset_cnstr_threshold 50000

#eval pi + pi
#eval pi*(10 - pi)
#eval float.lt (log pi) pi
#eval (90 : float)
#eval ([1, 2, 3, 4, 5] : list float).map log

meta def a := mk_array 10000 (2 : float)
meta def b  := a.read 500
 

