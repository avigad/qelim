import .main

/- Theorems -/

open tactic lia

example (x y z : int) : I (A' (atom.le 1 [2,3,4])) [x,y,z] ↔ 1 ≤ ((0 + 2 * x) + 3 * y) + 4 * z := 
begin
  refl,
end

#exit

meta def foobar : tactic unit := 
do `(%%x1 ≤ %%y1 ↔ %%x2 ≤ %%y2) ← target >>= whnf, 
  papply ``(le_iff_le %%x1 %%x2 %%y1 %%y2 
            (by {try {simp}; refl}) 
            _),
   skip
#check list.sum
lemma qq {a b c d : int} : a = b → c = d → 
  a + c = b + d := sorry
#check int.coe_neg_succ_eq_neg_succ_of_nat
example : ∀ (x y : int), ¬ (2 * x + 1 = 2 * y) :=
begin
  cooper, 
  apply le_iff_le, refl, 
  simp only [list.dot_prod, list.map,
    list.zip_pad, add_zero, zero_add], 
  -- simp only [add_zero], 
  -- unfold interp, unfold atom_type.val,
  -- unfold lia.val,
  
  rewrite (mul_comm h_1 2), 
  rewrite (mul_comm h _), 
  rewrite (add_comm (2 * h_1)),
  apply qq, 
  
  -- rewrite add_zero,  
  -- rw [int.coe_eq_of_nat, int.coe_neg_succ_eq_neg_succ_of_nat],




end

#exit
example : ∀ (x : int), ∃ (y : int), (2 * y ≤ x ∧ x < 2 * (y + 1)) := 
--by cooper' 

example : ∀ (y : int), ((∃ (d : int), y = 2 * d) → (∃ (c : int), y = 1 * c)) := 
--by cooper'

example : ∀ (x y z : int), (2 * x + 1 = 2 * y) → 129 < x + y + z :=
begin
  normalize_goal,
end

example : ∃ (x y : int), 5 * x + 3 * y = 1 := 
--by cooper' 

example : ∃ (w x y z : int), 2 * w + 3 * x + 4 * y + 5 * z = 1 := 
--by cooper' 

example : ∀ (x y : int), 6 * x = 5 * y → ∃ d, y = 3 * d := 
--by cooper' 

example : ∀ (x : int), (¬(∃ m, x = 2 * m) ∧ (∃ m, x = 3 * m + 1))
             ↔ ((∃ m, x = 12 * m + 1) ∨ (∃ m, x = 12 * m + 7)) := 
--by cooper'

-- example : ∃ (l : int), ∀ (x : int), 
--   x ≥ l → ∃ (u v : int), u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v := 
-- by cooper' -- timeout


/- Nontheorems -/

-- example : ∃ (x y z : int), 4 * x - 6 * y = 1 := 
-- by cooper' 

-- example : ∀ (x y : int), x ≤ y → 2 * x + 1 < 2 * y := 
-- by cooper' 

-- example : ∀ (a b : int), ∃ (x : int), a < 20 * x /\ 20 * x < b := 
-- by cooper' 

-- example : ∃ (y : int), ∀ x, 2 ≤ x + 5 * y ∧ 2 ≤ 13 * x - y ∧ x + 3 ≤ 0 := 
-- by cooper' 

-- example : ∀ (x y : int), ¬(x = 0) → 5 * y + 1 ≤ 6 * x ∨ 6 * x + 1 ≤ 5 * y  := 
-- by cooper' 

-- example : ∀ (z : int), 3 ≤ z → ∃ (x y : int), x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z := 
-- by cooper' -- timeout

-- example : ∃ (a b : int), a ≥ 2 ∧ b ≥ 2 ∧ ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧ (a = b) := 
-- by cooper' 

-- example : := 
-- by cooper' 
-- example : := 
-- by cooper' 
-- example : := 
-- by cooper' 