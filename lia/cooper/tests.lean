/- Test cases for cooper, from John Harrison's Handbook of Practical Logic and Automated Reasoning. -/

import .main

set_option profiler true

/- Theorems -/

open tactic lia

example : ∃ (x : int), x < 1 := 
by cooper

example : ∀ (x : int), ∃ (y : int), y = x + 1 := 
by cooper_vm

example : ∀ (x : int), ∃ (y : int), (2 * y ≤ x ∧ x < 2 * (y + 1)) := 
by cooper_vm

example : ∀ (y : int), ((∃ (d : int), y = 2 * d) → (∃ (c : int), y = 1 * c)) := 
by cooper_vm

example : ∀ (x y z : int), (2 * x + 1 = 2 * y) → 129 < x + y + z :=
by cooper_vm

example : ∃ (x y : int), 5 * x + 3 * y = 1 := 
by cooper_vm 

example : ∃ (w x y z : int), 2 * w + 3 * x + 4 * y + 5 * z = 1 := 
by cooper_vm 

example : ∀ (x y : int), 6 * x = 5 * y → ∃ d, y = 3 * d := 
by cooper_vm 

example : ∀ (x : int), (¬(∃ m, x = 2 * m) ∧ (∃ m, x = 3 * m + 1))
             ↔ ((∃ m, x = 12 * m + 1) ∨ (∃ m, x = 12 * m + 7)) := 
by cooper_vm

-- example : ∃ (l : int), ∀ (x : int), 
--   x ≥ l → ∃ (u v : int), u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v := 
-- by cooper_vm -- timeout

/- Nontheorems -/

--example : ∃ (x y z : int), 4 * x - 6 * y = 1 := 
--by cooper_vm

-- example : ∀ (x y : int), x ≤ y → ((2 * x) + 1) < 2 * y := 
-- by cooper_vm

-- example : ∀ (a b : int), ∃ (x : int), a < 20 * x /\ 20 * x < b := 
-- by cooper_vm 

-- example : ∃ (y : int), ∀ x, 2 ≤ x + 5 * y ∧ 2 ≤ 13 * x - y ∧ x + 3 ≤ 0 := 
-- by cooper_vm 

-- example : ∀ (x y : int), ¬(x = 0) → 5 * y + 1 ≤ 6 * x ∨ 6 * x + 1 ≤ 5 * y  := 
-- by cooper_vm 

--  example : ∀ (z : int), 3 ≤ z → ∃ (x y : int), x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z := 
--  by cooper_vm -- timeout

-- example : ∃ (a b : int), a ≥ 2 ∧ b ≥ 2 ∧ ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧ (a = b) := 
-- by cooper_vm 