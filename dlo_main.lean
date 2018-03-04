import .dlo_qelim .to_fm 

open tactic

meta def to_idx : expr → tactic nat 
| (expr.var n) := return n 
| _ := failed

meta def to_adlo (β : Type) [reflected β] (i : nat) : expr → tactic (adlo × list β)
| `(%%(expr.var m) = %%(expr.var n)) := return ((m =' n), [])
| `(%%(expr.var m) = %%ne) := 
  do bn ← eval_expr β ne,
     return ((m =' i), [bn])
| `(%%me = %%(expr.var n)) := 
  do bm ← eval_expr β me,
     return ((i =' n), [bm])
| `(%%me = %%ne) := 
  do bm ← eval_expr β me,
     bn ← eval_expr β ne,
     return ((i =' i+1), [bm,bn])
| `(%%(expr.var m) < %%(expr.var n)) := return ((m <' n), [])
| `(%%(expr.var m) < %%ne) := 
  do bn ← eval_expr β ne,
     return ((m <' i), [bn])
| `(%%me < %%(expr.var n)) := 
  do bm ← eval_expr β me,
     return ((i <' n), [bm])
| `(%%me < %%ne) := 
  do bm ← eval_expr β me,
     bn ← eval_expr β ne,
     return ((i <' i+1), [bm,bn])
| _ := failed

meta def dec_dlo_nat : tactic unit := 
do (p,ns) ← target >>= to_fm adlo nat (to_adlo nat) 0, 
   trace p, trace "\n", trace ns 

example : ¬ ∃ (n : nat), ¬ (n = 0 ∨ 0 < n) := by dec_dlo_nat 
