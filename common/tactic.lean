import .auxiliary

open tactic 

meta def tmrk : nat → tactic unit
| n := trace n 

meta def pad_print : nat → string → tactic unit
| n s := 
  do trace $ spaces n ++ s 

meta def print_expr : nat → expr → tactic unit 
| k (expr.lam n m d b) := 
  pad_print k "lam" >> print_expr (k+2) b 
| k (expr.app e1 e2) := 
  pad_print k "app" 
  >> print_expr (k+2) e1 
  >> print_expr (k+2) e2 
| k (expr.pi n m d b) := 
  pad_print k "pi" >> print_expr (k+2) b 
| k (expr.local_const n m d b) :=  
  pad_print k "lconst" >> print_expr (k+2) b 
| k (expr.mvar n m e') :=  
  pad_print k "mvar" >> print_expr (k+2) e' 
| k e := pad_print k e.to_string

meta def rewrite_target_pexpr (pe : pexpr) :=
to_expr pe >>= rewrite_target