import .correctness

open tactic

variable {α : Type}

meta def tmrk : nat → tactic unit
| n := trace n 

def spaces : nat → string  
| 0 := ""
| (k+1) := " " ++ spaces k 

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

lemma forall_iff_not_exists_not {α : Type} {p : α → Prop} :
   (∀ x, p x) ↔ (¬ ∃ x, ¬ p x) :=
by rewrite (@not_exists_not _ p (λ x, classical.dec _))

meta def elim_defs : tactic unit :=
`[repeat {simp only 
   [imp_iff_not_or, iff_iff_and_or_not_and_not]},
  repeat {simp only 
   [ge, gt, forall_iff_not_exists_not,
    int.lt_iff_add_one_le, le_antisymm_iff]}]

meta def to_coeffs : expr → tactic (int × list int) 
| `(%%t + %%s) := 
  do (i,lcfs) ← to_coeffs t, 
     (j,rcfs) ← to_coeffs s,
     return (i+j, list.comp_add lcfs rcfs)  
| `(%%t - %%s) := 
  do (i,lcfs) ← to_coeffs t, 
     (j,rcfs) ← to_coeffs s,
     return (i-j, list.comp_sub lcfs rcfs)  
| `(%%t * %%s) := 
  do (i,lcfs) ← to_coeffs t, 
     (j,rcfs) ← to_coeffs s,
     if (∀ (c : int), c ∈ lcfs → c = 0)
     then return (i*j, list.map_mul i rcfs)
     else if (∀ (c : int), c ∈ rcfs → c = 0)
          then return (j*i, list.map_mul j lcfs)
          else trace "Nonlinear term" >> failed
| `(- %%t) := 
  do (i,cfs) ← to_coeffs t,
     return (-i, list.map_neg cfs)
| (expr.var n) := return (0, list.update_nth_force [] n 1 0)
| c := 
  do z ← eval_expr int c, 
     return (z, [])

meta def coeffs_to_expr : nat → list int → tactic expr 
| _ [] := expr.of_int `(int) 0
| k (z::zs) := 
  do ze ← expr.of_int `(int) z,
     rhs ← coeffs_to_expr (k+1) zs, 
     adde ← to_expr ``(@has_add.add int _),
     mule ← to_expr ``(@has_mul.mul int _),
     -- e ← to_expr ``((int.mul %%(expr.mk_var k) %%ze) + %%rhs) ,
     return $ expr.mk_app adde [(expr.mk_app mule [(expr.mk_var k), ze]), rhs]

meta def normal_form : expr → tactic expr 
| `(%%pe ∧ %%qe) := 
  do pe' ← normal_form pe, 
     qe' ← normal_form qe, 
     return `(%%pe' ∧ %%qe')
| `(%%pe ∨ %%qe) := 
  do pe' ← normal_form pe, 
     qe' ← normal_form qe, 
     return `(%%pe' ∨ %%qe')
| `(¬ %%pe) :=
  do pe' ← normal_form pe, 
     return `(¬ %%pe')
| `(Exists %%(expr.lam n m b pe)) :=
  do pe' ← normal_form pe,
     to_expr ``(Exists %%(expr.lam n m b pe'))
| `(%%te ≤ %%se)  := 
  do (i,lcfs) ← to_coeffs te, 
     (j,rcfs) ← to_coeffs se,
     ce ← expr.of_int `(int) (i - j),
     rhs ← coeffs_to_expr 0 (list.comp_sub rcfs lcfs),
     to_expr ``(%%ce ≤ %%rhs)
| e := trace "Invalid input 4 : " >> trace e >> failed

lemma le_iff_zero_le_sub (a b) : a ≤ b ↔ (0 : int) ≤ b - a := sorry

meta def rewrite_target_pexpr (pe : pexpr) :=
to_expr pe >>= rewrite_target

meta def get_lhs : tactic expr := 
do `((_ ≤ %%lhs) ↔ _) ← target, return lhs 

meta def get_rhs : tactic expr := 
do `(_ ↔ (_ ≤ %%rhs)) ← target, return rhs 

meta def rep_lhs (t : expr → tactic unit) : tactic unit :=
repeat (get_lhs >>= t)

meta def rep_rhs (t : expr → tactic unit) : tactic unit :=
repeat (get_rhs >>= t)

meta def iter_rhs (t : expr → tactic unit) : expr → tactic unit 
| `(%%xe + %%ye) := 
  t xe <|> iter_rhs ye 
| _ := failed 

meta def rep_iter_rhs (t : expr → tactic unit) : tactic unit :=
repeat (get_rhs >>= iter_rhs t)

meta def group_right : tactic unit := 
do 
   t ← target >>= whnf, 
   match t with 
   | `(_ ↔ (%%te ≤ %%se)) :=
     do 
        rewrite_target_pexpr ``(le_iff_zero_le_sub %%te %%se),
        rhs ← get_rhs, 
        rewrite_target_pexpr ``(eq.symm (add_zero %%rhs))
   -- | `(%%te ↔ %%se) :=
   --   trace "Iff Other : " >> whnf te >>= trace >> whnf se >>= trace
   | _ := trace "Other : " >> print_expr 0 t 
   end

meta def get_vars : expr → tactic (list expr) 
| `(%%te + %%se) := 
  do xes ← get_vars te,
     yes ← get_vars se,
     return (xes ∪ yes)
| `(%%te * %%se) := 
  do xes ← get_vars te,
     yes ← get_vars se,
     return (xes ∪ yes)
| `(- %%te) := get_vars te 
| te := 
  if expr.is_local_constant te 
  then return [te]
  else return []

meta def is_const_term : expr → bool 
| `(%%xe * %%ye) := 
  is_const_term xe && is_const_term ye
| `(- %%xe) := is_const_term xe 
| e := bnot $ expr.is_local_constant e

meta def pull_const_core : expr → tactic unit  
| `(%%xe + %%yze) :=
  if is_const_term xe 
  then pull_const_core yze
  else match yze with 
       | `(%%ye + %%ze) :=
         if is_const_term ye
         then rewrite_target_pexpr ``(add_left_comm %%xe %%ye %%ze)
         else pull_const_core yze
       | _ := failed 
       end
| _ := failed 

meta def pull_consts : tactic unit :=
rep_rhs pull_const_core

meta def shift_const_core : expr → tactic unit  
| `(%%xe + %%yze) :=
  if is_const_term xe 
  then rewrite_target_pexpr ``(iff.symm (@sub_le_iff_le_add' _ _ _ %%xe _))
  else failed
| _ := failed

meta def shift_consts : tactic unit := 
rep_rhs shift_const_core

lemma mul_comm_assoc {α : Type} [comm_semigroup α] : 
  ∀ a b c : α, a * (b * c) = b * (a * c) := sorry

meta def pull_var : expr → tactic unit 
| `(%%xe * %%yze) := 
  if expr.is_local_constant xe 
  then failed
  else match yze with 
       | `(%%ye * %%ze) := 
         if expr.is_local_constant ye 
         then rewrite_target_pexpr ``(mul_comm_assoc %%xe %%ye %%ze)
         else pull_var yze 
       | _ := trace "Invalid input 1" >> failed
       end
| xe := failed 

meta def pull_vars : tactic unit := 
rep_iter_rhs pull_var

meta def term_mul_one : expr → tactic unit 
| `(%%te * 1) := failed
| te := to_expr ``(eq.symm (mul_one %%te))
        >>= rewrite_target

meta def terms_mul_one : tactic unit := 
rep_iter_rhs term_mul_one >> `[simp only [mul_assoc]]

meta def factor_neg_one : expr → tactic unit
| `(%%te * %%se) :=
  factor_neg_one te <|> factor_neg_one se
| `(- 1) := failed 
| `(- %%te) := 
  rewrite_target_pexpr ``(eq.symm (mul_neg_one %%te))
| _ := failed

meta def factor_neg_ones : tactic unit := 
rep_iter_rhs factor_neg_one >> `[simp only [mul_assoc]]

lemma mul_add_mul_add {α : Type} [ring α] (x c d t : α) : 
  (x * c) + (x * d + t) = x * (c + d) + t := sorry 

meta def merge_vars_core : expr → tactic unit  
| `(%%xce + %%ydte) :=
  match xce, ydte with 
  | `(%%xe * %%ce), `(%%yde + %%te) := 
    match yde with 
    | `(%%ye * %%de) := 
      match cmp xe ye with 
      | ordering.lt :=
        -- trace "alpha" >> 
        merge_vars_core ydte  
      | ordering.eq := 
        -- trace "beta" >>
        rewrite_target_pexpr ``(mul_add_mul_add %%xe %%ce %%de %%te)
      | ordering.gt := 
        -- trace "First term : " >>
        -- trace ``(%%xe * %%ce) >>
        -- trace ``(%%ye * %%de) >>
        rewrite_target_pexpr 
          ``(add_left_comm (%%xe * %%ce) (%%ye * %%de) %%te)
        -- >> trace "delta"
      end
    | _ := trace "Invalid input 2" >> failed 
    end
  | `(%%xe * %%ce), `(has_zero.zero _) := failed 
  | te', se := trace "Invalid input 3" >> failed 
  end
| _ := failed

meta def merge_vars_right : tactic unit :=
rep_rhs merge_vars_core

meta def merge_vars_left : tactic unit :=
rep_lhs merge_vars_core

meta def normalize_le : tactic unit :=
do group_right,
   `[simp only 
      [add_assoc, mul_add, add_mul, 
       sub_eq_add_neg, neg_add]],
   pull_consts,
   shift_consts,
   factor_neg_ones,
   terms_mul_one,
   pull_vars,
   merge_vars_right,
   skip

-- example (x y z w : int) : 
--    -w + 1 + 2 * (3 + x) * 5 ≤ 7 + (-2) * y + 55 + x + y * 4 + z := 
-- begin
--   normalize_le,
-- end

lemma not_iff_not' (p q : Prop) : (p ↔ q) → (¬p ↔ ¬q) :=
sorry
 
lemma or_iff_or (p p' q q' : Prop) :
  (p ↔ p') → (q ↔ q') → ((p ∨ q) ↔ (p' ∨ q')) := sorry 

lemma and_iff_and (p p' q q' : Prop) :
  (p ↔ p') → (q ↔ q') → ((p ∧ q) ↔ (p' ∧ q')) := sorry 

-- meta def reduce_app (e : expr) : tactic expr :=
-- match e with 
-- | `(¬ _)      := trace "01" >> return e
-- | `(Exists _) := trace "01" >> return e
-- | `(_ ∨ _)    := trace "01" >> return e
-- | `(_ ≤ _)    := trace "01" >> return e
-- | (expr.app (expr.lam n m d e1) e2) :=
--   trace "02" >> 
--   return (expr.instantiate_var e1 e2) 
-- | (expr.app e1 e2) :=
--   trace "03" >> print_expr 0 e1 >> 
--  --- whnf e1 >>= trace >>
--   return e 
-- | _ := return e
-- end

lemma le_iff_le (x1 x2 y1 y2 : int) : 
  x1 = x2 → y1 = y2 → 
  (x1 ≤ y1 ↔ x2 ≤ y2) := sorry

meta def show_le_iff_le : tactic unit := 
do `(%%x1 ≤ %%y1 ↔ %%x2 ≤ %%y2) ← target, 
   papply ``(le_iff_le %%x1 %%x2 %%y1 %%y2 (eq.refl _) (eq.refl _)),
   skip

meta def normalize_les_core : tactic unit := 
do `(%%pe ↔ %%qe) ← target,
   -- trace "RHS : " >> trace qe, 
   npe ← whnf pe, nqe ← whnf qe,
   -- trace "RHS after reduction : " >> trace nqe,
   match npe, nqe with
   | `(%%pe' → false), `(%%qe' → false) := 
     -- trace "Negation branch" >> 
     papply ``(not_iff_not' %%pe' %%qe' _)
     >> normalize_les_core
   | `(Exists %%pe'), `(Exists %%qe') := 
     -- trace "Exists branch" >> 
     papply ``(ex_iff_ex %%pe' %%qe' _) -- >> rotate 1 
     >> intro_fresh >> normalize_les_core
   | `(%%p1e ∨ %%p2e), `(%%q1e ∨ %%q2e) :=  
     tactic.seq
       (papply ``(or_iff_or %%p1e %%q1e %%p2e %%q2e _ _) >> skip)
       normalize_les_core
   | `(%%p1e ∧ %%p2e), `(%%q1e ∧ %%q2e) :=  
     tactic.seq
       (papply ``(and_iff_and  %%p1e %%q1e %%p2e %%q2e _ _) >> skip)
       normalize_les_core
   | _, _ := 
     do 
        normalize_le,
        merge_vars_left,
        show_le_iff_le -- `[simp]
        -- `(_ ↔ %%qe') ← target,
        -- papply ``(iff.refl %%qe') >> skip
   end 

meta def normalize_les : tactic unit := 
do te ← target,
   nte ← normal_form te, 
   trace nte,
   -- papply ``(@iff.elim_left %%nte %%te _ _),
   -- normalize_les_core,
   skip

meta def normalize_goal := elim_defs >> normalize_les

-- example : ∀ (x y : int), ¬ (2 * x + 1 = 2 * y) :=
-- begin
--   normalize_goal,
-- end

example : ∃ (l : int), ∀ (x : int), 
   x ≥ l → ∃ (u v : int), u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v :=
begin
  normalize_goal,
end