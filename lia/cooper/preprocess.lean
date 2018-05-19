import .correctness ...common.tauto ...common.algebra ...common.int ...common.tactic

open lia tactic

meta instance : has_reflect (fm atom) :=
by mk_has_reflect_instance

meta def get_lhs : tactic expr := 
do `(%%lhs = _) ← target, return lhs 

meta def get_rhs : tactic expr := 
do `(_ = %%rhs) ← target, return rhs 

meta def rep_lhs (t : expr → tactic unit) : tactic unit :=
repeat (get_lhs >>= t)

meta def rep_rhs (t : expr → tactic unit) : tactic unit :=
repeat (get_rhs >>= t)

meta def iter_rhs (t : expr → tactic unit) : expr → tactic unit 
| `(%%xe + %%ye) := 
  t ye <|> iter_rhs xe 
| _ := failed 

meta def rep_iter_rhs (t : expr → tactic unit) : tactic unit :=
repeat (get_rhs >>= iter_rhs t)

meta def elim_defs : tactic unit :=
`[repeat {simp only 
   [imp_iff_not_or, iff_iff_and_or_not_and_not]},
  repeat {simp only 
   [ge, gt, forall_iff_not_exists_not,
    int.lt_iff_add_one_le, le_antisymm_iff]}]

meta def expr_to_coeffs : expr → tactic (int × list int) 
| `(%%t + %%s) := 
  do (i,lcfs) ← expr_to_coeffs t, 
     (j,rcfs) ← expr_to_coeffs s,
     return (i+j, list.comp_add lcfs rcfs)  
| `(%%t - %%s) := 
  do (i,lcfs) ← expr_to_coeffs t, 
     (j,rcfs) ← expr_to_coeffs s,
     return (i-j, list.comp_sub lcfs rcfs)  
| `(%%t * %%s) := 
  do (i,lcfs) ← expr_to_coeffs t, 
     (j,rcfs) ← expr_to_coeffs s,
     if (∀ (c : int), c ∈ lcfs → c = 0)
     then return (i*j, list.map_mul i rcfs)
     else if (∀ (c : int), c ∈ rcfs → c = 0)
          then return (j*i, list.map_mul j lcfs)
          else trace "Nonlinear term" >> failed
| `(- %%t) := 
  do (i,cfs) ← expr_to_coeffs t,
     return (-i, list.map_neg cfs)
| (expr.var n) := return (0, list.update_nth_force [] n 1 0)
| c := 
  do z ← eval_expr int c, 
     return (z, [])

meta def expr_to_fm : expr → tactic (fm atom) 
| `(true) := return ⊤'
| `(false) := return ⊥'
| `(%%te ≤ %%se) :=
  do (i,ks) ← expr_to_coeffs te, 
     (j,ms) ← expr_to_coeffs se,
     return $ A' (atom.le (i - j) (list.comp_sub ms ks))
| `(%%p ∧ %%q) :=
  do pf ← expr_to_fm p, qf ← expr_to_fm q,
     return (pf ∧' qf)
| `(%%p ∨ %%q) :=
  do pf ← expr_to_fm p, qf ← expr_to_fm q,
     return (pf ∨' qf)
| `(¬ %%p) :=
  do pf ← expr_to_fm p, return (¬' pf)
| `(Exists %%(expr.lam _ _ _ p)) :=
  do pf ← expr_to_fm p, return (∃' pf)
| `(Exists (has_le.le %%te)) :=
  do (i,ks) ← expr_to_coeffs te, 
     return $ ∃' (A' (atom.le i (list.comp_sub [1] (0::ks))))
-- | (expr.pi _ _ p q) := 
--   if expr.has_var p
--   then do pf ← expr_to_fm p, 
--           qf ← expr_to_fm q,
--           return ((¬' pf) ∨' qf)
--   else  monad.cond (is_prop p)
--          (do pf ← expr_to_fm p, 
--              qf ← expr_to_fm q,
--              return ((¬' pf) ∨' qf))
--          (do qf ← expr_to_fm q, return (¬' ∃' ¬' qf))
| e := trace "\n Invalid input : " >> trace e >> failed

lemma le_iff_le_of_zero_eq (a b c d : int) :
  (0 = 0 + (b - a) - (d - c)) → (a ≤ b ↔ c ≤ d) := 
begin
  intro h, unfold has_le.le, unfold int.le,
  -- rewrite zero_add at h,
  rewrite eq_sub_iff_add_eq at h,
  simp only [zero_add] at h, rewrite h
end

meta def pull_add_up :=   
`[simp only 
   [add_assoc', mul_add, add_mul,
    sub_eq_add_neg, neg_add]]

meta def pull_const_right : expr → tactic unit  
| `(%%xye + %%ze) :=
  if expr.has_local ze 
  then match xye with 
       | `(%%xe + %%ye) :=
         if expr.has_local ye
         then pull_const_right xye
         else rewrite_target_pexpr ``(add_right_comm %%xe %%ye %%ze)
       | _ := failed 
       end
  else pull_const_right xye
| _ := failed 

meta def pull_consts_right : tactic unit :=
rep_rhs pull_const_right

meta def shift_const : expr → tactic unit  
| `(%%xe + %%ye) :=
  -- trace "Enter shift_const : " >> trace xe >> trace ye >> 
  if expr.has_local ye 
  then failed
  else 
       papply ``(@eq_add_of_sub_eq _ _ _ %%xe %%ye) 
       >> skip
| _ := failed

meta def shift_consts : tactic unit := 
rep_rhs shift_const

meta def elim_consts := 
   pull_consts_right >> 
   shift_consts

meta def factor_neg_one : expr → tactic unit
| `(%%te * %%se) :=
  factor_neg_one te <|> factor_neg_one se
| `(- 1) := failed 
| `(- %%te) := 
  rewrite_target_pexpr ``(eq.symm (neg_one_mul %%te))
| _ := failed

meta def factor_neg_ones : tactic unit := 
rep_iter_rhs factor_neg_one >> `[simp only [mul_assoc']]

meta def term_one_mul : expr → tactic unit 
| `(1 * %%te) := failed
| te := to_expr ``(eq.symm (one_mul %%te))
        >>= rewrite_target

meta def terms_one_mul : tactic unit := 
rep_iter_rhs term_one_mul >>
 `[simp only [mul_assoc']] >>
skip

meta def pull_var : expr → tactic unit 
| `(%%xye * %%ze) := 
  -- trace "Pull_var left term : " >> trace xye >>
  -- trace "Pull_var right term : " >> trace ze >>
  if expr.is_local_constant ze 
  then failed
  else 
       match xye with 
       | `(%%xe * %%ye) := 
         if expr.is_local_constant ye 
         then rewrite_target_pexpr ``(mul_comm_assoc %%xe %%ye %%ze)
         else pull_var xye
       | e := trace "Invalid input 1 : " >> trace e >> failed
       end
| xe := failed 

meta def pull_vars : tactic unit := 
rep_iter_rhs pull_var

meta def factor_terms_core : expr → tactic unit  
| `(%%tcxe + %%dye) :=
  match tcxe, dye with 
  | `(%%te + %%cxe), `(%%de * %%ye) := 
    match cxe with 
    | `(%%ce * %%xe) := 
      match cmp xe ye with 
      | ordering.lt :=
        factor_terms_core tcxe  
      | ordering.eq :=
        rewrite_target_pexpr ``(mul_add_mul_add %%te %%ce %%xe %%de)
      | ordering.gt :=
        rewrite_target_pexpr 
          ``(add_right_comm %%te %%cxe %%dye)
      end
    | _ := trace "Invalid input 2" >> failed 
    end
  | `(has_zero.zero _), _ := failed 
  | _, _ := trace "Invalid input 3 : " >> 
            trace tcxe >> trace dye >>
            failed 
  end
| _ := failed

lemma elim_zero_coeff (t s c x : int) : 
  c = 0 → t = s → t = s + (c * x)  :=
begin intro h, rewrite h, simp, end

meta def cancel_term : expr → tactic unit  
| `(%%se + (%%ce * %%xe)) :=
  -- trace "Before cancel_term : " >>  
  papply ``(elim_zero_coeff _ %%se %%ce %%xe (eq.refl _) _) >> 
  -- trace "Success"
    skip
| _ := failed

meta def factor_terms : tactic unit :=
rep_rhs factor_terms_core

meta def cancel_terms : tactic unit :=
rep_rhs cancel_term

meta def elim_vars := 
do factor_neg_ones,
   terms_one_mul,
   -- trace "Calling pull_vars", target >>= trace,
   pull_vars,
   -- trace "Finished pull_vars", target >>= trace,
   factor_terms,
   -- trace "After factor_terms", target >>= trace,
   cancel_terms,
   -- trace "After cancel_terms", target >>= trace,
   skip

meta def simp_dot_prod := 
`[simp [list.dot_prod, list.map, list.zip_pad]] 

lemma eq_of_eq_zero_add (x y : int) :
  x = 0 + y → x = y := by simp 

meta def normalize_le : tactic unit :=
do papply ``(le_iff_le_of_zero_eq),
   simp_dot_prod,
   papply ``(eq_of_eq_zero_add),
   pull_add_up
   
meta def show_le_iff_le : tactic unit := 
do normalize_le, elim_consts, elim_vars,
   papply ``(eq.refl _), skip

meta def show_iff (show_atom : tactic unit) : tactic unit := 
do `(%%pe ↔ %%qe) ← target,
   npe ← whnf pe, nqe ← whnf qe,
   match npe, nqe with
   | `(%%pe' → false), `(%%qe' → false) := 
     papply ``(@not_iff_not_of_iff %%pe' %%qe' _)
     >> show_iff
   | `(Exists %%pe'), `(Exists %%qe') := 
     papply ``(ex_iff_ex %%pe' %%qe' _) 
     >> intro_fresh >> show_iff
   | `(%%p1e ∨ %%p2e), `(%%q1e ∨ %%q2e) :=  
     tactic.seq
       (papply ``(or_iff_or %%p1e %%q1e %%p2e %%q2e _ _) >> skip)
       show_iff
   | `(%%p1e ∧ %%p2e), `(%%q1e ∧ %%q2e) :=  
     tactic.seq
       (papply ``(and_iff_and  %%p1e %%q1e %%p2e %%q2e _ _) >> skip)
       show_iff
   | _, _ := 
     -- trace "Calling show_atom : " >>
     -- target >>= trace >> 
     show_atom
   end 

meta def reflect_goal : tactic unit := 
do elim_defs,
   te ← target,
   fe ← expr_to_fm te,
   papply ``(@iff.elim_left (@I atom int _ %%`(fe) []) %%te _ _),
   show_iff show_le_iff_le