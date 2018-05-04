import .preprocess

open lia tactic



meta instance : has_reflect (fm atom) :=
by mk_has_reflect_instance

meta def to_lhs (ze : expr) : tactic int := 
eval_expr int ze 

meta def to_rhs : expr → tactic (list int) 
| `((%%ce * %%(expr.var n)) + %%se) := 
  do zs ← to_rhs se, 
     z ← eval_expr int ce, 
     return $ list.update_nth_force zs n z 0
| `(%%ce * %%(expr.var n)) := 
  do z ← eval_expr int ce, 
     return $ list.update_nth_force [] n z 0
| (expr.var n) := return (list.update_nth_force [] n 1 0)
| `(- %%(expr.var n)) := return (list.update_nth_force [] n (-1) 0)
| _ := trace "Invalid RHS" >> failed

meta def rhs_to_coeffs : expr → tactic (list int) 
| `((%%(expr.var n) * %%ze) + %%te) := 
  do zs ← rhs_to_coeffs te, 
     z ← eval_expr int ze, 
     return $ list.update_nth_force zs n z 0
| `(@has_zero.zero int _) := return []
| _ := trace "Invalid RHS" >> failed

meta def to_fm : expr → tactic (fm atom) 
| `(true) := return ⊤'
| `(false) := return ⊥'
| `(%%ze ≤ %%te) :=
  do z ← eval_expr int ze, 
     zs ← rhs_to_coeffs te,
     return $ A' (atom.le z zs)
| `(%%p ∧ %%q) :=
  do pf ← to_fm p, qf ← to_fm q,
     return (pf ∧' qf)
| `(%%p ∨ %%q) :=
  do pf ← to_fm p, qf ← to_fm q,
     return (pf ∨' qf)
| `(¬ %%p) :=
  do pf ← to_fm p, return (¬' pf)
| `(Exists %%(expr.lam _ _ _ p)) :=
  do pf ← to_fm p, return (∃' pf)
-- | (expr.pi _ _ p q) := 
--   if expr.has_var p
--   then do pf ← to_fm p, 
--           qf ← to_fm q,
--           return ((¬' pf) ∨' qf)
--   else  monad.cond (is_prop p)
--          (do pf ← to_fm p, 
--              qf ← to_fm q,
--              return ((¬' pf) ∨' qf))
--          (do qf ← to_fm q, return (¬' ∃' ¬' qf))
| e := trace e >> trace "\n Invalid input" >> failed

#check @iff.elim_left
--lemma of_of_I (f : fm atom) {q} : ((I f (@list.nil int)) ↔ q) → (I f (@list.nil int)) → q := id

meta def cooper : tactic unit :=
do normalize_goal,
   fe ← target >>= to_fm,
   papply ``(@iff.elim_left (@I atom int _ %%`(fe) []) _ _ _), 
   -- intro_fresh,
   -- trace "Before show_iff : ",
   -- trace_state, 
   show_iff (target >>= trace),
   --rewrite_target_pexpr ``(add_zero),
   -- unfold_I, 
   -- prove_ex_iff_ex,
   -- rewrite_cooper, 
   skip


#exit

meta def fm_to_expr (p : fm atom) : expr := 
reflected.to_expr `(p)


instance : decidable_eq (fm atom) :=
by mk_dec_eq_instance

def of_as_true_le {x y : int} (h₂ : as_true (has_le.le x y)) : (has_le.le x y) :=
match (int.decidable_le x y), h₂ with
| (is_true h_c),  h₂ := h_c
| (is_false h_c), h₂ := false.elim h₂
end

def of_as_true_dvd {x y : int} (h₂ : as_true (has_dvd.dvd x y)) : (has_dvd.dvd x y) :=
match (int.decidable_dvd x y), h₂ with
| (is_true h_c),  h₂ := h_c
| (is_false h_c), h₂ := false.elim h₂
end

meta def dec_triv_tac : tactic unit :=
do t ← target, 
   to_expr ``(@of_as_true %%t) >>= apply,
   triv
   
meta def show_le : tactic unit :=
papply ``(of_as_true_le) >> triv

meta def show_dvd : tactic unit :=
papply ``(of_as_true_dvd) >> triv

meta def unfold_I :=
`[simp only [I, interp, atom_type.val, lia.val,
             list.dot_prod, list.map, list.zip_pad,
             list.sum_exp, list.foldl, int.one_mul,
             int.neg_one_mul, int.zero_add,
             int.zero_mul, int.mul_zero]]

meta def rewrite_ite_eq_of :=
`[rewrite ite_eq_of,
  swap_goals, dec_triv_tac]
  
meta def rewrite_ite_eq_of_not :=
`[rewrite ite_eq_of_not,
  swap_goals, dec_triv_tac]

meta def rewrite_filter_map_cons_none := 
`[rewrite list.filter_map_cons_none,
  swap_goals, refl]

meta def rewrite_filter_map_cons_some := 
`[rewrite list.filter_map_cons_some,
  swap_goals, refl]

meta def prove_ex_iff_ex :=
`[repeat {apply ex_iff_ex, intro x}, simp, refl]

#check qe_cooper_prsv
meta def rewrite_cooper :=
`[rewrite iff.symm (qe_cooper_prsv _ _ _)]

meta def simp_cooper : tactic unit := sorry

meta def eval_cooper :=
`[repeat {simp_cooper 
      <|> rewrite_ite_eq_of
      <|> rewrite_ite_eq_of_not}]

meta def show_triv : tactic unit :=
 --  (seq (papply ``(and.intro) >> skip) show_triv)
 -- -- <|>  (`[simp] >> show_triv)
 --  <|> show_dvd
 --  <|> show_le
  `[repeat {apply (and.intro) 
            <|> simp 
            <|> show_dvd
            <|> show_le}]

meta def foo : tactic unit := 
(seq 
  (papply ``(and.intro) >> skip) 
  (trace_state >> foo))
<|> (papply ``(or.inl) >> foo)
<|> (papply ``(or.inr) >> foo)
<|> (`[simp] >> foo)
<|> show_dvd
<|> show_le


meta def dec_fm_core : fm atom → tactic bool
| ⊤' := return true
| ⊥' := return false
| (A' (atom.le 0 [])) := return true
| (A' (atom.le i [])) := return false
| (A' (atom.le _ (k::ks))) := 
  trace "Remaining free variables : le atom" >> failed
| (A' (atom.dvd d i [])) :=
  -- trace "Deciding : " >> trace d >> trace " | " >> trace i >>  
  match int.decidable_dvd d i with 
  | (is_true _) := return true
  | (is_false _) := return false
  end
| (A' (atom.dvd _ _ (k::ks))) := 
  trace "Remaining free variables : dvd atom " >> failed
| (A' (atom.ndvd d i [])) := 
  match int.decidable_dvd d i with 
  | (is_true _) := return false
  | (is_false _) := return true
  end
| (A' (atom.ndvd d i (k::ks))) := 
  -- trace "Coeffs : " >> trace (k::ks) >>
  trace "Remaining free variables : ndvd atom" >> failed
| (p ∧' q) := 
  do bp ← dec_fm_core p,
     bq ← dec_fm_core q, 
     return $ bp && bq
| (p ∨' q) := 
  do bp ← dec_fm_core p,
     bq ← dec_fm_core q, 
     return $ bp || bq
| (¬' p) := 
  do bp ← dec_fm_core p, return (bnot bp)
| (∃' p) := trace "Remaining quantifiers" >> failed
 
meta def dec_fm (p : fm atom) : tactic unit := 
monad.cond (dec_fm_core p) admit failed


#exit


meta def cooper' : tactic unit :=
do `[try {simp only [imp_iff_not_or, iff_iff_and_or_not_and_not, ge, gt]}],
   ge ← target, 
   -- trace "Formula before QE : ",
   f ← to_fm ge, 
   -- trace f, trace "\n", 
   -- trace "Formula after QE : ",
   -- trace $ qe_cooper f, trace "\n", 
   dec_fm $ qe_cooper f

meta def bar (xe ye : expr) : tactic unit :=
do x ← eval_expr int xe, 
   y ← eval_expr int ye, 
   let z := x * y in
   do hn ← mk_fresh_name,
      he ← to_expr ``(%%xe * %%ye = %%`(z)) >>= assert hn, 
      papply ``(eq.refl _),
      rewrite_target he,
      skip

lemma add_assoc' {α : Type} [add_semigroup α] {a b c : α} : 
  a + (b + c) = a + b + c :=
by rewrite add_assoc a b c

#exit


example : ∃ (x y : int), 0 ≤ 1 * x + 2 * y :=
begin 
  cooper, 
  repeat {
        rewrite_ite_eq_of
    <|> rewrite_ite_eq_of_not
    <|> rewrite_filter_map_cons_none
    <|> rewrite_filter_map_cons_some
    <|> `[simp 
           [
             int.of_nat_eq_coe, 
             I, interp, atom_type.val, 
             lia.val, qe_cooper,
             lift_nnf_qe, sqe_cooper, nnf,
             hd_coeffs_one, coeffs_lcm,
             hd_coeff, atoms_dep0, atoms,
             atom_type.dep0, list.filter,
             lia.dep0, list.head_dft,
             int.lcms, int.lcm, nat.lcm,
             map_fm, hd_coeff_one,
             qe_cooper_one, divisor,
             list.irange, list.range,
             list.range_core,
             inf_minus,
             
             disj, list_disj, map_neg,
             list.map, int.nat_abs, has_add.add,
int.add,
             -- has_neg.neg, int.neg, lia.subst,
             -- int.neg_succ_of_nat_coe, 
             list.comp_add, --function.comp,
             list.zip_pad, or_o, and_o, 
             lia.subst,
             lia.asubst
           ]             
         ]
  },
end

#exit



example : ∃ (x : int), 0 ≤ x ∧ 0 ≤ -x :=
begin
  have h : (∃ (x : int), 0 ≤ x ∧ 0 ≤ -x ) ↔ 
           I (∃' (A' atom.le 0 [1] ∧' A' atom.le 0 [-1])) (@list.nil int),
 rewrite h,
  rewrite iff.symm (qe_cooper_prsv _ _ _), 
  --simp,
  apply and.intro, apply one_dvd,
  apply and.intro; simp; apply le_refl,
  dec_triv_tac,
   
end