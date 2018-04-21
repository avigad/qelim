import .correctness

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

meta def to_coeffs : expr → tactic (int × list int) 
| `(%%t + %%s) := 
  do (i,lcfs) ← to_coeffs t, 
     (j,rcfs) ← to_coeffs s,
     return (i+j, list.comp_add lcfs rcfs)  
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

meta def to_fm : expr → tactic (fm atom) 
| `(true) := return ⊤'
| `(false) := return ⊥'
| `(%%t ≤ %%s) :=
  do (i,lcfs) ← to_coeffs t, 
     (j,rcfs) ← to_coeffs s,
     return $ A' (atom.le (i - j) (list.comp_sub rcfs lcfs))
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
| (expr.pi _ _ p q) := 
  monad.cond (is_prop p)
    (do pf ← to_fm p, 
        qf ← to_fm q,
        return ((¬' pf) ∨' qf))
    (do qf ← to_fm q, return (¬' ∃' ¬' qf))

| _ := trace "Invalid input" >> failed

meta def fm_to_expr (p : fm atom) : expr := 
reflected.to_expr `(p)

def f0 := (∃' (A' atom.le 0 [1] ∧' A' atom.le 0 [-1]))

lemma of_I_iff (f : fm atom) {q} : ((I f (@list.nil int)) ↔ q) → (I f (@list.nil int)) → q :=
λ h, h^.elim_left

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

meta def cooper : tactic unit :=
do ge ← target, 
   f ← to_fm ge,
   papply ``(of_I_iff %%`(f)), 
   unfold_I, 
   prove_ex_iff_ex,
   rewrite_cooper, 
   skip

meta def dec_fm_core : fm atom → tactic unit 
| ⊤' := skip
| ⊥' := failed
| (A' (atom.le 0 [])) := skip
| (A' (atom.le i [])) := failed
| (A' (atom.le _ (k::ks))) := trace "Remaining free variables" >> failed
| (A' (atom.dvd d i [])) := 
  match int.decidable_dvd d i with 
  | (is_true _) := skip
  | (is_false _) := failed
  end
| (A' (atom.dvd _ _ (k::ks))) := trace "Remaining free variables" >> failed
| (A' (atom.ndvd d i [])) := 
  match int.decidable_dvd d i with 
  | (is_true _) := failed
  | (is_false _) := skip
  end
| (A' (atom.ndvd _ _ (k::ks))) := trace "Remaining free variables" >> failed
| (p ∧' q) := dec_fm_core p >> dec_fm_core q 
| (p ∨' q) := dec_fm_core p <|> dec_fm_core q
| (¬' p) := trace "Remaining negations" >> failed
| (∃' p) := trace "Remaining quantifiers" >> failed
 
meta def dec_fm (p : fm atom) : tactic unit := 
dec_fm_core p >> admit 

meta def cooper' : tactic unit :=
do ge ← target, 
   f ← to_fm ge,
   -- trace $ qe_cooper f,
   dec_fm $ qe_cooper f

lemma forall_iff_not_exists_not {α : Type} {p : α → Prop}
[∀ (x : α), decidable (p x)] :
  (∀ (x : α), p x) ↔ (¬ ∃ x, ¬ p x) :=
by simp

example : ∃ (x y z : int), y + z ≤ (2 * 5) * (x) := 
begin
  cooper',
end

#exit

example : ∃ (x : int), 5 ≤ x ∨ 5 ≤ -x :=
begin
  cooper'
end

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