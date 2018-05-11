import .preprocess

open lia tactic

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

def of_as_false_dvd {x y : int} (h : as_false (has_dvd.dvd x y)) : ¬(has_dvd.dvd x y) :=
match (int.decidable_dvd x y), h with
| (is_true h_c),  h := false.elim h
| (is_false h_c), h := h_c 
end

meta def dec_triv_tac : tactic unit :=
do t ← target, 
   to_expr ``(@of_as_true %%t) >>= apply,
   triv

meta def show_le : tactic unit :=
papply ``(of_as_true_le) >> triv

meta def show_dvd : tactic unit :=
papply ``(of_as_true_dvd) >> triv

meta def show_ndvd : tactic unit :=
papply ``(of_as_false_dvd) >> triv

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

lemma  not_or_of_not_and_not {a b : Prop} (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
iff.elim_right not_or_distrib h

meta def show_fm : fm atom → tactic unit 
| ⊤' := triv
| ⊥' := failed
| (p ∧' q) := 
  do papply ``(and.intro), 
     show_fm p, show_fm q 
| (p ∨' q) := 
  (papply ``(or.inl) >> show_fm p)
  <|> (papply ``(or.inr) >> show_fm q)
| (A' (atom.le _ _)) := triv
| (A' (atom.dvd _ _ _)) := show_dvd
| (A' (atom.ndvd _ _ _)) := show_ndvd
| (¬' ⊤') := failed 
| (¬' ⊥') := papply ``(not_false) >> skip
| ¬'(p ∧' q) := 
  do papply ``(not_and_of_not_or_not),
     show_fm  (¬'p ∨' ¬'q)  
| ¬'(p ∨' q) := 
  do papply ``(not_or_of_not_and_not),
     show_fm  (¬'p ∧' ¬'q)  
| (¬'(A' (atom.le _ _))) := 
  papply ``(not_false) >> skip
| (¬'(A' (atom.dvd _ _ _))) := show_ndvd
| (¬'(A' (atom.ndvd _ _ _))) := 
  papply ``(not_not_intro) >> show_dvd
| (¬' ¬' p) := papply ``(not_not_intro) >> show_fm p
| _ := trace "Invalid input : remaining quantifier" >> failed

meta def dec_fm_core : fm atom → tactic bool
| ⊤' := return true
| ⊥' := return false
| (A' (atom.le i [])) := 
  match int.decidable_le i 0 with 
  | (is_true _) := return true
  | (is_false _) := return false
  end
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
     --trace "Result of evalulating ", 
     --trace (p ∧' q), trace " : ", trace (bp && bq),
     return $ bp && bq
| (p ∨' q) := 
  do bp ← dec_fm_core p,
     bq ← dec_fm_core q, 
     --trace "Result of evalulating ", 
     --trace (p ∨' q), trace " : ", trace (bp || bq),
     return $ bp || bq
| (¬' p) := 
  do bp ← dec_fm_core p, 
     --trace "Result of evalulating ", 
     --trace (¬' p), trace " : ", trace (bnot bp),
     return (bnot bp)
| (∃' p) := trace "Remaining quantifiers" >> failed
 
meta def dec_fm (p : fm atom) : tactic unit := 
monad.cond (dec_fm_core p) admit failed

meta def trace_fm:=
do `(I %%fe' []) ← target,
   eval_expr (fm atom) fe' >>= trace

meta def cooper : tactic unit :=
do reflect_goal, 
   `(I %%fe []) ← target,
   papply ``((qe_cooper_prsv %%fe _ _).elim_left),
   `(I %%fe' []) ← target,
   eval_expr (fm atom) fe' >>= show_fm,
   dec_triv_tac,
   skip

meta def cooper_vm : tactic unit :=
do reflect_goal, 
   `(I %%fe []) ← target,
   papply ``((qe_cooper_prsv %%fe _ _).elim_left),
   `(I %%fe' []) ← target,
   eval_expr (fm atom) fe' >>= dec_fm,
   dec_triv_tac,
   skip