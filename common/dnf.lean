import .atom

variables {α β : Type}

/-
Requires : nqfree arg-0
-/
def dnf : fm α → list (list α) 
| (fm.true α) := [[]]
| (fm.false α) := []
| (fm.atom a) := [[a]]
| (fm.and p q) := list.map append_pair $ list.product (dnf p) (dnf q)
| (fm.or p q) := dnf p ++ dnf q 
| _ := []

lemma dnf_prsv [atom_type α β] {p : fm α} {H : nqfree p} {bs : list β} : 
  some_true (list.map (allp (atom_type.val bs)) (dnf p)) ↔ I p bs := sorry
-- iff.trans (by rewrite some_true_iff_disj_list) (dnf_prsv _ H _)

#exit
lemma dnf_prsv [atom_type α β] : ∀ (p : fm α) (H : nqfree p) (xs : list β), 
  disj_list (list.map (λ (as : list α), allp (atom_type.val xs) as) (dnf p)) ↔ I p xs 
| (fm.true α) H bs := 
  by {unfold dnf, simp, unfold disj_list, 
      rewrite exp_allp_nil, rewrite true_or,
      unfold I, unfold interp}
| (fm.false α) H bs := 
  by {unfold dnf, simp, unfold disj_list, rewrite exp_I_bot }
| (fm.atom a) H bs := 
  begin
    unfold dnf, simp, unfold disj_list, simp, 
    apply iff.intro, intro Ha, apply Ha, 
    apply or.inl rfl, intros Ha a' Ha', 
    rewrite exp_mem_singleton at Ha', subst Ha',
    apply Ha
  end
| (fm.and p q) H bs := 
  begin
    unfold dnf, rewrite map_compose, rewrite exp_I_and, 
    rewrite (iff.symm (dnf_prsv p H^.elim_left bs)),
    rewrite (iff.symm (dnf_prsv q H^.elim_right bs)),
    repeat {rewrite disj_list_iff_some_true},
    repeat {unfold some_true},

    apply iff.intro,
    intro H0, cases H0 with r Hr, 
    have Hrl := Hr^.elim_left,
    have Hrr := Hr^.elim_right, clear Hr, 
    cases (ex_arg_of_mem_map Hrl) with d Hd,
    simp at Hd, 
    apply and.intro, 
         
    existsi (∀ (a : α), a ∈ (prod.fst d) → atom_type.val a bs),
    apply and.intro, apply mem_map_of_mem,
    apply fst_mem_of_mem_product Hd^.elim_right,
    intros a Ha, rewrite Hd^.elim_left at Hrr,
    apply Hrr, cases d with dl dr, unfold append_pair,
    apply mem_append_of_mem_or_mem,
    apply or.inl Ha, 

    existsi (∀ (a : α), a ∈ (prod.snd d) → atom_type.val a bs),
    apply and.intro, apply mem_map_of_mem, 
    apply snd_mem_of_mem_product Hd^.elim_right,
    intros a Ha, rewrite Hd^.elim_left at Hrr,
    apply Hrr, cases d with dl dr, unfold append_pair,
    apply mem_append_of_mem_or_mem,
    apply or.inr Ha, 

    intro H0, 
    cases (H0^.elim_left) with r Hr,
    cases (H0^.elim_right) with s Hs, clear H0, 
    cases (ex_arg_of_mem_map Hr^.elim_left) with ll Hll,
    cases (ex_arg_of_mem_map Hs^.elim_left) with lr Hlr,
    existsi (∀ (a : α), a ∈ append_pair (ll,lr) → atom_type.val a bs),
    apply and.intro, apply mem_map_of_mem, 
    apply mem_product_of_mem_of_mem,
    apply Hll^.elim_left, apply Hlr^.elim_left,
    intros a Ha, 
    cases (mem_or_mem_of_mem_append Ha) with HM HM,
    rewrite Hll^.elim_right at Hr,
    apply Hr^.elim_right _ HM, 
    rewrite Hlr^.elim_right at Hs,
    apply Hs^.elim_right _ HM 
  end
| (fm.or p q) H bs := 
  begin
    unfold dnf, rewrite map_dist_append, 
    rewrite disj_list_dist_append,
    rewrite dnf_prsv, rewrite dnf_prsv,
    rewrite exp_I_or, apply H^.elim_right,
    apply H^.elim_left
  end
| (fm.not p) H bs := by cases H
| (fm.ex p) H bs := by cases H
