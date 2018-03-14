import .atom

variables {α β : Type}

open atom_type

/-
Requires : nqfree arg-0
-/
def dnf : fm α → list (list α) 
| (fm.true α) := [[]]
| (fm.false α) := []
| (fm.atom a) := [[a]]
| (fm.and p q) := list.map append_pair $ list.product (dnf p) (dnf q)
| (fm.or p q) := dnf p ++ dnf q 
| (fm.ex _) := []
| (fm.not _) := []

lemma dnf_prsv_normal [atom_type α β] : ∀ (p : fm α), 
  fnormal β p → allp (allp (normal β)) (dnf p) 
| (fm.true α) hnm := 
  begin
    intros as has, unfold dnf at has,
    rewrite exp_mem_singleton at has, subst has,
    apply allp_nil
  end
| (fm.false α) hnm := allp_nil
| (fm.atom a) hnm := 
  begin
    intros as has, unfold dnf at has,
    rewrite exp_mem_singleton at has, 
    subst has, intros a' ha', 
    rewrite exp_mem_singleton at ha',
    subst ha', apply hnm,
  end
| (fm.and p q) hnm := 
  begin
    unfold fnormal at hnm, cases hnm with hnmp hnmq,
    unfold dnf, intros as has, intros a ha,
    rewrite exp_mem_map at has, 
    cases has with asp hasp, 
    cases hasp with hasp1 hasp2,
    cases asp with as1 as2, subst hasp2, 
    cases (mem_or_mem_of_mem_append ha) with hm hm,
    apply dnf_prsv_normal p hnmp as1, 
    apply fst_mem_of_mem_product hasp1, apply hm,  
    apply dnf_prsv_normal q hnmq as2, 
    apply snd_mem_of_mem_product hasp1, apply hm
  end
| (fm.or p q) hnm := 
  begin
    unfold fnormal at hnm, cases hnm with hnmp hnmq,
    unfold dnf, intros as has, intros a ha,
    cases (mem_or_mem_of_mem_append has) with hm hm,
    apply dnf_prsv_normal p hnmp as hm a ha, 
    apply dnf_prsv_normal q hnmq as hm a ha 
  end
| (fm.not _) hnm := allp_nil
| (fm.ex _) hnm := allp_nil

lemma dnf_prsv_alt [atom_type α β] : ∀ {p : fm α} {H : nqfree p} {xs : list β}, 
  disj_list (list.map (allp (atom_type.val xs)) (dnf p)) ↔ I p xs 
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
    rewrite iff.symm (@dnf_prsv_alt p _ bs),
    rewrite iff.symm (@dnf_prsv_alt q _ bs),
    repeat {rewrite disj_list_iff_some_true},
    repeat {unfold some_true},

    apply iff.intro,
    intro H0, cases H0 with r Hr, 
    have Hrl := Hr^.elim_left,
    have Hrr := Hr^.elim_right, clear Hr, 
    cases (ex_arg_of_mem_map Hrl) with d Hd,
    simp at Hd, 
    apply and.intro, 
         
    existsi (∀ (a : α), a ∈ (prod.fst d) → atom_type.val bs a),
    apply and.intro, apply mem_map_of_mem,
    apply fst_mem_of_mem_product Hd^.elim_right,
    intros a Ha, rewrite Hd^.elim_left at Hrr,
    apply Hrr, cases d with dl dr, unfold append_pair,
    apply mem_append_of_mem_or_mem,
    apply or.inl Ha, 

    existsi (∀ (a : α), a ∈ (prod.snd d) → atom_type.val bs a),
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
    existsi (∀ (a : α), a ∈ append_pair (ll,lr) → atom_type.val bs a),
    apply and.intro, apply mem_map_of_mem, 
    apply mem_product_of_mem_of_mem,
    apply Hll^.elim_left, apply Hlr^.elim_left,
    intros a Ha, 
    cases (mem_or_mem_of_mem_append Ha) with HM HM,
    rewrite Hll^.elim_right at Hr,
    apply Hr^.elim_right _ HM, 
    rewrite Hlr^.elim_right at Hs,
    apply Hs^.elim_right _ HM,
    apply H^.elim_right, apply H^.elim_left
  end
| (fm.or p q) H bs := 
  begin
    unfold dnf, rewrite map_dist_append, 
    rewrite disj_list_dist_append,
    rewrite dnf_prsv_alt, rewrite dnf_prsv_alt,
    rewrite exp_I_or, apply H^.elim_right,
    apply H^.elim_left
  end
| (fm.not p) H bs := by cases H
| (fm.ex p) H bs := by cases H

lemma dnf_prsv [atom_type α β] {p : fm α} {H : nqfree p} {bs : list β} : 
  some_true (list.map (allp (atom_type.val bs)) (dnf p)) ↔ I p bs := 
iff.trans (by rewrite some_true_iff_disj_list) (@dnf_prsv_alt _ _ _ _ H _)
