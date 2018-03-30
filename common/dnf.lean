import .atom

variables {α β : Type}

open atom_type list

/-
Requires : nqfree arg-0
-/
def dnf : fm α → list (list α) 
| (fm.true α) := [[]]
| (fm.false α) := []
| (fm.atom a) := [[a]]
| (fm.and p q) := list.map list.append_pair $ list.product (dnf p) (dnf q)
| (fm.or p q) := dnf p ++ dnf q 
| (fm.ex _) := []
| (fm.not _) := []

lemma dnf_prsv_pred [atom_type α β] (pr : α → Prop) : 
  ∀ (φ : fm α), list.allp pr (@atoms _ (atom_type.dec_eq _ β) φ) → list.allp (list.allp pr) (dnf φ) 
| (fm.true α) hnm := 
  begin
    intros as has, unfold dnf at has, simp,
    rewrite list.mem_singleton at has, subst has,
    apply list.forall_mem_nil
  end
| (fm.false α) hnm := 
  begin simp, unfold dnf, intros a ha, cases ha end
| (fm.atom a) hnm := 
  begin
    intros as has, unfold dnf at has,
    rewrite mem_singleton at has, 
    subst has, intros a' ha', 
    rewrite mem_singleton at ha',
    subst ha', apply hnm, apply or.inl rfl
  end
| (fm.and p q) hnm := 
  begin 
    unfold atoms at hnm, 
    rewrite allp_iff_forall_mem at hnm,
    rewrite forall_mem_union at hnm,
    cases hnm with hnmp hnmq,
    unfold dnf, intros as has, intros a ha,
    rewrite mem_map at has, 
    cases has with asp hasp, 
    cases hasp with hasp1 hasp2,
    cases asp with as1 as2, subst hasp2, 
    cases (mem_or_mem_of_mem_append ha) with hm hm,
    apply dnf_prsv_pred p hnmp as1,  
    apply fst_mem_of_mem_product hasp1, apply hm,  
    apply dnf_prsv_pred q hnmq as2, 
    apply snd_mem_of_mem_product hasp1, apply hm
  end
| (fm.or p q) hnm := 
  begin
    unfold atoms at hnm, 
    rewrite allp_iff_forall_mem at hnm,
    rewrite forall_mem_union at hnm,
    cases hnm with hnmp hnmq,
    unfold dnf, intros as has, intros a ha,
    cases (mem_or_mem_of_mem_append has) with hm hm,
    apply dnf_prsv_pred p hnmp as hm a ha, 
    apply dnf_prsv_pred q hnmq as hm a ha 
  end
| (fm.not _) hnm := 
  begin
    rewrite allp_iff_forall_mem, 
    unfold dnf, apply @forall_mem_nil _ (allp pr),
  end
| (fm.ex _) hnm := 
  begin
    rewrite allp_iff_forall_mem, 
    unfold dnf, apply @forall_mem_nil _ (allp pr),
  end
  
lemma dnf_prsv_normal [atom_type α β] : ∀ (p : fm α), 
  fnormal β p → list.allp (list.allp (normal β)) (dnf p) := 
begin
  intros p hp, rewrite fnormal_iff_fnormal_alt at hp,
  apply dnf_prsv_pred (normal β) _ hp, 
end

#check @mem_map_of_mem
lemma dnf_prsv_alt [atom_type α β] : ∀ {p : fm α} {H : nqfree p} {xs : list β}, 
  list.disj_list (list.map (allp (atom_type.val xs)) (dnf p)) ↔ I p xs 
| (fm.true α) H bs := 
  by {unfold dnf, simp, unfold disj_list, 
      rewrite true_or, unfold I, unfold interp}
| (fm.false α) H bs := 
  by {unfold dnf, simp, unfold disj_list, rewrite exp_I_bot }
| (fm.atom a) H bs := 
  begin
    unfold dnf, simp, unfold disj_list, simp, 
    apply iff.intro, intro Ha, apply Ha, 
    unfold I, unfold interp, apply id
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
    cases (list.exists_of_mem_map Hrl) with d Hd,
    simp at Hd, 
    apply and.intro, 
         
    existsi (∀ (a : α), a ∈ (prod.fst d) → atom_type.val bs a),
    cases Hd with hd1 hd2,
    apply and.intro, 
    rewrite iff.symm (allp_iff_forall_mem (val bs) d.fst), 
    apply mem_map_of_mem,
    
    apply fst_mem_of_mem_product, apply hd1,
    intros a Ha, subst hd2,
    apply Hrr, cases d with dl dr, unfold append_pair,
    apply mem_append_of_mem_or_mem,
    apply or.inl Ha, 

    existsi (∀ (a : α), a ∈ (prod.snd d) → atom_type.val bs a),
    cases Hd with hd1 hd2,
    apply and.intro, 
    rewrite iff.symm (allp_iff_forall_mem (val bs) d.snd), 
    apply mem_map_of_mem, 
    apply snd_mem_of_mem_product hd1,
    intros a Ha, subst hd2,
    apply Hrr, cases d with dl dr, unfold append_pair,
    apply mem_append_of_mem_or_mem,
    apply or.inr Ha, 

    intro H0, 
    cases (H0^.elim_left) with r Hr,
    cases (H0^.elim_right) with s Hs, clear H0, 
    cases (list.exists_of_mem_map Hr^.elim_left) with ll Hll,
    cases (list.exists_of_mem_map Hs^.elim_left) with lr Hlr,
    existsi (∀ (a : α), a ∈ append_pair (ll,lr) → atom_type.val bs a),
    apply and.intro, 
    rewrite iff.symm (allp_iff_forall_mem (val bs) (append_pair (ll,lr))),
    apply mem_map_of_mem _, 
    apply mem_product_of_mem_and_mem,
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
    unfold dnf, rewrite map_append, 
    rewrite disj_list_dist_append,
    rewrite dnf_prsv_alt, rewrite dnf_prsv_alt,
    rewrite exp_I_or, apply H^.elim_right,
    apply H^.elim_left
  end
| (fm.not p) H bs := by cases H
| (fm.ex p) H bs := by cases H

lemma dnf_prsv [atom_type α β] {p : fm α} {H : nqfree p} {bs : list β} : 
  list.some_true (list.map (allp (atom_type.val bs)) (dnf p)) ↔ I p bs := 
iff.trans (by rewrite some_true_iff_disj_list) (@dnf_prsv_alt _ _ _ _ H _)
