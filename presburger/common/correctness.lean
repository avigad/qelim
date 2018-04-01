import .atom ...common.lnq ...common.ldq ...common.predicates 

variables {α β : Type}

namespace pbgr

lemma down_closed_fnormal : @down_closed (pbgr.atom) (fnormal int)  
| ⊤' _ hd _ := by cases hd
| ⊥' _ hd _ := by cases hd
| (A' a) _ hd _ := by cases hd
| (p ∧' q) r hd hn := 
  by {unfold fnormal at hn, cases hn, cases hd; assumption}
| (p ∨' q) r hd hn := 
  by {unfold fnormal at hn, cases hn, cases hd; assumption}
| (¬' p) r hd hn := by {cases hd, apply hn}
| (∃' p) r hd hn := by {cases hd, apply hn}

lemma prop_up_closed_fnormal : @prop_up_closed (pbgr.atom) (fnormal int) 
| ⊤' := trivial
| ⊥' := trivial
| (A' a) := trivial
| (p ∧' q) := begin intros hp hq, apply and.intro hp hq end
| (p ∨' q) := begin intros hp hq, apply and.intro hp hq end
| (¬' p) := id
| (∃' p) := trivial

lemma fnormal_and_o : ∀ (p q : fm atom), fnormal int p → fnormal int q → fnormal int (and_o p q)
 := pred_and_o (fnormal int) prop_up_closed_fnormal

lemma fnormal_or_o : ∀ (p q : fm atom), fnormal int p → fnormal int q → fnormal int (or_o p q)
 := pred_or_o (fnormal int) prop_up_closed_fnormal

lemma fnormal_list_disj : ∀ (ps : list (fm atom)), (∀ p ∈ ps, fnormal int p) → fnormal int (list_disj ps) :=
pred_list_disj _ prop_up_closed_fnormal

lemma fnormal_disj : ∀ (bs : list β) (f : β → fm atom), (∀ b ∈ bs, fnormal int (f b)) → fnormal int (disj bs f) := 
pred_disj _ prop_up_closed_fnormal

meta def nnf_closed_fnormal_aux := 
`[unfold nnf, unfold fnormal,
  unfold fnormal at hn, cases hn with hnp hnq, 
  cases (nnf_closed_fnormal_core hnp) with hnp1 hnp2,
  cases (nnf_closed_fnormal_core hnq) with hnq1 hnq2,
  apply and.intro; apply and.intro; assumption]

lemma nnf_closed_fnormal_core : ∀ {p : fm pbgr.atom}, 
  fnormal int p → fnormal int (nnf int p) ∧ fnormal int (nnf int (¬' p))
| ⊤' hn := and.intro trivial trivial 
| ⊥' hn := and.intro trivial trivial 
| (A' a) hn := 
  begin
    unfold nnf, apply and.intro, 
    apply hn, rewrite fnormal_iff_fnormal_alt,
    apply atom_type.neg_prsv_normal, apply hn
  end
| (p ∧' q) hn := by nnf_closed_fnormal_aux
| (p ∨' q) hn := by nnf_closed_fnormal_aux
| (¬' p) hn := 
  begin
    apply and.symm, unfold fnormal at hn,
    unfold nnf, apply nnf_closed_fnormal_core hn
  end
| (∃' p) hn := 
  begin unfold nnf, apply and.intro; trivial end

lemma nnf_closed_fnormal : preserves (@nnf pbgr.atom int _) (fnormal int) := 
λ p hn, (nnf_closed_fnormal_core hn)^.elim_left

lemma atoms_and_o_subset {p q : fm pbgr.atom} : 
  atoms (and_o p q) ⊆ atoms p ∪ atoms q := 
begin
  apply cases_and_o' (λ p' q' r, atoms r ⊆ atoms p' ∪ atoms q') p q;
  intros a ha, 
  apply list.mem_union_right, apply ha, 
  apply list.mem_union_left, apply ha, 
  apply list.mem_union_left, apply ha, 
  apply list.mem_union_right, apply ha, 
  apply ha
end

lemma lnq_closed_fnormal (f : fm atom → fm atom) 
 (hc : preserves f (fnormal ℤ)) : preserves (lift_nnf_qe ℤ f) (fnormal ℤ) 
| ⊤' hn := trivial
| ⊥' hn := trivial
| (A' a) hn := by {unfold lift_nnf_qe, apply hn}
| (p ∧' q) hn := 
  begin
    unfold fnormal at hn , cases hn with hnp hnq,
    unfold lift_nnf_qe, apply cases_and_o, trivial, 
    apply lnq_closed_fnormal, apply hnp,
    apply lnq_closed_fnormal, apply hnq,
    apply and.intro; apply lnq_closed_fnormal; assumption, 
  end
| (p ∨' q) hn := 
  begin
    unfold fnormal at hn , cases hn with hnp hnq,
    unfold lift_nnf_qe, apply cases_or_o, trivial, 
    apply lnq_closed_fnormal, apply hnp,
    apply lnq_closed_fnormal, apply hnq,
    apply and.intro; apply lnq_closed_fnormal; assumption, 
  end
| (¬' p) hn := 
  begin
    unfold fnormal at hn, unfold lift_nnf_qe, apply cases_not_o, 
    trivial, trivial, apply lnq_closed_fnormal, apply hn
  end
| (∃' p) hn := 
  begin
    unfold lift_nnf_qe, apply hc, 
    apply nnf_closed_fnormal, 
    apply lnq_closed_fnormal, apply hn
  end

theorem lnq_prsv 
  (qe : fm pbgr.atom → fm pbgr.atom) 
  (hqe : preserves qe (fnormal int))
  (hqf : qfree_res_of_nqfree_arg qe)
  (hi : ∀ p, nqfree p → fnormal int p → ∀ (bs : list int), I (qe p) bs ↔ ∃ b, (I p (b::bs))) : 
∀ p, fnormal int p → ∀ (bs : list int), I (lift_nnf_qe int qe p) bs ↔ I p bs :=
@lnq_prsv_gen pbgr.atom int pbgr.atom_type 
  qe hqf (fnormal int) down_closed_fnormal hqe 
  nnf_closed_fnormal lnq_closed_fnormal hi 

theorem ldq_prsv 
  (qe : list pbgr.atom → fm pbgr.atom) 
  (hqf : ∀ as, (∀ a ∈ as, dep0 a) → qfree (qe as)) 
  (hn : ∀ as, (∀ a ∈ as, dep0 a) → (∀ a ∈ as, normal a) → fnormal int (qe as)) 
  (he : ∀ as, (∀ a ∈ as, dep0 a) → (∀ a ∈ as, normal a) → qe_prsv int qe as) :
  ∀ p, fnormal int p → ∀ (bs : list int), I (lift_dnf_qe int qe p) bs ↔ I p bs :=
@ldq_prsv_gen pbgr.atom int pbgr.atom_type _ hqf hn he 

end pbgr


