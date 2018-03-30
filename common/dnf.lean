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
    simp at ha, cases ha with hm hm,
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
    rewrite mem_append at has,
    cases has with hm hm,
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

lemma dnf_prsv [atom_type α β] : ∀ {p : fm α} {bs : list β},
  nqfree p → (list.some_true (list.map (allp (atom_type.val bs)) (dnf p)) ↔ I p bs) 
| (fm.true α) bs hf :=
  begin
    unfold dnf, unfold map, unfold I,
    unfold interp, simp, existsi true, simp
  end 
| (fm.false α) bs hf :=
  begin
    unfold dnf, unfold map, unfold I,
    unfold interp, simp, intro hc, cases hc with p hp,
    cases hp with hp1 hp2, cases hp1
  end 
| (fm.atom a) bs hf := 
  begin
    unfold dnf, unfold map, unfold I,
    unfold interp, simp, unfold some_true,
    apply iff.intro; intro h, cases h with p hp,
    cases hp with hp1 hp2, rewrite mem_singleton at hp1,
    subst hp1, apply hp2, existsi (val bs a), simp, apply h
  end
| (p ∧' q) bs hf := 
  begin
    cases hf with hfp hfq, unfold dnf,
    unfold some_true, rewrite map_compose,
    rewrite exp_I_and, 
    rewrite iff.symm (@dnf_prsv p bs hfp),
    rewrite iff.symm (@dnf_prsv q bs hfq),
    apply iff.intro; intro h,
    
    cases h with r hr, cases hr with hr1 hr2,
    rewrite mem_map at hr1, cases hr1 with ll hll,
    cases hll with hll1 hll2, subst hll2, cases ll with lp lq,
    unfold append_pair at hr2, rewrite mem_product at hll1,
    cases hll1 with hlp hlq, unfold allp at hr2,
    rewrite forall_mem_append at hr2, cases hr2 with hp hq,
    apply and.intro,
    existsi (allp (val bs) lp), 
    apply and.intro (mem_map_of_mem _ hlp) hp,
    existsi (allp (val bs) lq), 
    apply and.intro (mem_map_of_mem _ hlq) hq,

    cases h with hp hq, 
    cases hp with cp hcp, cases hcp with hcp1 hcp2, 
    cases hq with cq hcq, cases hcq with hcq1 hcq2,
    rewrite mem_map at hcp1, cases hcp1 with lp hlp,
    cases hlp with hlp1 hlp2, subst hlp2,
    rewrite mem_map at hcq1, cases hcq1 with lq hlq,
    cases hlq with hlq1 hlq2, subst hlq2,
    existsi (allp (val bs) (lp ++ lq)), apply and.intro,
    rewrite mem_map, existsi (lp,lq), apply and.intro,
    rewrite mem_product, apply and.intro; assumption,
    refl, unfold allp, rewrite forall_mem_append,
    apply and.intro hcp2 hcq2
  end
| (p ∨' q) bs hf := 
  begin
    cases hf with hfp hfq,
    unfold dnf, rewrite map_append, rewrite some_true_append,
    rewrite @dnf_prsv p _ hfp, rewrite @dnf_prsv q _ hfq, rewrite exp_I_or,
  end
| (fm.not _) bs hf := by cases hf
| (fm.ex _) bs hf := by cases hf
