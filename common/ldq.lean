import .nnf .dnf

variables {α β : Type}

open atom_type list

lemma exp_I_list_conj [atom_type α β] (xs : list β) : ∀ (ps : list (fm α)),
I (list_conj ps) xs = list.all_true (list.map (λ p, I p xs) ps)  
| [] := 
  begin
    apply @eq.trans _ _ true, refl, 
    apply eq.symm, rewrite eq_true, 
    apply list.all_true_nil
  end
| (p::ps) := 
  begin
    unfold list_conj, simp, 
    rewrite exp_I_and_o, unfold list.all_true,
    apply propext, apply iff.intro, 
    intros H p Hp, cases Hp with Hp Hp, 
    rewrite Hp, apply H^.elim_left, 
    rewrite exp_I_list_conj at H, 
    apply H^.elim_right, apply Hp, 
    intro H, apply and.intro, 
    apply H, apply or.inl (eq.refl _), 
    rewrite exp_I_list_conj, intros q Hq, 
    apply H, apply or.inr, apply Hq 
  end

def qe_prsv (β : Type) [atom_type α β] (qe : list α → fm α) (as : list α) : Prop := 
  ∀ (bs : list β), ((I (qe as) bs) ↔ (∃ x, ∀ a ∈ as, (val (x::bs) a)))

/- 
Requires : qe takes a list of atoms that are all dependent on 0-variable,
  and returns formula which (1) does not contain the 0-variable, and 
  (2) is equivalent to the conjunction of input list.
-/
def qelim (β) [atom_type α β] (qe : list α → fm α) (as : list α) : fm α :=
  and_o 
    (qe (@list.filter _ (dep0 β) (dec_dep0 _ _) as)) 
    (list_conj (list.map (λ (a : α), A' (decr β a)) (@list.filter _ (λ a, ¬ (dep0 β a)) 
      (begin 
         intro a, cases (dec_dep0 _ _ a) with H H, 
         apply decidable.is_true H, 
         apply decidable.is_false (not_not_intro H)
       end) as)))
  
variable (nm : α → Prop)

lemma qelim_prsv [atom_type α β] {qe : list α → fm α} 
  (hqe : ∀ as, (∀ a ∈ as, (dep0 β a)) → (∀ a ∈ as, normal β a) → qe_prsv β qe as)
  {as : list α} {hr : ∀ a ∈ as, normal β a} (bs : list β) : 
  (I (qelim β qe as) bs) ↔ (∃ b, ∀ a ∈ as, val (b::bs) a) := 
begin
  apply iff.intro; intro h,

  unfold qelim at h, 
  rewrite exp_I_and_o at h, cases h with h1 h2,
  rewrite hqe at h1, cases h1 with b h1, 
  existsi b, intros a ha,
  cases (atom_type.dec_dep0 _ β a) with hd hd,
  rewrite exp_I_list_conj at h2, 
  rewrite map_compose at h2,
  rewrite iff.symm (decr_prsv α β),
  apply h2, apply 
  @list.mem_map_of_mem _ _ (λ (x : α), I (A' decr β x) bs) a _ _, 
  apply mem_filter_of_mem, 
  apply ha, apply hd, 
  apply hd, apply h1, 
  apply mem_filter_of_mem, apply ha, 
  apply hd, intro a, apply of_mem_filter,
  apply forall_mem_filter_of_forall_mem,
  apply hr,

  cases h with b hb, unfold qelim, 
  rewrite exp_I_and_o, apply and.intro, 
  rewrite hqe, existsi b, 
  apply forall_mem_filter_of_forall_mem,
  apply hb, intro a,
  apply of_mem_filter, 
  apply forall_mem_filter_of_forall_mem,
  apply hr, 
  rewrite exp_I_list_conj, intros p hp,
  cases (list.exists_of_mem_map hp) with q hq,
  clear hp, simp at hq, cases hq with hq1 hq2, 
  subst hq2, cases hq1 with a h2, cases h2 with h2 h3,
  cases h2 with h2 h4, subst h3, 
  unfold I, unfold interp, rewrite decr_prsv,
  apply hb _ h2, apply h4
end

lemma fnormal_conj_of_allp_fnormal [atom_type α β] : 
  ∀ (ps : list (fm α)), (∀ p ∈ ps, fnormal β p) → fnormal β (list_conj ps) 
| [] hnm := by unfold list_conj 
| (p::ps) hnm := 
  begin
    unfold list_conj, 
    apply cases_and_o, trivial,
    apply hnm, apply or.inl rfl,
    apply fnormal_conj_of_allp_fnormal,
    apply list.forall_mem_of_forall_mem_cons hnm, 
    unfold fnormal, apply and.intro, 
    apply hnm, apply or.inl rfl,
    apply fnormal_conj_of_allp_fnormal,
    apply list.forall_mem_of_forall_mem_cons  hnm 
  end 

lemma fnormal_disj_of_allp_fnormal [atom_type α β] : 
  ∀ (ps : list (fm α)), (∀ p ∈ ps, fnormal β p) → fnormal β (list_disj ps) 
| [] hnm := by unfold list_disj 
| (p::ps) hnm := 
  begin
    unfold list_disj, 
    apply cases_or_o, trivial,
    apply hnm, apply or.inl rfl,
    apply fnormal_disj_of_allp_fnormal,
    apply list.forall_mem_of_forall_mem_cons hnm, 
    unfold fnormal, apply and.intro, 
    apply hnm, apply or.inl rfl,
    apply fnormal_disj_of_allp_fnormal,
    apply list.forall_mem_of_forall_mem_cons hnm 
  end 

meta def qelim_prsv_normal_tac :=
`[apply fnormal_conj_of_allp_fnormal,
  intros p hp, rewrite list.mem_map at hp,
  cases hp with a ha, cases ha with ha1 ha2,
  subst ha2, apply atom_type.decr_prsv_normal,
  apply hnm, apply list.mem_of_mem_filter ha1,
  apply list.of_mem_filter ha1]

lemma qelim_prsv_normal [atom_type α β] {qe : list α → fm α}
  {hqe : ∀ (as : list α), (∀ a ∈ as, dep0 β a) → (∀ a ∈ as, normal β a) → fnormal β (qe as)}  
  {as : list α} (hnm : (∀ a ∈ as, normal β a)) : 
  fnormal β (qelim β qe as) := 
begin
  unfold qelim, apply cases_and_o,
  trivial, apply hqe, intro a,
  apply list.of_mem_filter,
  apply list.forall_mem_filter_of_forall_mem hnm,
  qelim_prsv_normal_tac,
  unfold fnormal, apply and.intro, 
  apply hqe, intro as,
  apply list.of_mem_filter,
  apply list.forall_mem_filter_of_forall_mem hnm,
  qelim_prsv_normal_tac
end

def lift_dnf_qe (β : Type) [atom_type α β] (qe : list α → fm α) : fm α → fm α 
| (fm.true α) := ⊤'
| (fm.false α) := ⊥'
| (fm.atom a) := A' a
| (fm.and p q) := (lift_dnf_qe p) ∧' (lift_dnf_qe q)
| (fm.or p q) := (lift_dnf_qe p) ∨' (lift_dnf_qe q)
| (fm.not p) := ¬' (lift_dnf_qe p) 
| (fm.ex p) := dnf_to_fm (dnf (@nnf _ β _ $ lift_dnf_qe p)) (@qelim _ β _ @qe)

lemma atoms_conj_qfree [atom_type α β] : ∀ (as : list α), qfree (list_conj (list.map (λ (a : α), A' decr β a) as )) 
| [] := trivial
| (a::as) := 
  begin 
    unfold list.map, unfold list_conj, 
    apply cases_and_o, trivial, trivial,
    apply atoms_conj_qfree, unfold qfree, 
    apply and.intro trivial,
    apply atoms_conj_qfree
  end

meta def ldq_normal_tac := 
`[unfold fnormal at hnm, cases hnm with hnmp hnmq,
  unfold lift_dnf_qe, unfold fnormal,
  apply and.intro; apply ldq_normal; assumption]


lemma ldq_normal [atom_type α β] (qe : list α → fm α)  
  (hqe : ∀ (as : list α), (∀ a ∈ as, dep0 β a) → (∀ a ∈ as, normal β a) → fnormal β (qe as)) :
  ∀ p, fnormal β p → fnormal β (lift_dnf_qe β qe p) 
| (fm.true α) hnm := trivial
| (fm.false α) hnm := trivial
| (fm.atom a) hnm := hnm 
| (fm.and p q) hnm := by ldq_normal_tac
| (fm.or p q) hnm := by ldq_normal_tac
| (fm.not p) hnm := 
  begin
    unfold lift_dnf_qe, unfold fnormal,
    apply ldq_normal, apply hnm
  end
| (fm.ex p) hnm := 
  begin
    unfold lift_dnf_qe, unfold dnf_to_fm,
    apply fnormal_disj_of_allp_fnormal,
    intros a ha, rewrite list.mem_map at ha,
    cases ha with as has, cases has with has1 has2,
    subst has2, apply qelim_prsv_normal, apply hqe,
    apply dnf_prsv_normal, apply nnf_prsv_normal, 
    apply ldq_normal, unfold fnormal at hnm, apply hnm,
    apply has1
  end

lemma ldq_qfree [atom_type α β] (qe : list α → fm α)  
  (H : ∀ (l : list α), allp (dep0 β) l → qfree (qe l)) :
  ∀ (p : fm α), qfree (lift_dnf_qe β qe p)  
| (fm.true α) := trivial
| (fm.false α) := trivial
| (fm.atom a) := trivial  
| (fm.and p q) := 
  by {apply and.intro, apply ldq_qfree, apply ldq_qfree} 
| (fm.or p q) := 
  by {apply and.intro, apply ldq_qfree, apply ldq_qfree} 
| (fm.not p) := 
  by {unfold lift_dnf_qe, apply ldq_qfree}
| (fm.ex p) := 
  begin
    unfold lift_dnf_qe, apply qfree_dnf_to_fm, 
    unfold qelim, intro l, 
    apply cases_and_o qfree, trivial, apply H, 
    unfold allp, intro a, apply of_mem_filter,     
    apply atoms_conj_qfree, 
    unfold qfree, apply and.intro, apply H, 
    unfold allp, intro a, apply of_mem_filter,   
    apply atoms_conj_qfree 
  end

lemma I_list_disj [atom_type α β] (xs : list β) : 
  ∀ (ps : list (fm α)), I (list_disj ps) xs ↔ some_true (list.map (λ p, I p xs) ps) 
| [] := 
  begin
    unfold list_disj, unfold map, unfold I, 
    unfold interp, rewrite some_true_nil
  end
| (p::ps) := 
  begin
    unfold list_disj, rewrite exp_I_or_o, 
    unfold map, rewrite some_true_cons,
    rewrite I_list_disj
  end

lemma dist_ex_or (P Q : α → Prop) : (∃ x, (P x ∨ Q x)) ↔ ((∃ x, P x) ∨ (∃ x, Q x)) :=  
begin
  apply iff.intro, intro H, cases H with x Hx, cases Hx with Hx Hx, 
  apply or.inl, existsi x, apply Hx, 
  apply or.inr, existsi x, apply Hx, 
  intro H, cases H with H H, 
  cases H with x Hx, existsi x, apply (or.inl Hx),
  cases H with x Hx, existsi x, apply (or.inr Hx)
end

/-
lemma ex_some_true [atom_type α β] : ∀ (Ps : list (β → Prop)),  
  (∃ (x : β), some_true (list.map (λ (P : β → Prop), P x) Ps)) 
  ↔ (some_true (list.map Exists Ps))  
| [] :=
  begin 
    apply iff.intro; intro h, cases h with x hx, 
    cases hx with p hp, unfold map at hp, cases hp^.elim_left,
    cases h with p hp, unfold map at hp, cases hp^.elim_left,
  end
| (P::Ps) :=  
  begin 
    unfold map, apply iff.intro; intro h,

    cases h with x hx, cases hx with q hq,
    cases hq with hm hq, rewrite mem_cons_iff at hm, 
    cases hm with hm hm, subst hm,
    constructor, apply and.intro, apply or.inl rfl,
    existsi x, apply hq, 
    rewrite (@mem_map _ _ (λ (P : β → Prop), P x) q Ps) at hm,
    cases hm with Q hQ, cases hQ with hQ1 hQ2, subst hQ2,
    existsi (Exists Q), apply and.intro,
    apply mem_cons_of_mem,
    rewrite @mem_map _ _ Exists,
    existsi Q; simp, apply hQ1, existsi x, apply hq,
  
    
  end
-/

instance atom_type_to_dec_eq [atom_type α β] : decidable_eq α := atom_type.dec_eq α β 

lemma ldq_prsv_gen_ex [atom_type α β] 
(qe : list α → fm α)
(hqep : ∀ (as : list α), allp (dep0 β) as → allp (normal β) as → qe_prsv β qe as)
(p : fm α) (hpn : fnormal β p) (hpnq : nqfree p) (bs : list β) : 
  some_true (list.map (λ (x : list α), I (qelim β qe x) bs) (dnf p)) 
  ↔ ∃ (b : β), I p (b :: bs) := 
begin
  apply iff.intro; intro h,

  cases h with q hq, cases hq with hq1 hq2,
  cases (list.exists_of_mem_map hq1) with as has,
  cases has with has1 has2, simp at has2,
  subst has2, 
  rewrite (@qelim_prsv α β) at hq2,
  cases hq2 with b hb, existsi b, 
  rewrite iff.symm (dnf_prsv _), 
  existsi (allp (val (b :: bs)) as),
  apply and.intro, 
  apply list.mem_map_of_mem, apply has1, 
  apply hb, apply hpnq, apply hqep,
  apply dnf_prsv_normal,
  apply hpn,
  
  apply has1, cases h with b hb, 
  rewrite iff.symm (dnf_prsv _) at hb, 
  cases hb with q hq, cases hq with hq1 hq2,
  cases (list.exists_of_mem_map hq1) with as has,
  cases has with has1 has2, subst has2, 
  existsi (I (qelim β qe as) bs), 
  apply and.intro, 
  apply list.mem_map_of_mem  (λ (x : list α), I (qelim β qe x) bs),
  apply has1, rewrite (@qelim_prsv _ β), 
  existsi b, apply hq2, apply hqep, 
  apply dnf_prsv_normal,
  apply hpn, apply has1, apply hpnq
end



meta def ldq_prsv_core_aux := 
`[repeat {rewrite ldq_prsv_gen}, 
  intros a ha, 
  apply hp, unfold atoms, 
  apply mem_union_right, apply ha, 
  intros a ha, 
  apply hp, unfold atoms, 
  apply mem_union_left, apply ha]



lemma ldq_prsv_gen [atom_type α β] 
  (qe : list α → fm α)  
  (hqef : ∀ as, allp (dep0 β) as → qfree (qe as)) 
  (hqen : ∀ as, allp (dep0 β) as → allp (normal β) as → fnormal β (qe as))
  (hqep : ∀ as, allp (dep0 β) as → allp (normal β) as → qe_prsv β qe as) : 
  ∀ p, fnormal β p → ∀ (bs : list β), I (lift_dnf_qe β qe p) bs ↔ I p bs 
| ⊤' _ bs := iff.refl _
| ⊥' _ bs := iff.refl _
| (A' a) hp bs := iff.refl _
| (p ∧' q) hp bs := 
  begin
    cases hp with hp1 hp2, 
    unfold lift_dnf_qe,
    repeat {rewrite exp_I_and}, 
    repeat {rewrite ldq_prsv_gen}, 
    apply hp2, apply hp1
  end
| (p ∨' q) hp bs := 
  begin
    cases hp with hp1 hp2, 
    unfold lift_dnf_qe,
    repeat {rewrite exp_I_or}, 
    repeat {rewrite ldq_prsv_gen}, 
    apply hp2, apply hp1
  end
| (¬' p) hp bs := 
  begin
    unfold lift_dnf_qe,
    repeat {rewrite exp_I_not}, 
    repeat {rewrite ldq_prsv_gen}, 
    apply hp 
  end
| (∃' p) hp bs := 
  calc 
        I (lift_dnf_qe β qe (∃' p)) bs 
      ↔ ∃ (b : β), I (nnf β (lift_dnf_qe β qe p)) (b :: bs) : 
        begin
          unfold lift_dnf_qe, unfold dnf_to_fm,
          rewrite I_list_disj,
          rewrite map_compose, apply
          (@ldq_prsv_gen_ex α β), apply hqep,
          apply nnf_prsv_normal, apply ldq_normal, 
          apply hqen, apply hp, apply nnf_nqfree, 
          apply ldq_qfree, apply hqef
        end
  ... ↔ I (∃' p) bs : 
        begin
          rewrite exp_I_ex, apply ex_iff_ex,
          intro b, rewrite nnf_prsv,
          rewrite ldq_prsv_gen, apply hp,
          apply ldq_qfree, apply hqef
        end 