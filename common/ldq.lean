import .nnf .dnf

variables {α β : Type}

open atom_type

def qe_prsv (β : Type) [atom_type α β] (qe : list α → fm α) (as : list α) : Prop := 
  ∀ (bs : list β), ((I (qe as) bs) ↔ (∃ x, allp (val (x::bs)) as))

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
      
      #check exp_I_list_conj
lemma qelim_prsv [atom_type α β] {r} {qe} 
  (hqe : ∀ as, allp (dep0 β) as → allp r as → qe_prsv β qe as)
  {as : list α} (bs : list β) : 
  (I (qelim β qe as) bs) ↔ (∃ b, allp (val (b::bs)) as) := 
begin
  apply iff.intro; intro h,
  unfold qelim at h, 
  rewrite exp_I_and_o at h, cases h with h1 h2,
  rewrite hqe at h1, cases h1 with b h1, 
  existsi b, intros a ha,
  cases (atom_type.dec_dep0 _ β a),
  rewrite exp_I_list_conj at h2, 

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
    unfold lift_dnf_qe, apply disj_qfree, 
    unfold qelim, intro l, 
    apply cases_and_o qfree, trivial, 
    apply H, apply allp_filter,     
    apply atoms_conj_qfree, 
    unfold qfree, apply and.intro, apply H, 
    apply allp_filter, apply atoms_conj_qfree 
  end

lemma foo (Q : list β → α → Prop) (a : α) : ∀ (bss : list (list β)), 
  list.map (λ bs, Q bs a) bss = list.map (λ (P : α → Prop), P a) (list.map Q bss)  
| [] := eq.refl _
| (bs::bss) := by simp 

lemma exp_I_list_conj [atom_type α β] (xs : list β) : ∀ (ps : list (fm α)),
I (list_conj ps) xs = all_true (list.map (λ p, I p xs) ps)  
| [] := 
  begin
    apply @eq.trans _ _ true, refl, 
    apply eq.symm, rewrite eq_true, 
    apply all_true_nil
  end
| (p::ps) := 
  begin
    unfold list_conj, simp, 
    rewrite exp_I_and_o, unfold all_true,
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

lemma exp_I_list_disj [atom_type α β] (xs : list β) : ∀ (ps : list (fm α)),
I (list_disj ps) xs ↔ disj_list (list.map (λ p, I p xs) ps)  
| [] := iff.refl _ 
| (p::ps) := 
  begin
    simp, unfold list_disj, unfold disj_list,
    rewrite (iff.symm (exp_I_list_disj ps)), 
    apply exp_I_or_o
  end

lemma exp_I_list_disj_alt [atom_type α β] (xs : list β) (ps : list (fm α)) :
I (list_disj ps) xs ↔ some_true (list.map (λ p, I p xs) ps) := 
iff.trans (exp_I_list_disj _ _) 
  (by rewrite some_true_iff_disj_list) 

lemma dist_ex_or (P Q : α → Prop) : (∃ x, (P x ∨ Q x)) ↔ ((∃ x, P x) ∨ (∃ x, Q x)) :=  
begin
  apply iff.intro, intro H, cases H with x Hx, cases Hx with Hx Hx, 
  apply or.inl, existsi x, apply Hx, 
  apply or.inr, existsi x, apply Hx, 
  intro H, cases H with H H, 
  cases H with x Hx, existsi x, apply (or.inl Hx),
  cases H with x Hx, existsi x, apply (or.inr Hx)
end

lemma dist_ex_disj_list [atom_type α β] : ∀ (ps : list (β → Prop)),  
  (∃ (x : β), disj_list (list.map (λ (p : β → Prop), p x) ps)) 
  ↔ (disj_list (list.map Exists ps))  
| [] :=
  begin 
    apply iff.intro, intro H, cases H with x Hx, 
    unfold list.map at Hx, unfold disj_list at Hx, 
    apply Hx, intro H, cases H
  end
| (p::ps) :=  
  begin 
    unfold list.map, unfold disj_list,
    apply iff.trans, apply dist_ex_or,
    rewrite dist_ex_disj_list
  end

instance atom_type_to_dec_eq [atom_type α β] : decidable_eq α := atom_type.dec_eq α β 

meta def ldq_prsv_core_aux := 
`[repeat {rewrite ldq_prsv_gen}, 
  intros a ha, 
  apply hp, unfold atoms, 
  apply mem_union_of_mem_right, apply ha, 
  intros a ha, 
  apply hp, unfold atoms, 
  apply mem_union_of_mem_left, apply ha]

lemma ldq_prsv_gen_ex [atom_type α β] 
(qe : list α → fm α)
(hqf : ∀ (as : list α), allp (dep0 β) as → qfree (qe as))
(r : α → Prop)
(hqe : ∀ (as : list α), allp (dep0 β) as → allp r as → qe_prsv β qe as)
(p : fm α)
(hnqf : nqfree p)
(bs : list β)
: some_true (list.map (λ (x : list α), I (qelim β qe x) bs) (dnf p)) ↔
    ∃ (b : β), I p (b :: bs) := 
begin
  apply iff.intro; intro h,

  cases h with q hq, cases hq with hq1 hq2,
  cases (ex_arg_of_mem_map hq1) with as has,
  cases has with has1 has2, simp at has2,
  subst has2, rewrite qelim_prsv at hq2,
  cases hq2 with b hb, existsi b, 
  rewrite iff.symm dnf_prsv,
  existsi (allp (val (b :: bs)) as),
  apply and.intro, 
  apply mem_map_of_mem, apply has1, 
  apply hb, apply hnqf, apply hqe,

  cases h with b hb, 
  rewrite iff.symm dnf_prsv at hb, 
  cases hb with q hq, cases hq with hq1 hq2,
  cases (ex_arg_of_mem_map hq1) with as has,
  cases has with has1 has2, subst has2, 
  existsi (I (qelim β qe as) bs), 
  apply and.intro, apply mem_map_of_mem,
  apply has1, rewrite qelim_prsv, 
  existsi b, apply hq2, apply hqe, apply hnqf
end

lemma ldq_prsv_gen [atom_type α β] (qe : list α → fm α)  
  (hqf : ∀ as, allp (dep0 β) as → qfree (qe as)) 
  (r : α → Prop) 
  (hr : ∀ as, allp (dep0 β) as → allp r as → fnormal β (qe as)) 
  (he : ∀ as, allp (dep0 β) as → allp r as → qe_prsv β qe as) : 
  ∀ p, allp r (atoms p) → ∀ (bs : list β), I (lift_dnf_qe β qe p) bs ↔ I p bs 
| ⊤' _ bs := iff.refl _
| ⊥' _ bs := iff.refl _
| (A' a) hp bs := iff.refl _
| (p ∧' q) hp bs := 
  begin
    unfold lift_dnf_qe,
    repeat {rewrite exp_I_and}, 
    ldq_prsv_core_aux
  end
| (p ∨' q) hp bs := 
  begin
    unfold lift_dnf_qe,
    repeat {rewrite exp_I_or}, 
    ldq_prsv_core_aux
  end
| (¬' p) hp bs := 
  begin
    unfold lift_dnf_qe,
    repeat {rewrite exp_I_not}, 
    repeat {rewrite ldq_prsv_gen}, 
    intros a ha, apply hp, apply ha
  end
| (∃' p) hp bs := 
  calc 
        I (lift_dnf_qe β qe (∃' p)) bs 
      ↔ ∃ (b : β), I (nnf β (lift_dnf_qe β qe p)) (b :: bs) : 
        begin
          unfold lift_dnf_qe, unfold dnf_to_fm,
          rewrite exp_I_list_disj_alt,
          rewrite map_compose, apply ldq_prsv_gen_ex,
          apply hqf, apply he, apply nnf_nqfree, 
          apply ldq_qfree, apply hqf
        end
  ... ↔ I (∃' p) bs : 
        begin
          rewrite exp_I_ex, apply ex_iff_ex,
          intro b, rewrite nnf_prsv,
          rewrite ldq_prsv_gen, apply hp,
          apply ldq_qfree, apply hqf
        end 

#exit


lemma ldq_prsv [HA : atom_type α β] (qe : list α → fm α)  
  (H1 : ∀ (l : list α), allp (dep0 β) l → qfree (qe l))
  (H2 : ∀ (as : list α), allp (dep0 β) as → qe_prsv β qe as) : 
    ∀ (p : fm α) (xs : list β), I (lift_dnf_qe β qe p) xs ↔ I p xs 
| (fm.true α) xs := iff.refl _
| (fm.false α) xs := iff.refl _
| (fm.atom a) xs := iff.refl _
| (fm.and p q) xs := 
  begin
    unfold lift_dnf_qe, 
    repeat {rewrite exp_I_and}, 
    repeat {rewrite ldq_prsv} 
  end
| (fm.or p q) xs := 
  begin
    unfold lift_dnf_qe, 
    repeat {rewrite exp_I_or}, 
    repeat {rewrite ldq_prsv} 
  end
| (fm.not p) xs := 
  begin
    unfold lift_dnf_qe, 
    repeat {rewrite exp_I_not}, 
    rewrite ldq_prsv
  end
| (fm.ex p) xs := 
  begin
    unfold lift_dnf_qe, rewrite exp_I_ex,  
    apply iff.symm, 
    apply @iff.trans _ (∃ x, I (lift_dnf_qe β qe p) (x::xs)),  
    apply ex_iff_ex, 
    intro x, rewrite ldq_prsv p (x::xs), 
    apply @iff.trans _ (∃ x, I (nnf _ (lift_dnf_qe β qe p)) (x::xs)),  
    apply ex_iff_ex, 
    intro x, rewrite nnf_prsv, 
    apply ldq_qfree, apply H1, 
    apply iff.trans, apply ex_iff_ex, 
    intro x, apply iff.symm, 
    apply (dnf_prsv _ _ (x::xs)), 
    apply nnf_nqfree, apply ldq_qfree, apply H1, 
    apply iff.trans, apply ex_iff_ex, intro b,
    rewrite (@foo β α (λ (as : list α) (b : β), ∀ (a : α), a ∈ as → val (b :: xs) a)), 
    apply iff.trans, apply @dist_ex_disj_list α β _,
    unfold disj, apply iff.symm,
    apply iff.trans, apply exp_I_list_disj,
    apply iff_of_eq, apply (congr_arg disj_list),
    apply eq.symm, apply eq.trans,
    apply map_compose, simp, 
    apply map_eq, 
    
    unfold function.comp, 
    intro as, intro Has, 
    unfold qelim, rewrite exp_I_and_o, 
    rewrite H2,  
    
    apply propext, apply iff.intro,
    intro H3, apply and.intro, 

    cases H3 with b Hb, existsi b, 
    intros a Ha, apply Hb,
    apply mem_of_mem_filter,
    apply Ha, rewrite exp_I_list_conj,
    rewrite map_compose, unfold all_true, 
    intros q Hq, cases (ex_arg_of_mem_map Hq) with a Ha,
    simp at Ha, rewrite Ha^.elim_left, 
    cases H3 with b Hb, unfold I, unfold interp,
    rewrite decr_prsv a _ b, apply Hb, 
    apply mem_of_mem_filter Ha^.elim_right,
    apply pred_of_mem_filter_pred Ha^.elim_right,
    intro H3, 
    have Hb := H3^.elim_left,
    have H4 := H3^.elim_right, clear H3, 
    cases Hb with b Hb, existsi b, 
    intros a Ha, 
    cases (dec_dep0 _ β a) with HD HD,
    rewrite exp_I_list_conj at H4, simp at H4, 
    rewrite (iff.symm (decr_prsv a _ b xs)),
    apply H4, apply mem_map_of_mem _ a, 
    apply mem_filter_of_pred_and_mem, 
    apply HD, apply Ha, apply HD, 
    apply Hb, apply mem_filter_of_pred_and_mem,
    apply HD, apply Ha, apply allp_filter,
  end