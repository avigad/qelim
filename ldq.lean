import .nnf .dnf

variables {α β : Type}

open atom

def qelim [atom α β] (qe : list α → fm α) (as : list α) : fm α :=
  and_o 
    (qe (@list.filter _ (dep0 β) (dec_dep0 _ _) as)) 
    (list_conj (list.map (λ (a : α), A' (decr β a)) (@list.filter _ (λ a, ¬ (dep0 β a)) 
      (begin 
         intro a, cases (dec_dep0 _ _ a) with H H, 
         apply decidable.is_true H, 
         apply decidable.is_false (not_not_intro H)
       end) as)))
      
def lift_dnf_qe (β : Type) [atom α β] (qe : list α → fm α) : fm α → fm α 
| (fm.true α) := ⊤'
| (fm.false α) := ⊥'
| (fm.atom a) := A' a
| (fm.and p q) := (lift_dnf_qe p) ∧' (lift_dnf_qe q)
| (fm.or p q) := (lift_dnf_qe p) ∨' (lift_dnf_qe q)
| (fm.not p) := ¬' (lift_dnf_qe p) 
| (fm.ex p) := disj (dnf (@nnf _ β _ $ lift_dnf_qe p)) (@qelim _ β _ @qe)

lemma atoms_conj_qfree [atom α β] : ∀ (as : list α), qfree (list_conj (list.map (λ (a : α), A' decr β a) as )) 
| [] := trivial
| (a::as) := 
  begin 
    unfold list.map, unfold list_conj, 
    apply cases_and_o, trivial, trivial,
    apply atoms_conj_qfree, unfold qfree, 
    apply and.intro trivial,
    apply atoms_conj_qfree
  end

lemma ldq_qfree [atom α β] (qe : list α → fm α)  
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

def is_dnf_qe (β : Type) [HA : atom α β] (qe : list α → fm α) (as : list α) : Prop := 
  ∀ (xs : list β), ((@I _ _ HA (qe as) xs) ↔ (∃ x, (∀ a, a ∈ as → I (A' a) (x::xs))))

lemma foo (Q : list β → α → Prop) (a : α) : ∀ (bss : list (list β)), 
  list.map (λ bs, Q bs a) bss = list.map (λ (P : α → Prop), P a) (list.map Q bss)  
| [] := eq.refl _
| (bs::bss) := by simp 


lemma exp_I_list_conj [atom α β] (xs : list β) : ∀ (ps : list (fm α)),
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

lemma exp_I_list_disj [atom α β] (xs : list β) : ∀ (ps : list (fm α)),
I (list_disj ps) xs ↔ disj_list (list.map (λ p, I p xs) ps)  
| [] := iff.refl _ 
| (p::ps) := 
  begin
    simp, unfold list_disj, unfold disj_list,
    rewrite (iff.symm (exp_I_list_disj ps)), 
    apply exp_I_or_o
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

lemma dist_ex_disj_list [atom α β] : ∀ (ps : list (β → Prop)),  
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
  
lemma ldq_prsv [HA : atom α β] (qe : list α → fm α)  
  (H1 : ∀ (l : list α), allp (dep0 β) l → qfree (qe l))
  (H2 : ∀ (as : list α), allp (dep0 β) as → is_dnf_qe β qe as) : 
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
    apply @iff.trans _ (∃ x, I (nnf (lift_dnf_qe β qe p)) (x::xs)),  
    apply ex_iff_ex, 
    intro x, rewrite nnf_prsv, 
    apply ldq_qfree, apply H1, 
    apply iff.trans, apply ex_iff_ex, 
    intro x, apply iff.symm, 
    apply (dnf_prsv _ _ (x::xs)), 
    apply nnf_nqfree, apply ldq_qfree, apply H1, 
    apply iff.trans, apply ex_iff_ex, intro b,
    rewrite (@foo β α (λ (as : list α) (b : β), ∀ (a : α), a ∈ as → val a (b :: xs))), 
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
    intros q Hq, cases (exp_mem_map Hq) with a Ha,
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
    rewrite (eq.symm (decr_prsv a _ b xs)),
    apply H4, apply mem_map_of_mem _ a, 
    apply mem_filter_of_pred_and_mem, 
    apply HD, apply Ha, apply HD, 
    apply Hb, apply mem_filter_of_pred_and_mem,
    apply HD, apply Ha, apply allp_filter,
  end