import .atom .ldq

variables {α β : Type}

open tactic atom_eq_type

def lift_eq_qe (β : Type) [atom_eq_type α β] (qe : list α → fm α) (as : list α) : fm α := 
  let ntas := @list.filter _ (λ (a : α), ¬ atom_eq_type.trivial β a) 
    begin
      apply dec_not_pred_of_dec_pred (trivial β),  
      apply atom_eq_type.dec_triv
    end as in 
  match @list.first _ (solv0 β) 
        begin apply atom_eq_type.dec_solv0 end ntas with 
  | none := qe ntas 
  | some (eq,rest) := 
    list_conj  (list.map (λ (a : α), A' (subst0 β eq a)) rest)
  end

lemma leq_qe_prsv [atom_eq_type α β] (qe : list α → fm α) 
  (H : ∀ (as : list α), (∀ (a : α), a ∈ as → atom_type.dep0 β a ∧ ¬ solv0 β a) → qe_prsv β qe as) : 
  ∀ (as : list α), (∀ (a : α), a ∈ as → atom_type.dep0 β a) → qe_prsv β (lift_eq_qe β qe) as := 
begin
  intros as Has, unfold qe_prsv, intros bs, 
  unfold lift_eq_qe, simp, 
  cases (@cases_first _ (solv0 β) (dec_solv0 _ β) 
    (@list.filter _ (λ (a : α), ¬trivial β a) 
      (begin apply dec_not_pred_of_dec_pred (trivial β),  
      apply atom_eq_type.dec_triv end) as)) with HC HC,
  rewrite HC^.elim_left, 
  unfold lift_eq_qe, unfold qe_prsv at H,
  apply iff.trans, apply H, intros a Ha, 
  apply and.intro, apply Has, apply mem_of_mem_filter Ha,
  apply HC^.elim_right, apply Ha, 
  apply ex_iff_ex, intro b, 
  apply iff.intro, intros HL a Ha, 
  cases (dec_triv α β a) with HT HT, apply HL,
  apply mem_filter_of_mem, apply HT, apply Ha,
  apply true_triv, apply HT, 
  intros HR a Ha, apply HR, apply mem_of_mem_filter,
  apply Ha, 
  cases HC with eqn HC, cases HC with as' HC, 
  cases HC with H1 H2, cases H2 with H2 H3, 
  rewrite H1, unfold lift_eq_qe,
  rewrite exp_I_list_conj, rewrite map_compose, 
  
  apply iff.intro, intro HL, 
  existsi (list.nth_dft (atom_type.inh α β) bs ((@atom_eq_type.dest_solv0 α β _ eqn H2)-1)),
  intros a Ha, 
  cases (dec_triv α β a) with HT HT, 
  cases (atom_type.dec_eq α β a eqn) with HE HE,
  apply (atom_eq_type.subst_prsv H2)^.elim_left,
  apply HL, apply mem_map_of_mem,
  have HM : a ∈ (eqn::as'), apply (H3 a)^.elim_left,
  apply mem_filter_of_mem, apply HT,
  apply Ha, cases HM with HM HM, 
  apply absurd HM HE, apply HM,
  rewrite HE,  
  apply (atom_eq_type.subst_prsv H2)^.elim_left,
  apply atom_eq_type.true_subst, apply H2,
  apply true_triv, apply HT,
  intros HR p Hp, 
  cases (list.exists_of_mem_map Hp) with a Ha,
  cases Ha with Ha Ha', rewrite Ha', 
  clear Hp, clear Ha', clear p, 
  apply (atom_eq_type.subst_prsv H2)^.elim_right,
  cases HR with b Hb,
  have Hbe := atom_eq_type.solv0_eq H2 (Hb eqn _),
  have H4 := (H3 a)^.elim_right _,
  rewrite (nth_dft_pred _) at Hbe,
  rewrite Hbe, apply Hb, 
  apply mem_of_mem_filter H4, 
  apply dest_pos, 
  have H5 := (H3 eqn)^.elim_right _,
  apply of_mem_filterH5, 
  apply or.inl, refl, apply or.inr Ha,
  have H5 := (H3 eqn)^.elim_right _,
  apply mem_of_mem_filter H5, apply or.inl, refl
end

def lift_dnfeq_qe (β : Type) [atom_eq_type α β] (qe : list α → fm α) := lift_dnf_qe β (@lift_eq_qe α β _ qe) 

lemma leq_qfree [HA : atom_eq_type α β] (qe : list α → fm α)
(Hqe : ∀ (as' : list α), allp (atom_type.dep0 β) as' → qfree (qe as'))
(l : list α) (Hl : allp (atom_type.dep0 β) l) : qfree (lift_eq_qe β qe l) := 
begin
  unfold lift_eq_qe, simp,
  cases (list.first (solv0 β) _) with pr,
  apply Hqe, intros x Hx, apply Hl,
  apply mem_of_mem_filter Hx, cases pr with eqn as',
  apply qfree_list_conj, intros a Ha, 
  cases (list.exists_of_mem_map Ha) with a' Ha',
  rewrite Ha'^.elim_right, simp 
end

lemma ldeq_qfree [atom_eq_type α β] (qe : list α → fm α) 
  (Hqe : ∀ (as') (Has' : allp (@atom_type.dep0 α β _) as'), qfree (qe as')) 
  (p : fm α) : qfree (lift_dnfeq_qe β qe p) := 
begin
  unfold lift_dnfeq_qe, apply ldq_qfree, 
  intros as Has, apply leq_qfree, apply Hqe,
  apply Has
end

lemma ldeq_prsv [atom_eq_type α β] (qe : list α → fm α) 
  (Hqe : ∀ (as) (Has : allp (@atom_type.dep0 α β _) as), qfree (qe as)) 
  (Has : ∀ (as : list α), (∀ (a' : α), a' ∈ as → atom_type.dep0 β a' ∧ ¬ solv0 β a') → qe_prsv β qe as)  
  (p : fm α) (bs : list β) : I (lift_dnfeq_qe β qe p) bs ↔ I p bs := 
begin
  unfold lift_dnfeq_qe, apply ldq_prsv, apply leq_qfree,
  apply Hqe, apply leq_qe_prsv, apply Has
end