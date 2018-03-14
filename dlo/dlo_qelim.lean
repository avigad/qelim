import .dlo 

variables {α β : Type}

def dlo_qe_aux (as : list adlo) := -- (HZ) (H) := 
let prs := list.product (dlo_qe_lbs as) (dlo_qe_ubs as) in 
list_conj $ @list.map adlo (fm adlo) (@fm.atom adlo) (list.map (λ pr, (prod.fst pr <' prod.snd pr)) prs)

def dlo_qe (β : Type) [atom_eq_type adlo β] (as : list adlo) : fm adlo := 
@ite (adlo.lt 0 0 ∈ as) 
  (@list.decidable_mem adlo (atom_type.dec_eq _ β) (0 <' 0) as) _
  ⊥'
  (@ite (allp is_b_atm as) 
    (dec_allp _) _ 
    (dlo_qe_aux as)
    (⊥')
  )

def dlo_qelim (β : Type) [atom_eq_type adlo β] : fm adlo → fm adlo :=  
@lift_dnfeq_qe _ β _ (dlo_qe β)

-- Q : Why doesn't `cases (dlo_dec_mem (0 <' 0) as)` simplify things here? 
lemma dlo_qe_qfree [HA : atom_eq_type adlo β] : 
  ∀ (as : list adlo) (Has : allp (@atom_type.dep0 adlo β _) as), 
    qfree (dlo_qe β as) := 
begin
  intros as Has, unfold dlo_qe, 
  apply cases_ite, intro H, trivial, 
  intro HM, apply cases_ite, intro Hlt,
  unfold dlo_qe_aux, simp, apply list_conj_qfree,
  intros x Hx, 
  cases (ex_arg_of_mem_map Hx) with y Hy,
  cases Hy with Hyl Hyr, rewrite Hyr,
  cases y, unfold function.comp, 
  intro H, trivial
end

lemma btw_of_lt [dlo β] {m n} {bs : list β} (H : atom_type.val (m<' n) bs) :
  ∃ b, ((tval m bs < b) ∧ (b < tval n bs)) :=  
begin
  cases (dlo.btw H) with b Hb, 
  existsi b, apply Hb
end

lemma is_b_atm_of [dlo β] : 
  ∀ (a), (λ a', atom_type.dep0 β a' ∧ ¬atom_eq_type.solv0 β a' ∧ a' ≠ (0 <' 0)) a → is_b_atm a 
| (0   =' n  ) h := 
  begin exfalso, apply h^.elim_right^.elim_left, apply or.inl rfl end
| (m   =' 0  ) h := 
  begin exfalso, apply h^.elim_right^.elim_left, apply or.inr rfl end
| (m+1 =' n+1) h := 
  begin exfalso, cases h^.elim_left with h h; cases h end
| (0   <' 0  ) h := 
  begin exfalso, apply h^.elim_right^.elim_right, refl end
| (m+1 <' 0  ) h := 
  begin existsi m, apply or.inl rfl end
| (0   <' n+1) h := 
  begin existsi n, apply or.inr rfl end
| (m+1 <' n+1) h := 
  begin exfalso, cases h^.elim_left with h h; cases h end

lemma ex_high_lb_of_ex_lb [dlo β]   
  {as : list adlo} (hlb : ∃ m, is_lb m as) (bs : list β) :
∃ k, (is_lb k as ∧ ∀ j, is_lb j as → dle j k bs) := 
begin
  cases hlb with m hm, 
  have hi : list.map (λ n, tval n bs) (dlo_qe_lbs as) ≠ [],
  intro hc, have he := eq_nil_of_map_eq_nil hc,
  have hmm := mem_lbs_of_is_lb hm, 
  rewrite he at hmm, cases hmm,
  cases (exists_maximum _ hi) with b hb,
  cases hb with hb1 hb2, 
  cases (ex_arg_of_mem_map hb1) with k hk,
  cases hk with hk1 hk2, 
  existsi k, apply and.intro (is_lb_of_mem_lbs hk1),
  intros j hj, simp at hk2, unfold dle,  
  rewrite eq.symm hk2, apply hb2, 
  apply mem_map_of_mem, apply mem_lbs_of_is_lb hj
end

lemma ex_low_ub_of_ex_ub [dlo β] 
  {as : list adlo} (hub : ∃ n, is_ub n as) (bs : list β) :
∃ k, (is_ub k as ∧ ∀ j, is_ub j as → dle k j bs) := 
begin
  cases hub with n hn, 
  have hi : list.map (λ n, tval n bs) (dlo_qe_ubs as) ≠ [],
  intro hc, have he := eq_nil_of_map_eq_nil hc,
  have hnm := mem_ubs_of_is_ub hn, 
  rewrite he at hnm, cases hnm,
  cases (exists_minimum _ hi) with b hb,
  cases hb with hb1 hb2, 
  cases (ex_arg_of_mem_map hb1) with k hk,
  cases hk with hk1 hk2, 
  existsi k, apply and.intro (is_ub_of_mem_ubs hk1),
  intros j hj, simp at hk2, unfold dle,  
  rewrite eq.symm hk2, apply hb2, 
  apply mem_map_of_mem, apply mem_ubs_of_is_ub hj
end

lemma dlo_qe_is_dnf [HD : dlo β] : ∀ (as : list adlo), 
  (∀ (a : adlo), a ∈ as → atom_type.dep0 β a ∧ ¬ atom_eq_type.solv0 β a) 
  → qe_prsv β (dlo_qe β) as := 
begin
  intros as Has,
  unfold qe_prsv, intro bs, 
  unfold dlo_qe, unfold dlo_qe_aux, simp, 
  cases (@list.decidable_mem adlo (atom_type.dec_eq _ β) (0 <' 0) as) with Hc Hc,
  rewrite (exp_ite_false), 
 
  have HW : allp is_b_atm as := 
  begin
    apply allp_of_allp is_b_atm_of, intros a' Ha', 
    cases Has a' Ha' with Ha1' Ha2',
    apply and.intro Ha1',  
    apply and.intro Ha2', intro HN, 
    apply Hc, subst HN, apply Ha'  
  end, clear Has, clear Hc, 

  rewrite (exp_ite_true), 
  unfold function.comp, rewrite exp_I_list_conj,  

  apply @classical.by_cases (∃ m, is_lb m as) ; intro Hlb,
  cases (ex_high_lb_of_ex_lb Hlb bs) with m Hm, clear Hlb,
  cases Hm with Hm1 Hm2, 

  apply @classical.by_cases (∃ n, is_ub n as) ; intro Hub,
  cases (ex_low_ub_of_ex_ub Hub bs) with n Hn, clear Hub,
  cases Hn with Hn1 Hn2, 

  apply @iff.trans _ (I (A' (m <' n)) bs),
  rewrite map_compose,
  apply iff.intro, intro HL, apply HL, 
  apply @mem_map_of_mem _ _ (λ (x : ℕ × ℕ), I ((fm.atom ∘ λ (pr : ℕ × ℕ), pr.fst<' pr.snd) x) bs) _ (m,n),  
  apply mem_product_of_mem_of_mem,
  apply mem_omap _ Hm1, refl, 
  apply mem_omap _ Hn1, refl, 
  intro HR, intros a Ha, 
  cases (ex_arg_of_mem_map Ha) with pr Hpr,
  cases Hpr with Hpr1 Hpr2, subst Hpr2,
  cases pr with x y, simp, simp at Ha, 
  cases (ex_arg_of_mem_map Ha) with xy Hxy, 
  cases xy with x' y', simp at Hxy,
  cases Hxy with Hxy1 Hxy2, rewrite Hxy2,
  apply lt_of_le_of_lt (Hm2 _ _), 
  apply lt_of_lt_of_le _ (Hn2 _ _), 
  apply HR, 
  have Hy := snd_mem_of_mem_product Hxy1, simp at Hy,
  apply is_ub_of_mem_ubs, apply Hy, 
  have Hx := fst_mem_of_mem_product Hxy1, simp at Hx,
  apply is_lb_of_mem_lbs, apply Hx, 
  apply iff.intro; intro H, 
  cases (btw_of_lt H) with b Hb, cases Hb with Hb1 Hb2,
  existsi b, intros a Ha, 

  cases (HW a Ha) with k Ha', cases Ha' with Ha' Ha'; subst Ha',
  unfold I, unfold interp, rewrite exp_val_lt,
  rewrite nth_dft_succ, rewrite nth_dft_head, 
  apply lt_of_le_of_lt, 
  apply (Hm2 k Ha), apply Hb1,
  unfold I, unfold interp, rewrite exp_val_lt,
  rewrite nth_dft_succ, rewrite nth_dft_head, 
  apply lt_of_lt_of_le, 
  apply Hb2, apply (Hn2 k Ha), 
  cases H with b Hb, unfold I, unfold interp,
  have HE := (atom_type.decr_prsv (m+1 <' n+1) _ b bs),
  rewrite (exp_decr_lt (m+1) (n+1)) at HE, simp at HE,
  rewrite HE, clear HE, 
  apply lt_trans, 
  let Hbm := Hb _ Hm1, 
  unfold I at Hbm, unfold interp at Hbm, apply Hbm,
  let Hbn := Hb _ Hn1, 
  unfold I at Hbn, unfold interp at Hbn, apply Hbn,
  intro Hc', cases Hc' with Hc' Hc'; cases Hc', 

  apply true_iff_true,  
  rewrite (ubs_eq_nil_of_none_is_ub Hub), 
  rewrite product_nil, simp, apply all_true_nil,
  cases (dlo.abv (tval m bs)) with u Hu, 
  existsi u, intros a Ha, 
  cases (HW a Ha) with k Ha', cases Ha' with Ha' Ha'; subst Ha',
  unfold I, unfold interp, rewrite exp_val_lt,
  rewrite nth_dft_succ, rewrite nth_dft_head, 
  apply lt_of_le_of_lt, 
  apply (Hm2 k Ha), apply Hu, 
  exfalso, apply Hub, existsi k, apply Ha,

  apply @classical.by_cases (∃ n, is_ub n as) ; intro Hub,
  cases (ex_low_ub_of_ex_ub Hub bs) with n Hn, clear Hub,
  cases Hn with Hn1 Hn2, 

  apply true_iff_true,  
  rewrite (lbs_eq_nil_of_none_is_lb Hlb), 
  simp, apply all_true_nil, 
  cases (dlo.blw (tval n bs)) with l Hl, 
  existsi l, intros a Ha, 
  cases (HW a Ha) with k Ha', cases Ha' with Ha' Ha'; subst Ha',
  exfalso, apply Hlb, existsi k, apply Ha,
  unfold I, unfold interp, rewrite exp_val_lt,
  rewrite nth_dft_succ, rewrite nth_dft_head, 
  apply lt_of_lt_of_le, apply Hl,
  apply (Hn2 k Ha), 
  
  cases as with a, simp, unfold dlo_qe_lbs, 
  unfold list.omap, unfold list.product, 
  unfold list.map, apply true_iff_true,
  intros _ Hx, cases Hx, existsi (@dlo.inh β HD), 
  trivial, cases (HW _ (or.inl rfl)) with k Hk,
  cases Hk with Hk Hk, 
  exfalso, apply Hlb, existsi k, subst Hk, apply or.inl rfl, 
  exfalso, apply Hub, existsi k, subst Hk, apply or.inl rfl, 
  apply HW, apply Hc, 

  rewrite exp_ite_true, apply false_iff_false,
  intro h, apply h, 
  intro h, cases h with b hb, 
  apply (lt_irrefl b), 
  apply (hb _ Hc), apply Hc

end

lemma dlo_qelim_prsv [dlo β] : 
  ∀ (p : fm adlo) (bs : list β), I (dlo_qelim β p) bs ↔ I p bs := 
ldeq_prsv (dlo_qe β) dlo_qe_qfree dlo_qe_is_dnf 
