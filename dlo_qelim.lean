import .dlo 

variables {α β : Type}

#check @list.map

def dlo_qe_aux (as) (HZ) (H) := 
let lbsrbs := dlo_qe_split as (allp_single_0_of as H HZ) in 
let prs := list.product lbsrbs^.fst lbsrbs^.snd in 
list_conj $ @list.map adlo (fm adlo) (@fm.atom adlo) (list.map (λ pr, (prod.fst pr <' prod.snd pr)) prs)

def dlo_qe (β : Type) [atomeq adlo β] (as : list adlo) : fm adlo := 
@dite (adlo.lt 0 0 ∈ as) 
  (@list.decidable_mem adlo (atom.dec_eq _ β) (0 <' 0) _) _ 
  (λ _, ⊥')
  (λ HZ, @dite (allp lt_has_0 as) 
    (decidable_allp _) _ 
    (dlo_qe_aux as HZ)
    (λ _, ⊥')
  )

def dlo_qelim (β : Type) [atomeq adlo β] : fm adlo → fm adlo :=  
@lift_dnfeq_qe _ β _ (dlo_qe β)

-- Q : Why doesn't `cases (dlo_dec_mem (0 <' 0) as)` simplify things here? 
lemma dlo_qe_qfree [HA : atomeq adlo β] : 
  ∀ (as : list adlo) (Has : allp (@atom.dep0 adlo β _) as), 
    qfree (dlo_qe β as) := 
begin
  intros as Has, unfold dlo_qe, 
  apply cases_dite, intro H, trivial, 
  intro HM, 
  apply cases_dite, intro Hlt, 
  unfold dlo_qe_aux,
  simp, apply list_conj_qfree,
  intros x Hx, 
  cases (exp_mem_map Hx) with y Hy,
  cases Hy with Hyl Hyr, rewrite Hyr,
  cases y, unfold function.comp, 
  intro H, trivial
end

lemma exp_dlo_qe [atomeq adlo β] {as} 
  (Has : ∀ (a : adlo), a ∈ as → atom.dep0 β a ∧ ¬atomeq.solv0 β a) {xs : list β} :
∃ H HZ, dlo_qe β as = @dlo_qe_aux as HZ H := sorry

def is_lb (m) (as : list adlo) := (m+1 <' 0) ∈ as
def is_ub (n) (as : list adlo) := (0 <' n+1) ∈ as

lemma ex_high_lb_of_ex_lb [dlo β] {as : list adlo} (Hlb : ∃ m, is_lb m as) (bs : list β) :
∃ k, (is_lb k as ∧ ∀ j, is_lb j as → tval j bs ≤ tval k bs) := sorry

lemma ex_low_ub_of_ex_ub [dlo β] {as : list adlo} (Hub : ∃ n, is_ub n as) (bs : list β) :
∃ k, (is_ub k as ∧ ∀ j, is_ub j as → tval k bs ≤ tval j bs) := sorry
/-
lemma no_lb_or_ex_high_lb [dlo β] (as : list adlo) (bs : list β) : 
  (∀ m, ¬ is_lb m as) 
  ∨ (∃ m, is_lb m as 
          ∧ ∀ k, is_lb k as → tval k bs ≤ tval m bs) := sorry 

lemma no_ub_or_ex_low_ub [dlo β] (as : list adlo) (bs : list β) : 
  (∀ n, ¬ is_ub n as) 
  ∨ (∃ n, is_ub n as 
          ∧ ∀ k, is_ub k as → tval n bs ≤ tval k bs) := sorry 

lemma eq_nil_of_no_bound {as} (Hlt : allp lt_has_0 as)
 (Hlb : ∀ (m : ℕ), ¬is_lb m as) (Hub : ∀ (n : ℕ), ¬is_ub n as) : as = [] :=
begin
  cases as with a' as', refl, cases a' with x y x y,
  cases x with x, exfalso, apply Hub y, apply or.inl, refl,
  cases y with y, exfalso, apply Hlb, 
  apply or.inl, refl, exfalso,
  apply (Hlt _ (or.inl (by refl))),
  exfalso, apply (Hlt _ (or.inl (by refl)))
end
-/ 

#check @classical.by_cases
lemma dlo_qe_is_dnf [dlo β] [atomeq adlo β] : ∀ (as : list adlo), 
  (∀ (a : adlo), a ∈ as → atom.dep0 β a ∧ ¬ atomeq.solv0 β a) 
  → is_dnf_qe β (dlo_qe β) as := 
begin
  intros as Has, unfold is_dnf_qe, intro bs, 
  cases (exp_dlo_qe Has) with H1 H2,
  cases H2 with H2 H3, rewrite H3, 
  unfold dlo_qe_aux, simp, 

  apply @classical.by_cases (∃ m, is_lb m as) ; intro Hlb,
  apply @classical.by_cases (∃ n, is_ub n as) ; intro Hub,
  
  cases (ex_high_lb_of_ex_lb Hlb bs) with m Hm, clear Hlb,
  cases (ex_low_ub_of_ex_ub Hub bs) with n Hn, clear Hub,
  apply @eq.trans _ _ (I (A' (m <' n)) bs),
  rewrite exp_I_list_conj,
  rewrite map_compose, apply propext, 
  apply iff.intro, intro HL, apply HL, 
  apply @mem_map_of_mem _ _ (λ (x : ℕ × ℕ), I ((fm.atom ∘ λ (pr : ℕ × ℕ), pr.fst<' pr.snd) x) bs) _ (m,n),  
  apply mem_product_of_mem_of_mem,

  -- cases (no_lb_or_ex_high_lb as bs) with Hlb Hlb,
  --cases (no_ub_or_ex_low_ub as bs) with Hub Hub,

  --cases as with a' as',
  --simp, unfold dlo_qe_split, simp, 
  --unfold list.product, unfold list.map,
  --unfold list_conj, rewrite exp_I_top, 
  --apply eq.symm, rewrite eq_true,
  --existsi (atom.inh adlo β), trivial, 

  --cases (eq_nil_of_no_bound H1 Hlb Hub),

end
#check @mem_map_of_mem

lemma dlo_qelim_prsv_core [dlo β] [atomeq adlo β] : 
  ∀ (p : fm adlo) (bs : list β), I (dlo_qelim β p) bs = I p bs := 
ldeq_prsv (dlo_qe β) dlo_qe_qfree dlo_qe_is_dnf 