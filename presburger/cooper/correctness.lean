import .qe

open pbgr

lemma hco_le_nonzero (m i k : int) (ks) : 
  k ≠ 0 → 
  hd_coeff_one m (atom.le i (k::ks)) = 
  (let m' := int.div m (abs k) in 
   atom.le (m' * i) (int.sign k :: list.map (λ x, m' * x) ks)) :=
begin
  intro hne, cases k with n n, cases n, trivial, 
  trivial, trivial, 
end

lemma hco_dvd_nonzero (m d i k ks) : 
  k ≠ 0 → 
  hd_coeff_one m (atom.dvd d i (k::ks)) = 
 (let m' := int.div m k in 
  atom.dvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)) := 
begin
  intro hne, cases k with n n, cases n, trivial, 
  trivial, trivial, 
end

lemma hco_ndvd_nonzero (m d i k ks) : 
  k ≠ 0 → 
  hd_coeff_one m (atom.ndvd d i (k::ks)) = 
 (let m' := int.div m k in 
  atom.ndvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)) := 
begin
  intro hne, cases k with n n, cases n, trivial, 
  trivial, trivial, 
end

lemma normal_hco_atom
(z : int)
(hne : z ≠ 0) :
∀ (a : atom)
(ha1 : atom_type.normal ℤ a)
(ha2 : has_dvd.dvd (hd_coeff a) z ∨ hd_coeff a = 0),
 atom_type.normal ℤ (hd_coeff_one z a) 
| (atom.le i ks) ha1 ha2 := 
  begin
    cases ks with k ks, trivial, cases k with n, 
    cases n; trivial, trivial
  end
| (atom.dvd d i ks) ha1 ha2 := 
  begin
    cases ks with k ks, trivial, 
    cases (classical.em (k = 0)) with hk hk, 
    subst hk, trivial, 
    cases ha2 with ha2 ha2,
    rewrite hco_dvd_nonzero, simp,
    apply int.mul_nonzero, 
    unfold hd_coeff at ha2,
    unfold list.head_dft at ha2,
    apply int.div_nonzero, apply hne, apply ha2, 
    apply ha1, apply hk, 
    exfalso, apply hk ha2
  end
| (atom.ndvd d i ks) ha1 ha2 := 
  begin
    cases ks with k ks, trivial, 
    cases (classical.em (k = 0)) with hk hk, 
    subst hk, trivial, 
    cases ha2 with ha2 ha2,
    rewrite hco_ndvd_nonzero, simp,
    apply int.mul_nonzero, 
    unfold hd_coeff at ha2,
    unfold list.head_dft at ha2,
    apply int.div_nonzero, apply hne, apply ha2, 
    apply ha1, apply hk,   
    exfalso, apply hk ha2 
  end

meta def fnormal_map_hco_of_fnormal_tac :=
 `[unfold map_fm, unfold fnormal,
   cases hn with hnp hnq, unfold atoms at hnz, 
   rewrite list.forall_mem_union at hnz,
   cases hnz with hnzp hnzq,  apply and.intro; 
   apply fnormal_map_hco_of_fnormal; assumption]

lemma fnormal_map_hco_of_fnormal (z : int) (hz : z ≠ 0) :
  ∀ (p : fm atom), (fnormal ℤ p) 
  → (∀ a ∈ atoms p, has_dvd.dvd (hd_coeff a) z ∨ hd_coeff a = 0) 
  → fnormal ℤ (map_fm (hd_coeff_one z) p)  
| ⊤' hn hnz := by unfold map_fm 
| ⊥' hn hnz := by unfold map_fm 
| (A' a) hn hnz := 
  begin
    unfold map_fm, unfold fnormal, unfold fnormal at hn,
    apply normal_hco_atom z hz _ hn, apply hnz, 
    unfold atoms, simp,
  end
| (p ∧' q) hn hnz := by fnormal_map_hco_of_fnormal_tac
| (p ∨' q) hn hnz := by fnormal_map_hco_of_fnormal_tac
| (¬' p) hp hpz :=
  begin
    unfold map_fm, unfold fnormal, 
    apply fnormal_map_hco_of_fnormal p hp hpz,
  end
| (∃' p) hn hnz := by unfold map_fm

lemma hd_coeffs_one_normal_prsv : 
  preserves hd_coeffs_one (fnormal int) := 
begin
  intros p hp, unfold hd_coeffs_one, simp, 
  unfold fnormal, 
  have hne : int.zlcms (list.map hd_coeff (atoms_dep0 ℤ p)) ≠ 0, 
  apply int.zlcms_neq_zero, 
  apply @list.forall_mem_map_of_forall_mem _ _ 
          (atom_type.dep0 int) 
          (λ (z : int), z ≠ 0) 
          hd_coeff 
          (atoms_dep0 int p), 
  unfold atoms_dep0, intros a ha,
  apply list.of_mem_filter ha,
  intros a ha, apply ha, 
  apply and.intro, intro hc, apply hne hc,
  apply fnormal_map_hco_of_fnormal _ hne _ hp, 
  intros a ha, apply or_of_not_imp_right,
  intro haz, apply int.dvd_zlcms, apply haz,
  rewrite list.mem_map, existsi a, apply and.intro,
  unfold atoms_dep0, apply list.mem_filter_of_mem,
  apply ha, apply haz, refl
end

lemma normal_asubst_of_normal :
  ∀ a : atom, atom_type.normal int a 
    → ∀ i ks, atom_type.normal int (asubst i ks a) := 
begin
  intro a, cases a with i ks d i ks d i ks; 
  intros h i' ks'; cases ks with k ks; trivial
end

lemma fnormal_subst_of_fnormal (i ks) : 
  ∀ p, fnormal int p → fnormal int (subst i ks p) 
| ⊤' h := by unfold subst
| ⊥' h := by unfold subst
| (A' a) h :=
  begin
    unfold subst, unfold map_fm,
    unfold fnormal, apply normal_asubst_of_normal _ h
  end
| (p ∧' q) h := 
  begin
    cases h with hp hq, apply and.intro; 
    apply fnormal_subst_of_fnormal; assumption
  end
| (p ∨' q) h := 
  begin
    cases h with hp hq, apply and.intro; 
    apply fnormal_subst_of_fnormal; assumption
  end
| (¬' p) h := fnormal_subst_of_fnormal p h
| (∃' p) h := by unfold subst



meta def nqfree_hco_of_nqfree_tac := 
`[unfold map_fm, cases h with hp hq, apply and.intro; 
  apply nqfree_hco_of_nqfree; assumption]

lemma nqfree_hco_of_nqfree (z) : 
  ∀ (p : fm atom), nqfree p → nqfree (map_fm (hd_coeff_one z) p) 
| ⊤' h := by unfold map_fm
| ⊥' h := by unfold map_fm
| (A' _) h := by unfold map_fm
| (p ∧' q) h := by nqfree_hco_of_nqfree_tac
| (p ∨' q) h := by nqfree_hco_of_nqfree_tac
| (¬' _) h := by cases h
| (∃' _) h := by unfold map_fm

lemma nqfree_hcso_of_nqfree : 
  ∀ (p : fm atom), nqfree p → nqfree (hd_coeffs_one p) :=
begin
  intros p h, unfold hd_coeffs_one, simp,
  apply and.intro, trivial, 
  apply nqfree_hco_of_nqfree _ _ h
end

lemma qfree_subst_of_qfree (i ks) : 
  ∀ p, qfree p → qfree (subst i ks p) 
| ⊤' h := by unfold subst
| ⊥' h := by unfold subst
| (A' a) h := by unfold subst
| (p ∧' q) h := 
  begin
    cases h with hp hq, apply and.intro,
    apply qfree_subst_of_qfree p hp,
    apply qfree_subst_of_qfree q hq
  end
| (p ∨' q) h := 
  begin
    cases h with hp hq, apply and.intro,
    apply qfree_subst_of_qfree p hp,
    apply qfree_subst_of_qfree q hq
  end
| (¬' p) h := qfree_subst_of_qfree p h
| (∃' p) h := by unfold subst

lemma pred_inf_minus_of_pred (P) (hup : prop_up_closed P) 
  (hdn : down_closed P) : ∀ p, P p → P (inf_minus p)
| ⊤' h := h
| ⊥' h := h
| (A' a) h := 
  begin
    cases a with k ks, cases ks with k' ks, apply h,
    unfold inf_minus, apply cases_ite; intro h1,
    apply hup ⊤', apply cases_ite; intro h2, apply hup ⊥', 
    rewrite int.eq_zero_of_not_gt_zero_of_not_lt_zero k' h1 h2 at h,
    apply h, apply h, apply h
  end
| (p ∧' q) h := 
  begin
    unfold inf_minus, apply pred_and_o _ hup;
    apply pred_inf_minus_of_pred; 
    apply hdn _ _ _ h; constructor
  end
| (p ∨' q) h := 
  begin
    unfold inf_minus, apply pred_or_o _ hup;
    apply pred_inf_minus_of_pred; 
    apply hdn _ _ _ h; constructor
  end
| (¬' p) h := h
| (∃' p) h := h

lemma qfree_inf_minus_of_qfree : 
  ∀ p, qfree p → qfree (inf_minus p) :=
  pred_inf_minus_of_pred _ prop_up_closed_qfree down_closed_qfree

lemma fnormal_inf_minus_of_fnormal : 
  ∀ p, fnormal int p → fnormal int (inf_minus p) :=
  pred_inf_minus_of_pred _ prop_up_closed_fnormal down_closed_fnormal

lemma qe_cooper_one_normal_prsv : preserves qe_cooper_one (fnormal int) := 
begin
  unfold preserves, intros p hp, 
  unfold qe_cooper_one, simp,
  apply fnormal_or_o, apply fnormal_disj,
  intros z hz, apply fnormal_subst_of_fnormal,
  apply fnormal_inf_minus_of_fnormal, apply hp,
  apply fnormal_disj, intros zzs hzzs,
  apply fnormal_disj, intros z hz,
   apply fnormal_subst_of_fnormal, apply hp
end

lemma sqe_cooper_normal_prsv : preserves sqe_cooper (fnormal int) := 
begin
  intros p hp, unfold sqe_cooper,
  apply qe_cooper_one_normal_prsv,
  apply hd_coeffs_one_normal_prsv, 
  apply hp
end

lemma qfree_qco_of_nqfree : qfree_res_of_nqfree_arg qe_cooper_one := 
begin
  unfold qfree_res_of_nqfree_arg, intros p hp,
  unfold qe_cooper_one, simp,
  apply qfree_or_o; apply qfree_disj,

  intros z hz, apply qfree_subst_of_qfree,
  apply qfree_inf_minus_of_qfree,
  apply qfree_of_nqfree _ hp,

  intros zzs hzzs, apply qfree_disj,
  intros z hz, apply qfree_subst_of_qfree,
  apply qfree_of_nqfree _ hp
end

lemma qfree_sqe_cooper_of_nqfree : qfree_res_of_nqfree_arg sqe_cooper := 
begin
  unfold qfree_res_of_nqfree_arg, unfold sqe_cooper, 
  intros p h, apply qfree_qco_of_nqfree,
  apply nqfree_hcso_of_nqfree, apply h
end

def unified (p : fm atom) : Prop := 
  ∀ a ∈ atoms p, hd_coeff a = -1 ∨ hd_coeff a = 0 ∨ hd_coeff a = 1

lemma unfied_hd_coeff : ∀ (a : atom) (z : int),
  hd_coeff (hd_coeff_one z a) = -1
∨ hd_coeff (hd_coeff_one z a) = 0 
∨ hd_coeff (hd_coeff_one z a) = 1 := 
begin
  intros a z, cases a with i ks d i ks d i ks; cases ks with k ks, 
    
   apply or.inr (or.inl rfl), 

   cases (classical.em (k = 0)) with hk hk, subst hk,

     apply or.inr (or.inl rfl),

     rewrite hco_le_nonzero _ _ _ _ hk, simp,
     unfold hd_coeff, unfold list.head_dft, 
     apply int.sign_split,
  
   apply or.inr (or.inl rfl), 

   cases (classical.em (k = 0)) with hk hk, subst hk,

     apply or.inr (or.inl rfl),

     rewrite hco_dvd_nonzero _ _ _ _ _ hk, simp,
     unfold hd_coeff, unfold list.head_dft, simp,

   apply or.inr (or.inl rfl), 

   cases (classical.em (k = 0)) with hk hk, subst hk,

     apply or.inr (or.inl rfl),

    rewrite hco_ndvd_nonzero _ _ _ _ _ hk, simp,
    unfold hd_coeff, unfold list.head_dft, simp
end

lemma ex_iff_inf_or_bnd (P : int → Prop) :
  (∃ z, P z) ↔ ((∀ y, ∃ x, x < y ∧ P x) ∨ (∃ y, (P y ∧ ∀ x, x < y → ¬ P x))) := 
sorry

lemma unified_hd_coeffs_one :
  ∀ p, unified (hd_coeffs_one p) :=
begin
  intro p, unfold hd_coeffs_one, simp,
  unfold unified, unfold atoms, simp,
  apply and.intro, apply or.inr (or.inr rfl),
  intros a ha, rewrite atoms_map_fm at ha,
  rewrite list.mem_map at ha, cases ha with a' ha',
  cases ha' with h1 h2, subst h2,
  apply unfied_hd_coeff
end

lemma inf_minus_prsv (p : fm atom) :
  ∃ (y : int), ∀ x, x < y → ∀ (zs : list int), 
    (I (inf_minus p) zs ↔ I p zs) := sorry

lemma inf_minus_decr (p : fm atom) (z : int) (zs) :
  I (inf_minus p) (z::zs) 
  → I (inf_minus p) ((z - coeffs_lcm p)::zs) := sorry 

lemma inf_minus_incr (p : fm atom) (z : int) (zs) :
  I (inf_minus p) (z::zs) 
  → I (inf_minus p) ((z + coeffs_lcm p)::zs) := sorry 

lemma pos_coeffs_lcm (p : fm atom) :
  coeffs_lcm p > 0 := sorry

lemma pos_divisors_lcm (p : fm atom) :
  divisors_lcm p > 0 := sorry

lemma no_lb_inf_minus (p : fm atom) (z : int) (zs) :
  I (inf_minus p) (z::zs) 
  → ∀ y, ∃ x, (x < y ∧ I (inf_minus p) (x::zs)) := sorry

lemma inf_minus_mod : 
  ∀ p z bs, 
  (I (inf_minus p) (z :: bs)) ↔ 
  (I (inf_minus p) (int.mod z (divisors_lcm p) :: bs)) := sorry

lemma qe_cooper_one_prsv :  
  ∀ (p : fm atom), nqfree p → fnormal ℤ p → unified p
  → ∀ (bs : list ℤ), I (qe_cooper_one p) bs ↔ ∃ (b : ℤ), I p (b :: bs) := 
begin
  intros p hf hn hu bs,
  unfold qe_cooper_one, simp, 
  rewrite exp_I_or_o,  
  apply iff.intro; intro h, 
  cases h with h h, unfold disj at h,
  rewrite I_list_disj at h, cases h with q hq,
  cases hq with hq1 hq2, 
  rewrite list.mem_map at hq1, 
  cases hq1 with r hr, 
  rewrite list.mem_map at hr, cases hr with hr1 hr2,
  subst hr2, cases hr1 with z hz, cases hz with hz1 hz2,
  subst hz2, rewrite subst_prsv at hq2,
  rewrite list.nil_dot_prod at hq2,
  rewrite add_zero at hq2,
  
  cases (inf_minus_prsv p) with lb hlb,

  cases (no_lb_inf_minus p z bs hq2 lb) with x hx,
  cases hx with hx1 hx2, 

  rewrite (hlb x hx1 (x::bs)) at hx2,
  existsi x, apply hx2, 

  unfold disj at h, rewrite I_list_disj at h,
  cases h with q hq, rewrite list.mem_map at hq,
  cases hq with r hr, cases r with s hs,
  rewrite list.mem_map at hs, cases hs with h1 h2,
  cases h1 with zzs hzzs, cases hzzs with h2 h3,
  subst h3, subst h2, rewrite I_list_disj at hr,
  cases hr with t ht, rewrite list.mem_map at ht,
  cases ht with v hv, cases v with w hw,
  rewrite list.mem_map at hw, cases hw with hw1 hw2,
  subst hw2, cases hw1 with z hz, cases hz with hz1 hz2,
  subst hz2, rewrite subst_prsv at hv,
  constructor, apply hv, 

  rewrite ex_iff_inf_or_bnd at h, cases h with h h,
  apply or.inl, cases (inf_minus_prsv p) with lb hlb,
  cases (h lb) with x hx, cases hx with hx1 hx2, 
  rewrite iff.symm (hlb x hx1 (x::bs)) at hx2, 
  unfold disj, rewrite I_list_disj, simp, 
  unfold function.comp,
  existsi (I (inf_minus p) ( (int.mod x (divisors_lcm p)) :: bs)),
  apply and.intro, rewrite list.mem_map, 
  existsi (int.mod x (divisors_lcm p)), apply and.intro,
  apply list.mem_irange,
  apply int.mod_nonneg,
  apply int.neq_zero_of_gt_zero, apply pos_divisors_lcm,
  unfold divisors_lcm, apply int.mod_lt_of_pos, 
  apply pos_divisors_lcm, 
  rewrite subst_prsv, rewrite list.nil_dot_prod,
  rewrite add_zero, rewrite inf_minus_mod at hx2,
  apply hx2,
  cases h with lb hlb, cases hlb with hlb1 hlb2, 
  apply or.inr, unfold disj,

end


#check get_lb
lemma hd_coeffs_one_prsv :  
∀ (p : fm atom) (hf : nqfree p) (hn : fnormal ℤ p) (bs : list ℤ),
(∃ (b : ℤ), I (hd_coeffs_one p) (b :: bs)) ↔ ∃ (b : ℤ), I p (b :: bs) :=
sorry

lemma sqe_cooper_prsv :  
  ∀ (p : fm atom), nqfree p → fnormal ℤ p 
  → ∀ (bs : list ℤ), I (sqe_cooper p) bs ↔ ∃ (b : ℤ), I p (b :: bs) := 
begin
  intros p hf hn bs, unfold sqe_cooper, 
  rewrite qe_cooper_one_prsv,
  apply hd_coeffs_one_prsv p hf hn bs, 
  apply nqfree_hcso_of_nqfree p hf,
  apply hd_coeffs_one_normal_prsv _ hn,
  apply unified_hd_coeffs_one
end

lemma qe_cooper_prsv : 
  ∀ p, fnormal int p → ∀ (bs : list int), I (qe_cooper p) bs ↔ I p bs :=
  @pbgr.lnq_prsv sqe_cooper 
    sqe_cooper_normal_prsv 
    qfree_sqe_cooper_of_nqfree 
    sqe_cooper_prsv
    
  
