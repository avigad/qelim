import .qe

open pbgr

lemma I_atom_le (i ks zs) : 
  I (A' (atom.le i ks)) zs ↔ (i ≤ list.dot_prod ks zs) := sorry

lemma I_atom_dvd (d i ks zs) : 
  I (A' (atom.dvd d i ks)) zs ↔ (has_dvd.dvd d (i + list.dot_prod ks zs)) := sorry

lemma I_atom_ndvd (d i ks zs) : 
  I (A' (atom.ndvd d i ks)) zs ↔ ¬ (has_dvd.dvd d (i + list.dot_prod ks zs)) := sorry
  
lemma le_dep0_split (i ks) : 
  (¬ atom_type.dep0 int (atom.le i ks)) 
  ∨ ∃ k, ∃ ks', (k ≠ 0 ∧ ks = (k::ks')) := sorry

lemma dvd_dep0_split (d i ks) : 
  (¬ atom_type.dep0 int (atom.dvd d i ks)) 
  ∨ ∃ k, ∃ ks', (k ≠ 0 ∧ ks = (k::ks')) := sorry

lemma ndvd_dep0_split (d i ks) : 
  (¬ atom_type.dep0 int (atom.ndvd d i ks)) 
  ∨ ∃ k, ∃ ks', (k ≠ 0 ∧ ks = (k::ks')) := sorry

lemma hco_not_dep0 (m a) : 
  (¬ atom_type.dep0 int a) → hd_coeff_one m a = a := sorry

lemma hco_le_nonzero (m i k : int) (ks) : 
  k ≠ 0 → 
  hd_coeff_one m (atom.le i (k::ks)) = 
  (let m' := has_div.div m (abs k) in 
   atom.le (m' * i) (int.sign k :: list.map (λ x, m' * x) ks)) :=
begin
  intro hne, cases k with n n, cases n, trivial, 
  trivial, trivial, 
end

lemma hco_dvd_nonzero (m d i k ks) : 
  k ≠ 0 → 
  hd_coeff_one m (atom.dvd d i (k::ks)) = 
 (let m' := has_div.div m k in 
  atom.dvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)) := 
begin
  intro hne, cases k with n n, cases n, trivial, 
  trivial, trivial, 
end

lemma hco_ndvd_nonzero (m d i k ks) : 
  k ≠ 0 → 
  hd_coeff_one m (atom.ndvd d i (k::ks)) = 
 (let m' := has_div.div m k in 
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
  intros p hp, unfold hd_coeffs_one, 
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
  intros p h, unfold hd_coeffs_one,
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

lemma mem_bnd_points_and (p q) : 
  ∀ b, ((b ∈ bnd_points p ∨ b ∈ bnd_points q) → b ∈ bnd_points (p ∧' q)) := sorry

lemma unified_hd_coeffs_one :
  ∀ p, unified (hd_coeffs_one p) :=
begin
  intro p, unfold hd_coeffs_one,
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

lemma coeffs_lcm_atom_le (i k : int) (ks : list int) :
  k ≠ 0 → coeffs_lcm (A' (atom.le i (k::ks))) = abs k := sorry

lemma coeffs_lcm_atom_dvd (d i k : int) (ks : list int) :
  k ≠ 0 → coeffs_lcm (A' (atom.dvd d i (k::ks))) = abs k := sorry

lemma coeffs_lcm_atom_ndvd (d i k : int) (ks : list int) :
  k ≠ 0 → coeffs_lcm (A' (atom.ndvd d i (k::ks))) = abs k := sorry

lemma coeffs_lcm_and (p q) :
  coeffs_lcm (p ∧' q) = int.lcm (coeffs_lcm p) (coeffs_lcm q) := sorry

lemma no_lb_inf_minus (p : fm atom) (z : int) (zs) :
  I (inf_minus p) (z::zs) 
  → ∀ y, ∃ x, (x < y ∧ I (inf_minus p) (x::zs)) := sorry

lemma inf_minus_mod : 
  ∀ p z bs, 
  (I (inf_minus p) (z :: bs)) ↔ 
  (I (inf_minus p) (int.mod z (divisors_lcm p) :: bs)) := sorry

lemma atom_dvd_mod : 
  ∀ d i ks z zs, 
  (I (A' (atom.dvd d i ks)) (z :: zs)) ↔ 
  (I (A' (atom.dvd d i ks)) (int.mod z d :: zs)) := sorry

lemma atom_ndvd_mod : 
  ∀ d i ks z zs, 
  (I (A' (atom.ndvd d i ks)) (z :: zs)) ↔ 
  (I (A' (atom.ndvd d i ks)) (int.mod z d :: zs)) := sorry


lemma divisors_lcm_dvd_and_left (p q) : 
  has_dvd.dvd (divisors_lcm p) (divisors_lcm (p ∧' q)) := sorry

lemma divisors_lcm_dvd_and_right (p q) : 
  has_dvd.dvd (divisors_lcm q) (divisors_lcm (p ∧' q)) := sorry

lemma divisors_lcm_dvd_or (p q) : 
  has_dvd.dvd (divisors_lcm p) (divisors_lcm (p ∨' q)) := sorry

lemma mod_add_eq_mod (i j k) : (has_dvd.dvd k j) → int.mod (i + j) k = int.mod i k := sorry

lemma le_hd_coeff_decr {y z i k : int} {zs ks : list int} :
k < 0 → y < z 
→ I (A' atom.le i (k :: ks)) (z :: zs)
→ I (A' atom.le i (k :: ks)) (y :: zs) := sorry

lemma qe_cooper_one_prsv_lb (z : ℤ) (zs : list ℤ) :
∀ (p : fm atom), nqfree p → fnormal ℤ p → unified p 
  → ∀ k, 0 < k → (has_dvd.dvd (divisors_lcm p) k) 
    → ¬ I p (z :: zs) → I p ((z + k)::zs)
    → ∃ (k' : int), ∃ iks, iks ∈ bnd_points p
        ∧ (0 ≤ k' 
        ∧ k' < k 
        ∧ z + k = (k' + (prod.fst iks) + list.dot_prod (map_neg (prod.snd iks)) zs)) 
| ⊤' hf hn hu k _ hk h1 h2 := by trivial
| ⊥' hf hn hu k _ hk h1 h2 := by trivial
| (A' (atom.le i ks)) hf hn hu k hkp hk h1 h2 := 
  begin
    cases (atom_type.dec_dep0 atom int (atom.le i ks)) with hdep hdep,
    
    unfold I at h1, unfold interp at h1, 
    rewrite iff.symm (atom_type.decr_prsv atom int) at h1,
    unfold I at h2, unfold interp at h2, 
    rewrite iff.symm (atom_type.decr_prsv atom int) at h2,
    exfalso, apply h1 h2, apply hdep, apply hdep,
    
    cases ks with k' ks', exfalso, apply hdep, refl,
  
    cases (hu (atom.le i (k' :: ks')) _) with hu1 hu2,
    unfold hd_coeff at hu1, unfold list.head_dft at hu1,
    subst hu1,
    exfalso, apply h1, 
    apply le_hd_coeff_decr _ _ h2, 
    apply int.pred_self_lt,
    apply int.lt_add_of_pos k z hkp,
    cases hu2 with hu2 hu2,
    unfold hd_coeff at hu2, 
    unfold list.head_dft at hu2, 
    subst hu2, exfalso, apply hdep, refl,

    unfold hd_coeff at hu2, 
    unfold list.head_dft at hu2, 
    subst hu2, 
    existsi ((z + k) - (i + list.dot_prod (map_neg (ks')) zs)),
    existsi (i,ks'),
    apply and.intro, apply or.inl rfl, 
    apply and.intro, unfold map_neg,

    rewrite list.neg_dot_prod,
    rewrite sub_add_eq_sub_sub, 
    rewrite sub_neg_eq_add, 
    unfold I at h2, unfold interp at h2, 
    have hv : i ≤ list.dot_prod (1::ks') ((z + k) :: zs),
    apply h2, rewrite list.cons_dot_prod_cons at hv,
    rewrite iff.symm (sub_le_sub_iff_right i) at hv,
    simp at hv, simp, apply hv,

    apply and.intro,

    have hv : ¬ (i ≤ list.dot_prod (1::ks') (z:: zs)),
    apply h1, rewrite not_le at hv, 
    rewrite list.cons_dot_prod_cons at hv, 
    unfold map_neg, rewrite list.neg_dot_prod,
    simp at hv, 
    have hv' := add_lt_add_right (sub_lt_sub_right hv i) k,
    simp at hv', simp, apply hv',

    simp, rewrite add_comm k (-i), 
    rewrite eq.symm (add_assoc _ _ _), simp,

    apply or.inl rfl
  end
| (A' (atom.ndvd d i ks)) hf hn hu k _ hk h1 h2 := 
  begin
    cases (atom_type.dec_dep0 atom int (atom.dvd d i ks)) with hdep hdep,

    unfold I at h1, unfold interp at h1, 
    rewrite iff.symm (atom_type.decr_prsv atom int) at h1,
    unfold I at h2, unfold interp at h2, 
    rewrite iff.symm (atom_type.decr_prsv atom int) at h2,
    exfalso, apply h1 h2, apply hdep, apply hdep,

    rewrite atom_ndvd_mod at h1,
    rewrite atom_ndvd_mod at h2,
    rewrite mod_add_eq_mod at h2,
    exfalso, apply h1 h2, 
    apply dvd.trans (int.dvd_zlcms _ _) hk,
    apply hn, rewrite list.mem_map,
    existsi (atom.ndvd d i ks), apply and.intro,
    unfold atoms_dep0, rewrite list.mem_filter,
    apply and.intro, apply or.inl rfl,
    apply hdep, refl
  end
  | (A' (atom.dvd d i ks)) hf hn hu k _ hk h1 h2 := 
  begin
    cases (atom_type.dec_dep0 atom int (atom.dvd d i ks)) with hdep hdep,

    unfold I at h1, unfold interp at h1, 
    rewrite iff.symm (atom_type.decr_prsv atom int) at h1,
    unfold I at h2, unfold interp at h2, 
    rewrite iff.symm (atom_type.decr_prsv atom int) at h2,
    exfalso, apply h1 h2, apply hdep, apply hdep,

    rewrite atom_dvd_mod at h1,
    rewrite atom_dvd_mod at h2,
    rewrite mod_add_eq_mod at h2,
    exfalso, apply h1 h2, 
    apply dvd.trans (int.dvd_zlcms _ _) hk,
    apply hn, rewrite list.mem_map,
    existsi (atom.dvd d i ks), apply and.intro,
    unfold atoms_dep0, rewrite list.mem_filter,
    apply and.intro, apply or.inl rfl,
    apply hdep, refl
  end
| (p ∨' q) hf hn hu k hkp hk h1 h2 := 
  begin
    rewrite exp_I_or at h1, 
    rewrite not_or_distrib at h1, 
    rewrite exp_I_or at h2, cases h1 with hp hq,
    cases hn with hnp hnq,
    cases hf with hfp hfq,  
    unfold unified at hu, 
    unfold atoms at hu, 
    rewrite list.forall_mem_union at hu,
    cases hu with hup huq,
    cases h2 with h2 h2,
    cases (qe_cooper_one_prsv_lb p hfp hnp hup k hkp _ _ h2) with k' ik',
    cases ik' with iks hiks, cases hiks with hm h,
    existsi k', existsi iks, apply and.intro,
    apply mem_bnd_points_and, apply or.inl hm, apply h,
    apply dvd.trans _ hk, apply divisors_lcm_dvd_and_left,
    assumption,
    cases (qe_cooper_one_prsv_lb q hfq hnq huq k hkp _ _ h2) with k' ik',
    cases ik' with iks hiks, cases hiks with hm h,
    existsi k', existsi iks, apply and.intro,
    apply mem_bnd_points_and, apply or.inr hm, apply h,
    apply dvd.trans _ hk, apply divisors_lcm_dvd_and_right,
    assumption
  end
| (p ∧' q) hf hn hu k hkp hk h1 h2 := 
  begin
    rewrite exp_I_and at h1, 
    rewrite (@not_and_distrib _ _ (classical.prop_decidable _)) at h1,
    rewrite exp_I_and at h2,
    cases h2 with h1p h1q, 
    cases hn with hnp hnq,
    cases hf with hfp hfq,  
    unfold unified at hu, 
    unfold atoms at hu, 
    rewrite list.forall_mem_union at hu,
    cases hu with hup huq,
    cases h1 with h1 h1, 
    cases (qe_cooper_one_prsv_lb p hfp hnp hup k hkp _ h1 _) with k' ik',
    cases ik' with iks hiks, cases hiks with hm h,
    existsi k', existsi iks, apply and.intro,
    apply mem_bnd_points_and, apply or.inl hm, apply h,
    apply dvd.trans _ hk, apply divisors_lcm_dvd_and_left,
    assumption,
    cases (qe_cooper_one_prsv_lb q hfq hnq huq k hkp _ h1 _) with k' ik',
    cases ik' with iks hiks, cases hiks with hm h,
    existsi k', existsi iks, apply and.intro,
    apply mem_bnd_points_and, apply or.inr hm, apply h,
    apply dvd.trans _ hk, apply divisors_lcm_dvd_and_right,
    assumption
  end
| (¬' p) hf hn hu k _ hk h1 h2 := by cases hf
| (∃' p) hf hn hu k _ hk h1 h2 := by cases hf

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
  apply or.inr, 

  have h := 
    qe_cooper_one_prsv_lb 
      (lb - divisors_lcm p) bs p hf hn hu (divisors_lcm p) (pos_divisors_lcm _)
      (dvd_refl _) _ _,
  cases h with k' h, cases h with iks h, cases h with hiks h,
  cases h with h1 h, cases h with h2 h3,
  simp at h3, subst h3,

  unfold disj, rewrite I_list_disj, 

  existsi (I (list_disj
    (list.map (λ (n : ℤ), subst (n + iks.fst) (map_neg (iks.snd)) p)
       (list.irange (int.zlcms (list.map divisor (atoms_dep0 ℤ p)))))) bs), 
  
  apply and.intro, rewrite list.mem_map, 
  
  existsi (list_disj
             (list.map (λ (n : ℤ), subst (n + iks.fst) (map_neg (iks.snd)) p)
                (list.irange (int.zlcms (list.map divisor (atoms_dep0 ℤ p)))))),
  apply and.intro, rewrite list.mem_map,
  existsi iks, apply and.intro, apply hiks, refl, refl,
  rewrite I_list_disj,
  existsi (I (subst (k' + iks.fst) (map_neg (iks.snd)) p) bs),
  apply and.intro, rewrite list.mem_map,
  existsi (subst (k' + iks.fst) (map_neg (iks.snd)) p),
  apply and.intro, rewrite list.mem_map,
  existsi k', apply and.intro, 
  apply list.mem_irange, apply h1, apply h2, refl, refl,
  rewrite subst_prsv, simp, apply hlb1,
  apply hlb2, rewrite sub_lt_self_iff,
  apply pos_divisors_lcm, 
  simp, apply hlb1
end

lemma mul_div_abs (k z) : 
has_dvd.dvd (abs k) z → k * (z / abs k) = int.sign k * z := sorry

lemma int.mul_dvd_mul (x y z : int) : 
  z ≠ 0 → (has_dvd.dvd (z * x) (z * y) ↔ has_dvd.dvd x y) := sorry
  
lemma hd_coeffs_one_prsv_1 (lcm z : int) (zs)
  (hlcm1 : lcm > 0) 
  (hdvd : has_dvd.dvd lcm z) :
  ∀ (p : fm atom), nqfree p → fnormal ℤ p 
  → (has_dvd.dvd (coeffs_lcm p) lcm)
  → I (map_fm (hd_coeff_one lcm) p) (z::zs)
  → I p ((has_div.div z lcm)::zs) 
| ⊤' hf hn _ h := trivial
| ⊥' hf hn _ h := begin exfalso, apply h end
| (A' (atom.le i ks)) hf hn hlcm2 h := 
  begin
    unfold map_fm at h, 
    cases (le_dep0_split i ks) with hc hc, 
    rewrite hco_not_dep0 _ _ hc at h,
    rewrite I_not_dep0, rewrite I_not_dep0 at h, 
    apply h, apply hc, apply hc, 

    cases hc with k hk, cases hk with ks hks,
    cases hks with hks1 hks2, subst hks2,
    rewrite hco_le_nonzero at h, simp at h,

    rewrite coeffs_lcm_atom_le at hlcm2,
    rewrite I_atom_le, rewrite I_atom_le at h,
    apply @le_of_mul_le_mul_left _ _ _ _ (lcm / abs k),
    rewrite eq.symm (list.map_mul_dot_prod _ _ _),
    unfold list.map_mul, simp,
    rewrite list.cons_dot_prod_cons,
    rewrite list.cons_dot_prod_cons at h,
    simp, simp at h, 
    rewrite int.div_mul_comm lcm (abs k) k,
    rewrite int.mul_div_assoc, 
    rewrite int.div_abs_self,
    rewrite mul_comm lcm, rewrite mul_assoc,
    rewrite mul_comm lcm, rewrite int.div_mul_cancel,
    apply h, 
    apply hdvd,
    rewrite int.abs_dvd, apply dvd_refl, apply hlcm2,
    apply int.div_pos_of_pos_of_dvd,
    apply hlcm1, apply abs_nonneg, 
    rewrite int.abs_dvd, 
    rewrite int.abs_dvd at hlcm2, apply hlcm2, 
    apply hks1, apply hks1
  end
| (p ∧' q) hf hn hlcm h := 
  begin
    rewrite exp_I_and, 
    cases hf with hfp hfq, cases hn with hnp hnq,
    unfold map_fm at h, cases h with hp hq, 
    -- apply and.intro; apply hd_coeffs_one_prsv_1; 
    -- assumption
  end
  | (p ∨' q) hf hn h := 
  begin
    -- rewrite exp_I_or, 
    -- cases hf with hfp hfq, cases hn with hnp hnq,
    -- unfold map_fm at h, rewrite exp_I_or at h, cases h with hp hq,
    -- apply or.inl, apply hd_coeffs_one_prsv_1; assumption,
    -- apply or.inr, apply hd_coeffs_one_prsv_1; assumption
  end
| (¬' p) hf hn _ h := by cases hf
| (∃' p) hf hn _ h := by cases hf

#exit

/-
| (A' (atom.le i ks)) hf hn h hdvd := 
  begin
    unfold map_fm at h, 
    cases (le_dep0_split i ks) with hc hc, 
    rewrite hco_not_dep0 _ _ hc at h,
    existsi z, apply h,
    cases hc with k hc, cases hc with ks' hc,
    cases hc with hc1 hc2, subst hc2,
    rewrite hco_le_nonzero at h, simp at h,  

    let ex := (coeffs_lcm_atom_le i k ks' _),
    unfold coeffs_lcm at ex, rewrite ex at h,
    rewrite int.div_self at h, simp at h,

    existsi (has_div.div z (abs k)),
    rewrite list.map_one_mul at h,
    rewrite I_atom_le at h, rewrite I_atom_le,
    rewrite list.cons_dot_prod_cons at h,
    rewrite list.cons_dot_prod_cons,
    rewrite mul_div_abs, apply h, 
    rewrite coeffs_lcm_atom_le at hdvd,
    apply hdvd, apply hc1, 
    apply int.abs_neq_zero_of_neq_zero, 
    apply hc1, apply hc1, apply hc1
  end
| (A' (atom.dvd d i ks)) hf hn h hdvd := 
  begin
    unfold map_fm at h, 
    cases (dvd_dep0_split d i ks) with hc hc, 
    rewrite hco_not_dep0 _ _ hc at h,
    existsi z, apply h,
    cases hc with k hc, cases hc with ks' hc,
    cases hc with hc1 hc2, subst hc2,
    rewrite hco_dvd_nonzero at h, simp at h,  

    let ex := (coeffs_lcm_atom_dvd d i k ks' _),
    unfold coeffs_lcm at ex, rewrite ex at h,
    rewrite eq.symm (int.sign_eq_abs_div _) at h, 
    
    existsi (has_div.div z (abs k)), rewrite I_atom_dvd at h,
    rewrite I_atom_dvd, 
    rewrite iff.symm (int.mul_dvd_mul _ _ (int.sign k) _),
    rewrite mul_add, 
    rewrite eq.symm (list.map_mul_dot_prod _ _ _),
    unfold list.map_mul, unfold list.map, simp,
    rewrite list.cons_dot_prod_cons at h,
    rewrite list.cons_dot_prod_cons, 
    simp at h, rewrite int.sign_self_mul,
    rewrite int.mul_div_cancel', simp, apply h,
    rewrite coeffs_lcm_atom_dvd at hdvd,
    apply hdvd, apply hc1,
    apply int.sign_neq_zero_of_neq_zero, 
    apply hc1, apply hc1, apply hc1 
  end
| (A' (atom.ndvd d i ks)) hf hn h hdvd := 
  begin
    unfold map_fm at h, 
    cases (ndvd_dep0_split d i ks) with hc hc, 
    rewrite hco_not_dep0 _ _ hc at h,
    existsi z, apply h,
    cases hc with k hc, cases hc with ks' hc,
    cases hc with hc1 hc2, subst hc2,
    rewrite hco_ndvd_nonzero at h, simp at h,  

    let ex := (coeffs_lcm_atom_ndvd d i k ks' _),
    unfold coeffs_lcm at ex, rewrite ex at h,
    rewrite eq.symm (int.sign_eq_abs_div _) at h, 
    
    existsi (has_div.div z (abs k)), rewrite I_atom_ndvd at h,
    rewrite I_atom_ndvd, 
    rewrite iff.symm (int.mul_dvd_mul _ _ (int.sign k) _),
    rewrite mul_add, 
    rewrite eq.symm (list.map_mul_dot_prod _ _ _),
    unfold list.map_mul, unfold list.map, simp,
    rewrite list.cons_dot_prod_cons at h,
    rewrite list.cons_dot_prod_cons, 
    simp at h, rewrite int.sign_self_mul,
    rewrite int.mul_div_cancel', simp, apply h,
    rewrite coeffs_lcm_atom_ndvd at hdvd,
    apply hdvd, apply hc1,
    apply int.sign_neq_zero_of_neq_zero, 
    apply hc1, apply hc1, apply hc1 
  end
| (p ∧' q) hf hn h hdvd := sorry
| (p ∨' q) hf hn h hdvd := sorry
| (¬' p) hf hn h hdvd := by cases hf
| (∃' p) hf hn h hdvd := by cases hf -/

lemma hd_coeffs_one_prsv_2 (lcm z zs) :
  ∀ (p : fm atom), nqfree p → fnormal ℤ p 
  → has_dvd.dvd (coeffs_lcm p) lcm
  → I p (z::zs) 
  → I (map_fm (hd_coeff_one lcm) p) ((lcm*z)::zs) := sorry
  
lemma hd_coeffs_one_prsv :  
∀ (p : fm atom) (hf : nqfree p) (hn : fnormal ℤ p) (bs : list ℤ),
(∃ (b : ℤ), I (hd_coeffs_one p) (b :: bs)) ↔ ∃ (b : ℤ), I p (b :: bs) :=
begin
  intros p hf hn bs, apply iff.intro; 
  intro h; cases h with z hz, 

  unfold hd_coeffs_one at hz, 
  rewrite exp_I_and at hz,
  existsi (has_div.div z (coeffs_lcm p)), 
  cases hz with hz1 hz2, 
  apply hd_coeffs_one_prsv_1, 
  rewrite I_atom_dvd at hz1, 
  rewrite zero_add at hz1,
  rewrite list.cons_dot_prod_cons at hz1,
  rewrite list.nil_dot_prod at hz1,
  rewrite add_zero at hz1, rewrite one_mul at hz1, 
  apply hz1, apply hf, apply hn, apply hz2,

  existsi (coeffs_lcm p * z), unfold hd_coeffs_one,
  rewrite exp_I_and, apply and.intro,
  rewrite I_atom_dvd, rewrite zero_add,
  rewrite list.cons_dot_prod_cons,
  rewrite list.nil_dot_prod,
  rewrite add_zero, rewrite one_mul,
  apply dvd_mul_right, apply hd_coeffs_one_prsv_2,
  apply hf, apply hn, apply dvd_refl, apply hz
  
end

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
    
  
