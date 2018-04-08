import .qe

open pbgr

lemma I_atom_le (i : int) (ks zs : list int) : 
  I (A' (atom.le i ks)) zs ↔ (i ≤ list.dot_prod ks zs) := iff.refl _

lemma I_atom_dvd (d i ks zs) : 
  I (A' (atom.dvd d i ks)) zs ↔ (has_dvd.dvd d (i + list.dot_prod ks zs)) := iff.refl _

lemma I_atom_ndvd (d i ks zs) : 
  I (A' (atom.ndvd d i ks)) zs ↔ ¬ (has_dvd.dvd d (i + list.dot_prod ks zs)) := iff.refl _

lemma I_atom_ndvd' (d i : int) (ks zs : list int) :
   I (A' (atom.ndvd d i ks)) zs ↔ ¬ I (A' (atom.dvd d i ks)) zs :=
begin
  unfold I, unfold interp,
  unfold atom_type.val, unfold val
end 

meta def atom_dep0_split :=
`[cases ks with k' ks', 
  apply or.inl, apply not_not_intro rfl,
  cases (classical.em (k' = 0)) with h h, subst h, 
  apply or.inl, apply not_not_intro rfl,  
  apply or.inr, existsi k', existsi ks',
  apply and.intro; simp, apply h]

lemma le_dep0_split (i ks) : 
  (¬ atom_type.dep0 int (atom.le i ks)) 
  ∨ ∃ k, ∃ ks', (k ≠ 0 ∧ ks = (k::ks')) := by atom_dep0_split

lemma dvd_dep0_split (d i ks) : 
  (¬ atom_type.dep0 int (atom.dvd d i ks)) 
  ∨ ∃ k, ∃ ks', (k ≠ 0 ∧ ks = (k::ks')) := by atom_dep0_split

lemma ndvd_dep0_split (d i ks) : 
  (¬ atom_type.dep0 int (atom.ndvd d i ks)) 
  ∨ ∃ k, ∃ ks', (k ≠ 0 ∧ ks = (k::ks')) := by atom_dep0_split

meta def hco_not_dep0_tac :=
`[  cases ks with k' ks', refl, 
    cases (classical.em (k' = 0)) with hz hnz,
    subst hz, refl, exfalso, apply hnd, apply hnz]

lemma hco_not_dep0 (m) :
  ∀ a, (¬ atom_type.dep0 int a) → hd_coeff_one m a = a :=
begin
  intros a hnd, cases a with i ks d i ks d i ks,
  repeat
  {cases ks with k' ks', refl, 
    cases (classical.em (k' = 0)) with hz hnz,
    subst hz, refl, exfalso, apply hnd, apply hnz}
end

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
  have hne : int.lcms (list.map hd_coeff (atoms_dep0 ℤ p)) ≠ 0, 
  apply int.nonzero_of_pos,
  apply int.lcms_pos, 
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
  intro haz, apply int.dvd_lcms,
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

lemma ex_iff_inf_or_bnd_aux (P : int → Prop)
  (hP : ∀ (y : ℤ), (P y → ∃ (x : ℤ), x < y ∧ P x))
  (y : int) : ∀ (m n : nat), n ≤ m → P (y + int.of_nat n) → ∃ (x : int), (x < y ∧ P x)
| 0 n hle hn := 
  begin 
    cases n with n,
    have he : int.of_nat 0 = 0, refl, 
    rewrite he at hn, rewrite add_zero at hn, 
    apply hP, apply hn, cases hle
  end
| (m+1) n hle hn :=
  begin
    cases (lt_or_eq_of_le hle) with hlt heq,
    apply ex_iff_inf_or_bnd_aux m n,
    apply nat.le_of_lt_succ, apply hlt, apply hn,
    subst heq, clear hle, 
    cases (hP _ hn) with w hw, cases hw with hw1 hw2,
    cases (classical.em (w < y)) with hw3 hw3,
    existsi w, apply and.intro; assumption,
    rewrite not_lt at hw3, 
    cases (int.exists_nat_diff y w (m+1) hw3 hw1) with k hk,
    cases hk with hk1 hk2, 
    apply ex_iff_inf_or_bnd_aux m k, 
    apply nat.le_of_lt_succ, apply hk1,
    rewrite hk2 at hw2, apply hw2,
  end
   
lemma ex_iff_inf_or_bnd (P : int → Prop) :
  (∃ z, P z) ↔ ((∀ y, ∃ x, x < y ∧ P x) ∨ (∃ y, (P y ∧ ∀ x, x < y → ¬ P x))) := 
begin
  apply iff.intro; intro h1, 
  cases (classical.em ( ∃ (y : ℤ), P y ∧ ∀ (x : ℤ), x < y → ¬P x)) with h2 h2,
  apply or.inr h2, rewrite not_exists at h2,
  apply or.inl, intro y, cases h1 with z hz,
  cases (lt_or_le z y) with hlt hle, 
  existsi z, apply and.intro; assumption,
  rewrite iff.symm sub_nonneg at hle,
  rewrite int.nonneg_iff_exists at hle,
  cases hle with n hn, 
  apply (ex_iff_inf_or_bnd_aux P _ y n n _),
  rewrite sub_eq_iff_eq_add at hn, rewrite hn at hz,
  rewrite add_comm, apply hz, 
  intros x hx, apply classical.by_contradiction,
  intro hc, apply (h2 x), apply and.intro hx,
  rewrite not_exists at hc, intros w hw1 hw2,
  apply hc w, apply and.intro; assumption, 
  apply le_refl, 

  cases h1 with hinf hbnd, cases (hinf 0) with z hz,
  existsi z, apply hz^.elim_right, 
  cases hbnd with z hz, 
  existsi z, apply hz^.elim_left  
end

lemma mem_bnd_points_and (p q) : 
  ∀ b, ((b ∈ bnd_points p ∨ b ∈ bnd_points q) → b ∈ bnd_points (p ∧' q)) := 
begin
  unfold bnd_points, intro zzs,
  repeat {rewrite list.mem_filter_map},
  intro hm, cases hm with hm hm;
 {cases hm with a ha, cases ha with ha1 ha2,
  unfold atoms_dep0 at ha1, rewrite list.mem_filter at ha1, 
  cases ha1 with ha1a ha1b, existsi a, apply and.intro _ ha2,
  apply list.mem_filter_of_mem _ ha1b, unfold atoms,
  {apply list.mem_union_left ha1a _
   <|> apply list.mem_union_right _ ha1a}}
end

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

meta def inf_minus_prsv_tac :=
`[existsi (0 : int), intros z hz, unfold inf_minus]

lemma inf_minus_prsv (zs) : ∀ (p : fm atom),
  ∃ (y : int), ∀ z, z < y →  
    (I (inf_minus p) (z::zs) ↔ I p (z::zs)) 
| ⊤' := 
  begin 
    existsi (0 : int), intros z hz,
    apply true_iff_true; trivial
  end
| ⊥' := 
  begin 
    existsi (0 : int), intros z hz,
    apply false_iff_false; intro hc; cases hc
  end
| (A' (atom.le i ks)) := 
  begin
    cases ks with k ks, inf_minus_prsv_tac,
    cases (lt_trichotomy k 0) with hlt heqgt,

    existsi (- abs (i - list.dot_prod ks zs)), 
    intros z hz,
    unfold inf_minus, rewrite ite_true,
    rewrite I_atom_le, simp,
    rewrite iff.symm sub_le_iff_le_add,
    apply true_iff_true, trivial,
    apply le_trans (le_abs_self _),
    rewrite lt_neg at hz,
    apply le_trans (le_of_lt hz),
    rewrite eq.symm (neg_neg k),
    rewrite neg_mul_comm,
    apply int.le_mul_of_pos_left,
    apply le_trans _ (le_of_lt hz),
    apply abs_nonneg, unfold gt,
    rewrite lt_neg, apply hlt, apply hlt,

    cases heqgt with heq hgt, subst heq,
    inf_minus_prsv_tac,
    rewrite ite_false,
    rewrite ite_false, intro hc, cases hc,
    intro hc, cases hc,

    existsi (- abs (i - list.dot_prod ks zs)),
    intros z hz, unfold inf_minus,
    rewrite ite_false, rewrite ite_true,
    rewrite I_atom_le, simp, 
    rewrite iff.symm sub_le_iff_le_add,
    apply false_iff_false, intro hc, cases hc,
    rewrite not_le,
    apply @lt_of_le_of_lt _ _ _ z,
    rewrite iff.symm neg_le_neg_iff,
    rewrite neg_mul_eq_mul_neg,
    apply int.le_mul_of_pos_left,
    unfold ge, rewrite le_neg,
    apply le_trans, apply le_of_lt hz,
    rewrite neg_le_neg_iff, apply abs_nonneg,
    apply hgt, apply lt_of_lt_of_le hz,
    rewrite neg_le, apply neg_le_abs_self,
    apply hgt, rewrite not_lt, 
    apply le_of_lt hgt
  end
| (A' (atom.dvd d i ks)) := by inf_minus_prsv_tac
| (A' (atom.ndvd d i ks)) := by inf_minus_prsv_tac
| (p ∧' q) := 
  begin
    cases (inf_minus_prsv p) with x hx,
    cases (inf_minus_prsv q) with y hy,
    cases (int.exists_lt_and_lt x y) with z hz,
    cases hz with hz1 hz2,
    existsi z, intros w hw,
    unfold inf_minus, rewrite exp_I_and_o,
    rewrite hx, rewrite hy, rewrite exp_I_and,
    apply lt.trans hw hz2,
    apply lt.trans hw hz1,
  end
| (p ∨' q) := 
  begin
    cases (inf_minus_prsv p) with x hx,
    cases (inf_minus_prsv q) with y hy,
    cases (int.exists_lt_and_lt x y) with z hz,
    cases hz with hz1 hz2,
    existsi z, intros w hw,
    unfold inf_minus, rewrite exp_I_or_o,
    rewrite hx, rewrite hy, rewrite exp_I_or,
    apply lt.trans hw hz2,
    apply lt.trans hw hz1,
  end
| (¬' p) := by inf_minus_prsv_tac
| (∃' p) := by inf_minus_prsv_tac

lemma pos_coeffs_lcm (p : fm atom) :
  coeffs_lcm p > 0 := 
begin
  unfold coeffs_lcm, apply int.lcms_pos,
  intros z hz, rewrite list.mem_map at hz,
  cases hz with a ha, cases ha with ha1 ha2,
  subst ha2, unfold atoms_dep0 at ha1, 
  rewrite list.mem_filter at ha1, apply ha1^.elim_right
end

lemma pos_divisors_lcm (p : fm atom) (hn : fnormal int p) :
  divisors_lcm p > 0 := 
begin
  unfold divisors_lcm, apply int.lcms_pos,
  intros z hz, rewrite list.mem_map at hz,
  cases hz with a ha, cases ha with ha1 ha2,
  subst ha2, unfold atoms_dep0 at ha1, 
  rewrite list.mem_filter at ha1, 
  cases ha1 with ha1 ha2,
  rewrite iff.symm normal_iff_divisor_nonzero,
  rewrite fnormal_iff_fnormal_alt at hn,
  apply hn, apply ha1
end

meta def coeffs_lcm_atom_tac :=
`[intro hk, unfold coeffs_lcm,
  unfold atoms_dep0, unfold atoms,
  unfold list.filter, rewrite ite_true,
  unfold list.map, unfold hd_coeff, 
  unfold list.head_dft, unfold int.lcms,
  apply int.lcm_one_right, apply hk]

lemma coeffs_lcm_atom_le {i k : int} {ks : list int} :
  k ≠ 0 → coeffs_lcm (A' (atom.le i (k::ks))) = abs k := 
by coeffs_lcm_atom_tac

lemma coeffs_lcm_atom_dvd {d i k : int} {ks : list int} :
  k ≠ 0 → coeffs_lcm (A' (atom.dvd d i (k::ks))) = abs k := 
by coeffs_lcm_atom_tac

lemma coeffs_lcm_atom_ndvd {d i k : int} {ks : list int} :
  k ≠ 0 → coeffs_lcm (A' (atom.ndvd d i (k::ks))) = abs k := 
by coeffs_lcm_atom_tac

meta def divisors_lcm_atom_tac :=
`[intro hk,
  unfold divisors_lcm, unfold atoms_dep0,
  unfold atoms, unfold list.filter,
  rewrite ite_true, unfold list.map, 
  unfold divisor, unfold int.lcms,
  apply int.lcm_one_right, apply hk]

lemma divisors_lcm_atom_dvd {d i k : int} {ks : list int} :
  k ≠ 0 → divisors_lcm (A' (atom.dvd d i (k::ks))) = abs d := 
by divisors_lcm_atom_tac

lemma divisors_lcm_atom_ndvd {d i k : int} {ks : list int} :
  k ≠ 0 → divisors_lcm (A' (atom.ndvd d i (k::ks))) = abs d := 
by divisors_lcm_atom_tac

meta def lcm_distrib_tac :=
`[apply int.lcms_distrib, 
  apply list.equiv.trans, 
  apply list.map_equiv_map_of_equiv,
  apply list.filter_union,
  apply list.map_union]

lemma coeffs_lcm_and (p q) :
  coeffs_lcm (p ∧' q) = int.lcm (coeffs_lcm p) (coeffs_lcm q) := 
by lcm_distrib_tac

lemma coeffs_lcm_or (p q) :
  coeffs_lcm (p ∨' q) = int.lcm (coeffs_lcm p) (coeffs_lcm q) := 
by lcm_distrib_tac

lemma divisors_lcm_and (p q) :
  divisors_lcm (p ∧' q) = int.lcm (divisors_lcm p) (divisors_lcm q) := 
by lcm_distrib_tac

lemma divisors_lcm_or (p q) :
  divisors_lcm (p ∨' q) = int.lcm (divisors_lcm p) (divisors_lcm q) := 
by lcm_distrib_tac

lemma coeffs_lcm_pos (p) :
  coeffs_lcm p > 0 := 
begin
  apply int.lcms_pos,
  intros z hz, rewrite list.mem_map at hz,
  cases hz with a ha, cases ha with ha1 ha2,
  subst ha2, unfold atoms_dep0 at ha1,
  rewrite list.mem_filter at ha1,
  apply ha1^.elim_right
end

lemma divisors_lcm_pos (p) :
  fnormal int p → divisors_lcm p > 0 := 
begin
  intro hn, apply int.lcms_pos,
  intros z hz, rewrite list.mem_map at hz,
  cases hz with a ha, cases ha with ha1 ha2,
  subst ha2, unfold atoms_dep0 at ha1,
  rewrite list.mem_filter at ha1,
  rewrite fnormal_iff_fnormal_alt at hn,
  rewrite iff.symm normal_iff_divisor_nonzero,
  apply hn, apply ha1^.elim_left
end

lemma atom_dvd_mod (m d i ks z zs) :
  has_dvd.dvd d m → 
  ((I (A' (atom.dvd d i ks)) (z :: zs)) ↔ 
   (I (A' (atom.dvd d i ks)) (z % m :: zs))) := 
begin
  intro hdvd,
  repeat {rewrite I_atom_dvd},  
  cases ks with k ks; simp,
  repeat {rewrite add_comm i},
  repeat {rewrite (add_assoc)},
  apply iff.symm, apply iff.trans,
  apply (@dvd_add_iff_right _ _ _ (k * (z - z % m))),
  apply dvd_mul_of_dvd_right, 
  rewrite int.mod_def, 
  rewrite eq.symm (sub_add _ _ _), simp,
  apply dvd_mul_of_dvd_left, apply hdvd,
  rewrite add_comm, rewrite add_assoc,
  rewrite add_comm _ i,
  rewrite add_assoc,
  rewrite eq.symm (mul_add _ _ _),
  rewrite add_comm (z % m),
  rewrite sub_add_cancel, simp
end

lemma atom_ndvd_mod (m d i ks z zs) : 
  has_dvd.dvd d m → 
  ((I (A' (atom.ndvd d i ks)) (z :: zs)) ↔ 
   (I (A' (atom.ndvd d i ks)) (z % m :: zs))) := 
begin
  intro hdvd,
  repeat {rewrite I_atom_ndvd'},
  rewrite atom_dvd_mod, apply hdvd
end

lemma divisors_lcm_dvd_and_left (p q) : 
  has_dvd.dvd (divisors_lcm p) (divisors_lcm (p ∧'  q)) := 
begin
  rewrite divisors_lcm_and,
  apply int.dvd_lcm_left
end

lemma divisors_lcm_dvd_and_right (p q) : 
  has_dvd.dvd (divisors_lcm q) (divisors_lcm (p ∧' q)) := 
begin
  rewrite divisors_lcm_and,
  apply int.dvd_lcm_right
end

lemma inf_minus_mod (k z zs) : 
  ∀ p, nqfree p → (has_dvd.dvd (divisors_lcm p) k)
    → ((I (inf_minus p) (z :: zs)) 
       ↔ (I (inf_minus p) (z % k :: zs)))
| ⊤' _ _ := begin apply true_iff_true; trivial end
| ⊥' _ _ := begin apply false_iff_false; intro hc; cases hc end
| (A' (atom.le i [])) hf hdvd := 
  begin
    unfold inf_minus, repeat {rewrite I_not_dep0},
    repeat {apply not_not_intro, refl}
  end
| (A' (atom.le i (k'::ks'))) hf hdvd := 
  begin
    cases (lt_trichotomy k' 0) with hlt heqgt;
    unfold inf_minus, rewrite ite_true,
    apply true_iff_true; trivial, apply hlt,
    cases heqgt with heq hgt, subst heq,
    rewrite ite_false, rewrite ite_false, 
    repeat {rewrite I_not_dep0},
    repeat {apply not_not_intro, refl},
    simp, simp, 
    rewrite ite_false, rewrite ite_true, 
    apply false_iff_false; intro hc; cases hc,
    apply hgt, rewrite not_lt, apply le_of_lt hgt
  end
| (A' (atom.dvd d i ks)) hf hdvd := 
  begin
    cases (dvd_dep0_split d i ks) with hd0 hd0,
    unfold inf_minus, repeat {rewrite I_not_dep0},
    assumption, assumption,
    cases hd0 with k' hk', cases hk' with ks' hks',
    cases hks' with h1 h2, subst h2,
    rewrite divisors_lcm_atom_dvd at hdvd,
    rewrite int.abs_dvd at hdvd, 
    apply atom_dvd_mod, apply hdvd, apply h1
  end
| (A' (atom.ndvd d i ks)) hf hdvd := 
  begin
    cases (ndvd_dep0_split d i ks) with hd0 hd0,
    unfold inf_minus,  repeat {rewrite I_not_dep0},
    assumption, assumption,
    cases hd0 with k' hk', cases hk' with ks' hks',
    cases hks' with h1 h2, subst h2,
    rewrite divisors_lcm_atom_ndvd at hdvd,
    rewrite int.abs_dvd at hdvd, 
    apply atom_ndvd_mod, apply hdvd, apply h1
  end
| (p ∧' q) hf hdvd := 
  begin
    cases hf with hfp hfq,
    unfold inf_minus,
    repeat {rewrite exp_I_and_o},
    repeat {rewrite inf_minus_mod; try {assumption}},
    apply dvd.trans _ hdvd,
    apply divisors_lcm_dvd_and_right,
    apply dvd.trans _ hdvd,
    apply divisors_lcm_dvd_and_left
  end
| (p ∨' q) hf hdvd := 
  begin
    cases hf with hfp hfq,
    unfold inf_minus,
    repeat {rewrite exp_I_or_o},
    repeat {rewrite inf_minus_mod; try {assumption}},
    apply dvd.trans _ hdvd,
    apply divisors_lcm_dvd_and_right,
    apply dvd.trans _ hdvd,
    apply divisors_lcm_dvd_and_left
  end
| (¬' p) hf _ := by cases hf
| (∃' p) hf _ := by cases hf

lemma no_lb_inf_minus (p : fm atom) (hf : nqfree p)
  (hn : fnormal int p) (z : int) (zs) : I (inf_minus p) (z::zs) 
  → ∀ y, ∃ x, (x < y ∧ I (inf_minus p) (x::zs)) := 
begin
  intros h y, cases lt_or_le z y with hlt hle,
  existsi z, apply and.intro; assumption,
  have hw : ∃ (w : int), z < y + (w * divisors_lcm p),
  existsi (z - y + 1),
  rewrite iff.symm sub_lt_iff_lt_add',
  apply int.lt_mul_of_nonneg_right,
  rewrite int.lt_add_one_iff,
  rewrite iff.symm sub_nonneg at hle,
  apply le_trans hle, 
  apply le_of_lt, rewrite int.lt_add_one_iff,
  apply divisors_lcm_pos _ hn,
  cases hw with w hw,
  rewrite iff.symm sub_lt_iff_lt_add at hw,
  existsi (z - w * divisors_lcm p),
  apply and.intro hw, 
  rewrite inf_minus_mod (divisors_lcm p),
  rewrite inf_minus_mod (divisors_lcm p) at h,
  rewrite (sub_eq_add_neg _ _),
  rewrite neg_mul_eq_neg_mul,
  rewrite int.add_mul_mod_self, apply h,
  repeat {assumption <|> apply dvd_refl}
end

lemma mod_add_eq_mod (i j k : int) : (has_dvd.dvd k j) → (i + j) % k = i % k := 
begin
  intro hdvd, rewrite int.dvd_iff_exists at hdvd,
  cases hdvd with z hz, subst hz,
  rewrite int.add_mul_mod_self
end

lemma le_hd_coeff_decr {y z i k : int} {zs ks : list int} :
k < 0 → y < z 
→ I (A' atom.le i (k :: ks)) (z :: zs)
→ I (A' atom.le i (k :: ks)) (y :: zs) := 
begin
  intros hk hyz h,
  rewrite I_atom_le at *, simp at *,
  apply le_trans h,
  rewrite add_le_add_iff_right,
  rewrite int.mul_le_mul_iff_le_of_neg_left,
  apply le_of_lt hyz, apply hk
end

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

    rewrite atom_ndvd_mod d at h1,
    rewrite atom_ndvd_mod d at h2,
    rewrite mod_add_eq_mod at h2,
    exfalso, apply h1 h2, 
    apply dvd.trans (int.dvd_lcms _) hk,
    rewrite list.mem_map,
    existsi (atom.ndvd d i ks), apply and.intro,
    unfold atoms_dep0, rewrite list.mem_filter,
    apply and.intro, apply or.inl rfl,
    apply hdep, refl, apply dvd_refl, apply dvd_refl
  end
  | (A' (atom.dvd d i ks)) hf hn hu k _ hk h1 h2 := 
  begin
    cases (atom_type.dec_dep0 atom int (atom.dvd d i ks)) with hdep hdep,

    unfold I at h1, unfold interp at h1, 
    rewrite iff.symm (atom_type.decr_prsv atom int) at h1,
    unfold I at h2, unfold interp at h2, 
    rewrite iff.symm (atom_type.decr_prsv atom int) at h2,
    exfalso, apply h1 h2, apply hdep, apply hdep,

    rewrite atom_dvd_mod d at h1,
    rewrite atom_dvd_mod d at h2,
    rewrite mod_add_eq_mod at h2,
    exfalso, apply h1 h2, 
    apply dvd.trans (int.dvd_lcms _) hk,
    rewrite list.mem_map,
    existsi (atom.dvd d i ks), apply and.intro,
    unfold atoms_dep0, rewrite list.mem_filter,
    apply and.intro, apply or.inl rfl,
    apply hdep, refl,
    apply dvd_refl, apply dvd_refl
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
  
  cases (inf_minus_prsv bs p) with lb hlb,

  cases (no_lb_inf_minus p hf hn z bs hq2 lb) with x hx,
  cases hx with hx1 hx2, 

  rewrite (hlb x hx1) at hx2,
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
  apply or.inl, cases (inf_minus_prsv bs p) with lb hlb,
  cases (h lb) with x hx, cases hx with hx1 hx2, 
  rewrite iff.symm (hlb x hx1) at hx2, 
  unfold disj, rewrite I_list_disj, simp, 
  unfold function.comp,
  existsi (I (inf_minus p) ( (int.mod x (divisors_lcm p)) :: bs)),
  apply and.intro, rewrite list.mem_map, 
  existsi (int.mod x (divisors_lcm p)), apply and.intro,
  apply list.mem_irange,
  apply int.mod_nonneg,
  apply int.neq_zero_of_gt_zero, apply pos_divisors_lcm,
  apply hn,
  unfold divisors_lcm, apply int.mod_lt_of_pos, 
  apply pos_divisors_lcm, apply hn,
  rewrite subst_prsv, rewrite list.nil_dot_prod,
  rewrite add_zero, rewrite inf_minus_mod at hx2,
  apply hx2, apply hf, apply dvd_refl,
  cases h with lb hlb, cases hlb with hlb1 hlb2, 
  apply or.inr, 

  have h := 
    qe_cooper_one_prsv_lb 
      (lb - (divisors_lcm p)) bs p hf hn hu 
      (divisors_lcm p) (pos_divisors_lcm _ hn)
      (dvd_refl _) _ _,
  cases h with k' h, cases h with iks h, cases h with hiks h,
  cases h with h1 h, cases h with h2 h3,
  simp at h3, subst h3,

  unfold disj, rewrite I_list_disj, 

  existsi (I (list_disj
    (list.map (λ (n : ℤ), subst (n + iks.fst) (map_neg (iks.snd)) p)
       (list.irange (int.lcms (list.map divisor (atoms_dep0 ℤ p)))))) bs), 
  
  apply and.intro, rewrite list.mem_map, 
  
  existsi (list_disj
             (list.map (λ (n : ℤ), subst (n + iks.fst) (map_neg (iks.snd)) p)
                (list.irange (int.lcms (list.map divisor (atoms_dep0 ℤ p)))))),
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
  apply pos_divisors_lcm, apply hn,
  simp, apply hlb1
end

lemma I_hco_le (lcm z i : ℤ) (zs ks : list ℤ)
  (hpos : lcm > 0)
  (hdvd : coeffs_lcm (A' atom.le i ks) ∣ lcm) :
  I (A' hd_coeff_one lcm (atom.le i ks)) (lcm * z :: zs) 
  ↔ I (A' atom.le i ks) (z :: zs) :=
begin
  cases (le_dep0_split i ks) with hdep0 hdep0,
  rewrite hco_not_dep0 _ _ hdep0, 
  repeat {rewrite I_not_dep0 _ _ _ hdep0},

  cases hdep0 with k hk, cases hk with ks' hks',
  cases hks' with hk hks', subst hks',
  rewrite coeffs_lcm_atom_le hk at hdvd, 

  rewrite hco_le_nonzero, simp, 
  repeat {rewrite I_atom_le}, simp,
  apply iff.trans _ 
    (int.mul_le_mul_iff_le_of_pos_left _ _ (has_div.div lcm (abs k)) _),
  simp, rewrite mul_add, simp,
  rewrite eq.symm (mul_assoc _ k z),
  rewrite int.div_mul_comm lcm _ k,
  rewrite int.mul_div_assoc,
  rewrite int.div_abs_self,
  rewrite mul_comm lcm (int.sign k), simp,
  rewrite mul_assoc, rewrite int.abs_dvd,
  apply dvd_refl, apply hdvd,
  apply int.div_pos_of_pos_of_dvd, apply hpos,
  apply abs_nonneg, apply hdvd, apply hk
end 

lemma I_hco_dvd (lcm z d i : ℤ) (zs ks : list ℤ)
  (hpos : lcm > 0)
  (hdvd : coeffs_lcm (A' atom.dvd d i ks) ∣ lcm) :
  I (A' hd_coeff_one lcm (atom.dvd d i ks)) (lcm * z :: zs) 
  ↔ I (A' atom.dvd d i ks) (z :: zs) :=
begin
  cases (dvd_dep0_split d i ks) with hdep0 hdep0,
  rewrite hco_not_dep0 _ _ hdep0, 
  repeat {rewrite I_not_dep0 _ _ _ hdep0},
  cases hdep0 with k hk, cases hk with ks' hks',
  cases hks' with hk hks', subst hks',
  rewrite coeffs_lcm_atom_dvd hk at hdvd, 
  rewrite int.abs_dvd at hdvd, 
  rewrite hco_dvd_nonzero, simp, 
  repeat {rewrite I_atom_dvd}, simp,
  apply iff.trans _ 
    (@mul_dvd_mul_iff_left _ _ (has_div.div lcm k) _ _ _),
  rewrite mul_add, rewrite mul_add, 
  rewrite eq.symm (mul_assoc _ _ _),
  rewrite int.div_mul_cancel, simp, 
  apply hdvd, apply int.div_nonzero, 
  apply int.nonzero_of_pos hpos, apply hdvd,
  apply hk 
end

lemma I_hco_ndvd (lcm z d i : ℤ) (zs ks : list ℤ)
  (hpos : lcm > 0)
  (hdvd : coeffs_lcm (A' atom.ndvd d i ks) ∣ lcm) :
  I (A' hd_coeff_one lcm (atom.ndvd d i ks)) (lcm * z :: zs) 
  ↔ I (A' atom.ndvd d i ks) (z :: zs) :=
begin
  cases (ndvd_dep0_split d i ks) with hdep0 hdep0,
  rewrite hco_not_dep0 _ _ hdep0, 
  repeat {rewrite I_not_dep0 _ _ _ hdep0},
  cases hdep0 with k hk, cases hk with ks' hks',
  cases hks' with hk hks', subst hks',
  rewrite coeffs_lcm_atom_ndvd hk at hdvd, 
  rewrite int.abs_dvd at hdvd, 
  rewrite hco_ndvd_nonzero, simp, 
  repeat {rewrite I_atom_ndvd}, simp,
  rewrite (@not_iff_not _ _ (classical.dec _) (classical.dec _)),
  apply iff.trans _ 
    (@mul_dvd_mul_iff_left _ _ (has_div.div lcm k) _ _ _),
  rewrite mul_add, rewrite mul_add, 
  rewrite eq.symm (mul_assoc _ _ _),
  rewrite int.div_mul_cancel, simp, 
  apply hdvd, apply int.div_nonzero, 
  apply int.nonzero_of_pos hpos, apply hdvd,
  apply hk 
end

lemma hcso_prsv_2 (lcm z : int) (zs) 
  (hpos : lcm > 0) :
  ∀ (p : fm atom), nqfree p → fnormal ℤ p 
  → has_dvd.dvd (coeffs_lcm p) lcm
  → I p (z::zs) 
  → I (map_fm (hd_coeff_one lcm) p) ((lcm * z)::zs) 
| ⊤' hf hn hdvd h := trivial
| ⊥' hf hn hdvd h := by cases h
| (A' (atom.le i ks)) hf hn hdvd h := 
  begin
    unfold map_fm, rewrite I_hco_le, 
    apply h, apply hpos, apply hdvd
  end
| (A' (atom.dvd d i ks)) hf hn hdvd h := 
  begin
    unfold map_fm, rewrite I_hco_dvd, 
    apply h, apply hpos, apply hdvd
  end
| (A' (atom.ndvd d i ks)) hf hn hdvd h := 
  begin
    unfold map_fm, rewrite I_hco_ndvd, 
    apply h, apply hpos, apply hdvd
  end
| (p ∧' q) hf hn hdvd h := 
  begin
    unfold map_fm, rewrite exp_I_and, 
    rewrite exp_I_and at h, cases h with hp hq,
    cases hn with hnp hnq,
    cases hf with hfp hfq,
    rewrite coeffs_lcm_and at hdvd,
    apply and.intro; apply hcso_prsv_2;
    try {assumption},
    apply dvd.trans _ hdvd, apply int.dvd_lcm_left,
    apply dvd.trans _ hdvd, apply int.dvd_lcm_right
  end
| (p ∨' q) hf hn hdvd h := 
  begin
    unfold map_fm, rewrite exp_I_or, 
    rewrite exp_I_or at h, 
    cases hn with hnp hnq,
    cases hf with hfp hfq,
    rewrite coeffs_lcm_or at hdvd,
    cases h with hp hq, apply or.inl, 
    apply hcso_prsv_2; try {assumption},
    apply dvd.trans _ hdvd, apply int.dvd_lcm_left,
    apply or.inr, 
    apply hcso_prsv_2; try {assumption},
    apply dvd.trans _ hdvd, apply int.dvd_lcm_right
  end
| (¬' p) hf hn hdvd h := by cases hf
| (∃' p) hf hn hdvd h := by cases hf

meta def hcso_prsv_tac := 
`[rewrite int.dvd_iff_exists at hdvd,
  cases hdvd with w hw, rewrite eq.symm hw,
  rewrite int.mul_div_assoc, 
  rewrite int.div_self, rewrite mul_one,
  rewrite eq.symm hw at h, rewrite mul_comm at h]

lemma hcso_prsv_1 (lcm z : int) (zs)
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
    hcso_prsv_tac, unfold map_fm at h,
    rewrite I_hco_le at h; try {assumption}, 
    apply int.nonzero_of_pos hlcm1, apply dvd_refl
  end
| (A' (atom.dvd d i ks)) hf hn hlcm2 h := 
  begin
    hcso_prsv_tac, unfold map_fm at h,
    rewrite I_hco_dvd at h; try {assumption}, 
    apply int.nonzero_of_pos hlcm1, apply dvd_refl
  end
| (A' (atom.ndvd d i ks)) hf hn hlcm2 h := 
  begin
    unfold map_fm at h, 
    cases (ndvd_dep0_split d i ks) with hc hc, 
    rewrite hco_not_dep0 _ _ hc at h,
    rewrite I_not_dep0, rewrite I_not_dep0 at h, 
    apply h, apply hc, apply hc, 

    cases hc with k hk, cases hk with ks hks,
    cases hks with hks1 hks2, subst hks2,
    rewrite hco_ndvd_nonzero at h, simp at h,

    rewrite coeffs_lcm_atom_ndvd at hlcm2, 
    rewrite int.abs_dvd at hlcm2, 
    rewrite I_atom_ndvd, rewrite I_atom_ndvd at h,
    intro hc, exfalso, apply h,
    rewrite iff.symm (@mul_dvd_mul_iff_left _ _ (has_div.div lcm k) _ _ _) at hc,
    simp, simp at hc, rewrite mul_add at hc, 
    rewrite mul_add at hc, simp at hc, 
    rewrite eq.symm (mul_assoc _ _ _) at hc, 
    rewrite int.div_mul_cancel at hc, 
    rewrite mul_comm lcm at hc, 
    rewrite int.div_mul_cancel at hc, 
    simp at hc, apply hc, apply hdvd,
    apply hlcm2, apply int.div_nonzero,
    apply int.nonzero_of_pos, apply hlcm1,
    apply hlcm2, apply hks1, apply hks1
  end
| (p ∧' q) hf hn hlcm2 h := 
  begin
    rewrite exp_I_and, 
    cases hf with hfp hfq, cases hn with hnp hnq,
    unfold map_fm at h, cases h with hp hq, 
    rewrite coeffs_lcm_and at hlcm2,
    apply and.intro; apply hcso_prsv_1; 
    try {assumption},
    apply dvd.trans _ hlcm2, apply int.dvd_lcm_left,
    apply dvd.trans _ hlcm2, apply int.dvd_lcm_right,
  end
  | (p ∨' q) hf hn hlcm2 h := 
  begin
    rewrite coeffs_lcm_or at hlcm2,
    rewrite exp_I_or, 
    cases hf with hfp hfq, cases hn with hnp hnq,
    unfold map_fm at h, rewrite exp_I_or at h, cases h with hp hq,
    apply or.inl, apply hcso_prsv_1; try {assumption},
    apply dvd.trans _ hlcm2, apply int.dvd_lcm_left,
    apply or.inr, apply hcso_prsv_1; try {assumption},
    apply dvd.trans _ hlcm2, apply int.dvd_lcm_right
  end
| (¬' p) hf hn _ h := by cases hf
| (∃' p) hf hn _ h := by cases hf

lemma hcso_prsv :  
∀ (p : fm atom) (hf : nqfree p) (hn : fnormal ℤ p) (bs : list ℤ),
(∃ (b : ℤ), I (hd_coeffs_one p) (b :: bs)) ↔ ∃ (b : ℤ), I p (b :: bs) :=
begin
  intros p hf hn bs, apply iff.intro; 
  intro h; cases h with z hz, 

  unfold hd_coeffs_one at hz, 
  rewrite exp_I_and at hz,
  existsi (has_div.div z (coeffs_lcm p)), 
  cases hz with hz1 hz2, 
  apply hcso_prsv_1; try {assumption},
  rewrite I_atom_dvd at hz1, 
  rewrite zero_add at hz1,
  rewrite list.cons_dot_prod_cons at hz1,
  rewrite list.nil_dot_prod at hz1,
  rewrite add_zero at hz1, rewrite one_mul at hz1, 
  apply coeffs_lcm_pos,
  rewrite I_atom_dvd at hz1, simp at hz1, 
  apply hz1, apply dvd_refl,

  existsi (coeffs_lcm p * z), unfold hd_coeffs_one,
  rewrite exp_I_and, apply and.intro,
  rewrite I_atom_dvd, rewrite zero_add,
  rewrite list.cons_dot_prod_cons,
  rewrite list.nil_dot_prod,
  rewrite add_zero, rewrite one_mul,
  apply dvd_mul_right, apply hcso_prsv_2;
  try {assumption},
  apply coeffs_lcm_pos, apply dvd_refl
end

lemma sqe_cooper_prsv :  
  ∀ (p : fm atom), nqfree p → fnormal ℤ p 
  → ∀ (bs : list ℤ), I (sqe_cooper p) bs ↔ ∃ (b : ℤ), I p (b :: bs) := 
begin
  intros p hf hn bs, unfold sqe_cooper, 
  rewrite qe_cooper_one_prsv,
  apply hcso_prsv p hf hn bs, 
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
    
  
