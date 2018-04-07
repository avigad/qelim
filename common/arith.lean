import .nat ...mathlib.data.int.basic

namespace int

lemma mul_nonzero {z y : int} : z ≠ 0 → y ≠ 0 → z * y ≠ 0 := 
begin
  intros hm hn hc, apply hm,
  apply eq.trans, apply eq.symm, 
  apply int.mul_div_cancel,
  apply hn, rewrite hc, apply int.zero_div
end 

lemma div_nonzero (z y : int) : z ≠ 0 → has_dvd.dvd y z → (z / y) ≠ 0 := 
begin
  intros hz hy hc, apply hz,
  apply eq.trans, apply eq.symm, 
  apply int.div_mul_cancel, apply hy,
  rewrite hc, apply zero_mul,
end

lemma nat_abs_neq_zero (z : int) : z ≠ 0 → int.nat_abs z ≠ 0 := 
begin
  intro hz, cases z with n n, simp,
  apply nat.neq_zero_of_of_nat_neq_zero hz,
  simp, intro hc, cases hc
end

lemma dvd_iff_nat_abs_dvd_nat_abs {x y : int} : 
  (has_dvd.dvd x y)
  ↔ (has_dvd.dvd (int.nat_abs x) (int.nat_abs y)) :=
begin
  rewrite iff.symm int.coe_nat_dvd,
  rewrite int.nat_abs_dvd, rewrite int.dvd_nat_abs
end

def lcm (x y : int) : int :=
  (nat.lcm (nat_abs x) (nat_abs y))

lemma lcm_dvd {x y z : int} (hx : has_dvd.dvd x z) (hy : y ∣ z) : lcm x y ∣ z :=
begin
  rewrite dvd_iff_nat_abs_dvd_nat_abs, 
  rewrite dvd_iff_nat_abs_dvd_nat_abs at hx, 
  rewrite dvd_iff_nat_abs_dvd_nat_abs at hy,
  unfold lcm, rewrite nat_abs_of_nat,
  apply nat.lcm_dvd; assumption
end

lemma lcm_one_right (z : int) :
  lcm z 1 = abs z :=
begin
  unfold lcm, simp, rewrite nat.lcm_one_right, 
  cases (classical.em (0 ≤ z)) with hz hz,
  rewrite abs_eq_nat_abs, 
  rewrite not_le at hz, 
  apply @eq.trans _ _ (↑(nat_abs z)), refl,
  rewrite (@of_nat_nat_abs_of_nonpos z _),
  rewrite abs_of_neg, apply hz,
  apply le_of_lt hz
end

def lcms : list int → int
| [] := 1 
| (z::zs) := lcm z (lcms zs)

lemma dvd_lcm_left : ∀ (x y : int), has_dvd.dvd x (lcm x y) := sorry

lemma dvd_lcm_right : ∀ (x y : int), has_dvd.dvd y (lcm x y) := sorry

lemma dvd_lcms {x : int} : ∀ {zs : list int}, x ∈ zs → has_dvd.dvd x (lcms zs) 
| [] hm := by cases hm
| (z::zs) hm := 
  begin
    unfold lcms, rewrite list.mem_cons_iff at hm,
    cases hm with hm hm, subst hm,
    apply dvd_lcm_left, 
    apply dvd_trans, apply @dvd_lcms zs hm,
    apply dvd_lcm_right, 
  end

lemma nonzero_of_pos {z : int} : z > 0 → z ≠ 0 := sorry

lemma lcm_nonneg (x y : int) : lcm x y ≥ 0 := 
by unfold lcm

lemma lcms_nonneg : ∀ (zs : list int), lcms zs ≥ 0 
| [] := by unfold lcms 
| (z::zs) := by unfold lcms

lemma lcm_pos (x y : int) : x ≠ 0 → y ≠ 0 → lcm x y > 0 := sorry

lemma lcms_pos : ∀ {zs : list int}, (∀ z : int, z ∈ zs → z ≠ 0) → lcms zs > 0
| [] _ := coe_succ_pos _
| (z::zs) hnzs :=
  begin
    unfold lcms, apply lcm_pos, 
    apply hnzs _ (or.inl rfl),
    apply nonzero_of_pos, apply lcms_pos,
    apply list.forall_mem_of_forall_mem_cons hnzs 
  end

lemma lcms_dvd {k : int} : 
  ∀ {zs : list int}, (∀ z ∈ zs, has_dvd.dvd z k) → (has_dvd.dvd (lcms zs) k) 
| [] hk := one_dvd _
| (z::zs) hk :=
  begin
    unfold lcms, apply lcm_dvd,
    apply hk _ (or.inl rfl),
    apply lcms_dvd, 
    apply list.forall_mem_of_forall_mem_cons hk
  end

lemma lcms_distrib (xs ys zs : list int) : 
  list.equiv zs (xs ∪ ys) 
  → lcms zs = lcm (lcms xs) (lcms ys) :=
begin
  intro heqv, apply dvd_antisymm,
  apply lcms_nonneg, apply lcm_nonneg,
  apply lcms_dvd, intros z hz,
  rewrite (list.mem_iff_mem_of_equiv heqv) at hz,
  rewrite list.mem_union at hz, cases hz with hz hz,
  apply dvd_trans (dvd_lcms _) (dvd_lcm_left _ _);
  assumption,
  apply dvd_trans (dvd_lcms _) (dvd_lcm_right _ _);
  assumption,
  apply lcm_dvd; apply lcms_dvd; intros z hz;
  apply dvd_lcms; rewrite (list.mem_iff_mem_of_equiv heqv),
  apply list.mem_union_left hz,
  apply list.mem_union_right _ hz
end

lemma dvd_of_mul_dvd_mul_left : ∀ {x y z : int}, 
  z ≠ 0 → has_dvd.dvd (z * x) (z * y) → has_dvd.dvd x y := sorry

  lemma eq_zero_of_not_gt_zero_of_not_lt_zero (z : int) :
  (¬ z < 0) → (¬ z > 0) → z = 0 := sorry

lemma sign_split (z) : 
  sign z = -1 ∨ sign z = 0 ∨ sign z = 1 :=
begin
  cases z with n n, cases n,
  apply or.inr (or.inl rfl),
  apply or.inr (or.inr rfl),
  apply or.inl rfl
end

lemma neq_zero_of_gt_zero (z : int) :
  z > 0 → z ≠ 0 := sorry

lemma lt_add_of_pos (k z : int) : 0 < k → z < z + k := sorry


lemma abs_neq_zero_of_neq_zero {z : int} (h : z ≠ 0) : abs z ≠ 0 :=
begin
  intro hc, apply h, apply eq_zero_of_abs_eq_zero, apply hc
end

lemma sign_neq_zero_of_neq_zero {z : int} (h : z ≠ 0) : sign z ≠ 0 :=
sorry

lemma mul_le_mul_iff_le_of_pos_left (x y z : int) :
  z > 0 → (z * x ≤ z * y ↔ x ≤ y) := sorry

lemma dvd_iff_exists (x y) :
  has_dvd.dvd x y ↔ ∃ (z : int), z * x = y := sorry

lemma sign_eq_abs_div (a : ℤ) : sign a = (abs a) / a := sorry

lemma div_abs_self (z) : has_div.div z (abs z) = sign z := sorry

lemma sign_self_mul (z : int) : int.sign z * z = abs z := sorry

lemma div_mul_comm (x y z : int) : has_dvd.dvd y x → (x / y) * z = x * z / y := sorry

lemma abs_dvd (x y : int) : has_dvd.dvd (abs x) y ↔ has_dvd.dvd x y := sorry

lemma exists_nat_diff (x y : int) (n : nat) :
  x ≤ y → y < x + int.of_nat n → ∃ (m : nat), m < n ∧ y = x + int.of_nat m := sorry

lemma nonneg_iff_exists (z : int) :
  0 ≤ z ↔ ∃ (n : nat), z = int.of_nat n :=
begin
  cases z with m m, apply true_iff_true, constructor,
  existsi m, refl, apply false_iff_false; intro hc,
  cases hc, cases hc with m hm, cases hm
end

lemma exists_lt_and_lt (x y : int) :
  ∃ z, z < x ∧ z < y := 
begin
  cases (lt_trichotomy x y),
  existsi (pred x), 
  apply and.intro (pred_self_lt _) (lt_trans (pred_self_lt _) h),
  cases h with h h, subst h, 
  existsi (pred x), apply and.intro (pred_self_lt _) (pred_self_lt _),
  existsi (pred y),
  apply and.intro (lt_trans (pred_self_lt _) h) (pred_self_lt _)
end

lemma le_mul_of_pos_left : ∀ {x y : int}, y ≥ 0 → x > 0 → y ≤ x * y :=
begin
  intros x y hy hx,
  have hx' : x ≥ 1 := add_one_le_of_lt hx,
  let h := mul_le_mul hx' (le_refl y) hy _,
  rewrite one_mul at h, apply h, 
  apply le_of_lt hx
end

end int


