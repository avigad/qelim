import .nat ...mathlib.data.int.basic

namespace int

lemma le_iff_zero_le_sub (a b) : a ≤ b ↔ (0 : int) ≤ b - a := 
begin
  rewrite le_sub, simp
end

lemma abs_dvd (x y : int) : has_dvd.dvd (abs x) y ↔ has_dvd.dvd x y :=
begin rewrite abs_eq_nat_abs, apply nat_abs_dvd end

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

lemma nat_abs_nonzero (z : int) : z ≠ 0 → int.nat_abs z ≠ 0 := 
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

lemma dvd_lcm_left : ∀ (x y : int), has_dvd.dvd x (lcm x y) := 
begin
  intros x y, unfold lcm, rewrite iff.symm (abs_dvd _ _),
  rewrite abs_eq_nat_abs, rewrite coe_nat_dvd,
  apply nat.dvd_lcm_left
end

lemma dvd_lcm_right : ∀ (x y : int), has_dvd.dvd y (lcm x y) :=
begin
  intros x y, unfold lcm, rewrite iff.symm (abs_dvd _ _),
  rewrite abs_eq_nat_abs, rewrite coe_nat_dvd,
  apply nat.dvd_lcm_right
end
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

lemma nonzero_of_pos {z : int} : z > 0 → z ≠ 0 := 
begin intros hgt heq, subst heq, cases hgt end

lemma lcm_nonneg (x y : int) : lcm x y ≥ 0 := 
by unfold lcm

lemma lcms_nonneg : ∀ (zs : list int), lcms zs ≥ 0 
| [] := by unfold lcms 
| (z::zs) := by unfold lcms

lemma lcm_pos (x y : int) : x ≠ 0 → y ≠ 0 → lcm x y > 0 := 
begin
  intros hx hy, unfold lcm, unfold gt,
  rewrite coe_nat_pos, 
  let h := @nat.pos_iff_ne_zero, unfold gt at h,
  rewrite h, apply nat.lcm_nonzero;
  apply nat_abs_nonzero; assumption
end

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

-- lemma dvd_of_mul_dvd_mul_left : ∀ {x y z : int}, 
--   z ≠ 0 → has_dvd.dvd (z * x) (z * y) → has_dvd.dvd x y := sorry

lemma eq_zero_of_nonpos_of_nonzero (z : int) :
(¬ z < 0) → (¬ z > 0) → z = 0 := 
begin
  cases (lt_trichotomy z 0) with h h,
  intro hc, cases (hc h),
  cases h with h h, intros _ _, apply h,
  intros _ hc, cases (hc h)
end

lemma sign_split (z) : 
  sign z = -1 ∨ sign z = 0 ∨ sign z = 1 :=
begin
  cases z with n n, cases n,
  apply or.inr (or.inl rfl),
  apply or.inr (or.inr rfl),
  apply or.inl rfl
end

-- lemma abs_neq_zero_of_neq_zero {z : int} (h : z ≠ 0) : abs z ≠ 0 :=
-- begin
--   intro hc, apply h, apply eq_zero_of_abs_eq_zero, apply hc
-- end

lemma mul_le_mul_iff_le_of_pos_left (x y z : int) :
  z > 0 → (z * x ≤ z * y ↔ x ≤ y) := 
begin
  intro hz, apply iff.intro; intro h,
  let h' := @int.div_le_div _ _ z hz h,
  repeat {rewrite mul_comm z at h',
  rewrite int.mul_div_cancel _ (nonzero_of_pos hz) at h'},
  apply h', repeat {rewrite mul_comm z},
  apply int.mul_le_of_le_div hz, 
  rewrite int.mul_div_cancel _ (nonzero_of_pos hz),
  apply h 
end

lemma mul_le_mul_iff_le_of_neg_left (x y z : int) :
  z < 0 → (z * x ≤ z * y ↔ y ≤ x) := 
begin
  intros hz,
  rewrite eq.symm (neg_neg z),
  repeat {rewrite eq.symm (neg_mul_eq_neg_mul (-z) _)},
  rewrite neg_le_neg_iff,
  apply mul_le_mul_iff_le_of_pos_left,
  unfold gt, rewrite lt_neg, apply hz
end

lemma dvd_iff_exists (x y) :
  has_dvd.dvd x y ↔ ∃ (z : int), z * x = y := 
begin
  apply iff.intro; intro h, 
  existsi (y / x), apply int.div_mul_cancel h,
  cases h with z hz, subst hz, 
  apply dvd_mul_left
end

lemma div_mul_comm (x y z : int) : has_dvd.dvd y x → (x / y) * z = x * z / y := 
begin
  intro h, rewrite mul_comm x, 
  rewrite int.mul_div_assoc _ h, rewrite mul_comm,
end

lemma nonneg_iff_exists (z : int) :
  0 ≤ z ↔ ∃ (n : nat), z = ↑n :=
begin
  cases z with m m, apply true_iff_true, constructor,
  existsi m, refl, apply false_iff_false; intro hc,
  cases hc, cases hc with m hm, cases hm
end

lemma exists_nat_diff (x y : int) (n : nat) :
  x ≤ y → y < x + ↑n → ∃ (m : nat), m < n ∧ y = x + ↑m := 
begin
  intros hxy hyx, 
  rewrite iff.symm (sub_nonneg) at hxy,
  rewrite nonneg_iff_exists at hxy, 
  cases hxy with m hm, existsi m,
  rewrite iff.symm sub_lt_iff_lt_add' at hyx,
  apply and.intro, rewrite iff.symm coe_nat_lt,
  rewrite eq.symm hm, apply hyx,
  rewrite eq.symm hm, rewrite add_sub, simp,
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

lemma lt_mul_of_nonneg_right : ∀ {x y z : int}, x < y → y ≥ 0 → z > 0 → x < y * z :=
begin
  intros x y z hxy hy hz,
  have h := @mul_lt_mul _ _ x 1 y z hxy,
  rewrite mul_one at h, apply h,
  apply add_one_le_of_lt hz, 
  apply int.zero_lt_one, apply hy
end

lemma zero_mul (z : int) : 
  int.of_nat 0 * z = 0 := 
eq.trans (refl _) (zero_mul _)

lemma mul_zero (z : int) : 
  z * int.of_nat 0 = 0 := 
eq.trans (refl _) (mul_zero _)

lemma one_mul (z : int) : 
  int.of_nat 1 * z = z := 
eq.trans (refl _) (one_mul _)

lemma neg_one_mul (z : int) : 
  (int.neg_succ_of_nat 0) * z = -z := 
eq.trans (refl _) (neg_one_mul _)

lemma zero_add (z : int) : 
  int.of_nat 0 + z = z := 
eq.trans (refl _) (zero_add _)

lemma coe_eq_of_nat {n : nat} :
  ↑n = int.of_nat n := refl _

lemma coe_neg_succ_eq_neg_succ_of_nat {n : nat} :
  -↑(nat.succ n) = int.neg_succ_of_nat n := refl _


end int
