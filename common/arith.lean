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
int.of_nat (nat.lcm (nat_abs x) (nat_abs y))

def lcms : list int → int
| [] := 1 
| (z::zs) := lcm z (lcms zs)

lemma dvd_lcm_left : ∀ (x y : int), has_dvd.dvd x (lcm x y) := sorry

lemma dvd_lcm_right : ∀ (x y : int), has_dvd.dvd y (lcm x y) := sorry

lemma dvd_lcms {x : int} (hz : x ≠ 0) : ∀ {zs : list int}, x ∈ zs → has_dvd.dvd x (lcms zs) 
| [] hm := by cases hm
| (z::zs) hm := 
  begin
    unfold lcms, rewrite list.mem_cons_iff at hm,
    cases hm with hm hm, subst hm,
    apply dvd_lcm_left, 
    apply dvd_trans, apply @dvd_lcms zs hm,
    apply dvd_lcm_right, 
  end

-- lemma dvd_lcms {z : int} (hz : z ≠ 0) : ∀ {zs : list int}, z ∈ zs → has_dvd.dvd z (lcms zs) 
-- | [] hm := by cases hm
-- | (z'::zs) hm := 
--   begin
--     unfold lcms, unfold list.map, unfold nat.lcms,
--     rewrite dvd_iff_nat_abs_dvd_nat_abs, simp,
--     rewrite list.mem_cons_iff at hm, cases hm with hm hm,
--     subst hm, apply nat.dvd_lcm_left,
--     apply dvd.trans _ (nat.dvd_lcm_right _ _),
--     have h := dvd_lcms hm, unfold lcms at h,
--     rewrite iff.symm int.coe_nat_dvd,
--     rewrite nat_abs_dvd, apply h
--   end 

lemma nonzero_of_pos {z : int} : z > 0 → z ≠ 0 := sorry

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

end int


