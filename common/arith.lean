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

def zlcms (zs : list int) : int :=
int.of_nat $ nat.lcms (list.map int.nat_abs zs)

lemma dvd_zlcms {z : int} (hz : z ≠ 0) : ∀ {zs : list int}, z ∈ zs → has_dvd.dvd z (zlcms zs) 
| [] hm := by cases hm
| (z'::zs) hm := 
  begin
    unfold zlcms, unfold list.map, unfold nat.lcms,
    rewrite dvd_iff_nat_abs_dvd_nat_abs, simp,
    rewrite list.mem_cons_iff at hm, cases hm with hm hm,
    subst hm, apply nat.dvd_lcm_left,
    apply dvd.trans _ (nat.dvd_lcm_right _ _),
    have h := dvd_zlcms hm, unfold zlcms at h,
    rewrite iff.symm int.coe_nat_dvd,
    rewrite nat_abs_dvd, apply h
  end 

lemma zlcms_neq_zero : ∀ {zs : list int} {hzs : ∀ (z : int), z ∈ zs → z ≠ 0}, zlcms zs ≠ 0
| [] _ := begin intro hc, cases hc end
| (z::zs) h :=
  begin
    unfold zlcms, unfold list.map, unfold nat.lcms,
    apply nat.of_nat_neq_zero, apply nat.lcm_neq_zero, 
    apply nat_abs_neq_zero, apply h, apply or.inl rfl,
    let ih := @zlcms_neq_zero zs _, unfold zlcms at ih,
    apply nat.neq_zero_of_of_nat_neq_zero, apply ih, 
    apply list.forall_mem_of_forall_mem_cons h
  end

end int
