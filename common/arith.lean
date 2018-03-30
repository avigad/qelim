import .list ...mathlib.data.int.basic ...mathlib.data.nat.gcd

def divides (m n : nat) : Prop := ∃ k, m * k = n 

lemma divisor_le (m n) : divides m n → n ≠ 0 → m ≤ n := 
begin
  intros h hn, cases h with k hk, cases k with k,
  exfalso, apply hn, rewrite mul_zero at hk, rewrite hk,
  rewrite eq.symm hk, rewrite nat.mul_succ,
  apply nat.le_add_left
end

lemma ex_pred_of_neq_zero (m) : m ≠ 0 → ∃ m', m = nat.succ m' := 
begin
  intro hm, cases m with m', exfalso, apply hm, refl,
  existsi m', refl
end

lemma gt_zero_of_neq_zero (n) : n ≠ 0 → n > 0 :=
begin
  intro h, cases n, exfalso, apply h, refl, 
  apply nat.zero_lt_succ
end

lemma gcd_divides : ∀ (m n : nat), divides (nat.gcd m n) m ∧ divides (nat.gcd m n) n
| 0 n := 
  begin 
    apply and.intro, existsi 0, rewrite mul_zero,
    unfold nat.gcd, existsi 1, rewrite mul_one
  end
| (m+1) n :=
  have (n % nat.succ m < nat.succ m), from (nat.mod_lt _ $ nat.succ_pos _),
  begin
    unfold nat.gcd, apply and.intro, 
    apply and.elim_right (gcd_divides _ _),
    cases (gcd_divides (n % nat.succ m) (nat.succ m)) with h1 h2,
    cases h1 with i hi, cases h2 with j hj,
    existsi (j * (n/(m+1))) + i,
    rewrite mul_add, rewrite hi,
    rewrite eq.symm (mul_assoc _ _ _),
    rewrite hj, rewrite add_comm,
    apply nat.mod_add_div
  end

lemma nat.mul_nonzero {m n : nat} : m ≠ 0 → n ≠ 0 → m * n ≠ 0 := 
begin
  intros hm hn hc, apply hm,
  apply eq.trans, apply eq.symm, 
  apply nat.mul_div_cancel,
  apply gt_zero_of_neq_zero, apply hn,
  rewrite hc, apply nat.zero_div
end

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

theorem gcd_neq_zero : ∀ (m n : nat), m ≠ 0 → n ≠ 0 → (nat.gcd m n) ≠ 0 
| 0 n hm hn := begin exfalso, apply hm, refl end
| (nat.succ m) n hm hn := 
  have (n % nat.succ m < nat.succ m), from (nat.mod_lt _ $ nat.succ_pos _),
  begin
    unfold nat.gcd, 
    apply (@classical.by_cases (n % nat.succ m ≠ 0) _ _ _); intro h,
    apply gcd_neq_zero, apply h, intro hc, cases hc,
    rewrite (classical.by_contradiction h), intro hc, cases hc 
  end

lemma lcm_neq_zero (m n : nat) : m ≠ 0 → n ≠ 0 → (nat.lcm m n) ≠ 0 :=
begin
  intros hm hn hc,
  have h := nat.gcd_mul_lcm m n,
  rewrite hc at h, rewrite mul_zero at h,
  apply nat.mul_nonzero hm hn, 
  apply eq.symm h
end

lemma of_nat_neq_zero (n : nat) : n ≠ 0 → int.of_nat n ≠ 0 :=
begin
  intro hn, cases n, exfalso, apply hn, refl,
  intro hc, cases hc
end

lemma neq_zero_of_of_nat_neq_zero {n : nat} : int.of_nat n ≠ 0 → n ≠ 0 :=
begin
  cases n, intro hc, exfalso, apply hc, refl,
  intros _ hc, cases hc 
end

lemma nat_abs_neq_zero (z : int) : z ≠ 0 → int.nat_abs z ≠ 0 := 
begin
  intro hz, cases z with n n, simp,
  apply neq_zero_of_of_nat_neq_zero hz,
  simp, intro hc, cases hc
end

lemma zlcms_neq_zero : ∀ {zs : list int} {hzs : ∀ (z : int), z ∈ zs → z ≠ 0}, zlcms zs ≠ 0
| [] _ := begin intro hc, cases hc end
| (z::zs) h :=
  begin
    unfold zlcms, unfold list.map, unfold lcms,
    apply of_nat_neq_zero, apply lcm_neq_zero, 
    apply nat_abs_neq_zero, apply h, apply or.inl rfl,
    let ih := @zlcms_neq_zero zs _, unfold zlcms at ih,
    apply neq_zero_of_of_nat_neq_zero, apply ih, 
    apply list.forall_mem_of_forall_mem_cons h
  end
