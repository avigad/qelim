import .list 

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
  intros hm hn, unfold nat.lcm, 
  rewrite nat.div_def, 
  apply (@cases_ite _ _ (λ x, x ≠ 0)), simp,
  intros h hc, rewrite nat.succ_add at hc,
  cases hc, intro hc, 
  exfalso, apply hc, apply and.intro, 
  apply gt_zero_of_neq_zero, 
  apply gcd_neq_zero; assumption, 
  apply le_trans, apply divisor_le,
  apply and.elim_left (gcd_divides _ _), apply hm,
  cases (ex_pred_of_neq_zero n hn) with n' hn',
  subst hn', rewrite nat.mul_succ,
  apply nat.le_add_left
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

lemma zlcms_neq_zero : ∀ {zs} {hzs : allp (λ (z : int), z ≠ 0) zs}, zlcms zs ≠ 0
| [] _ := begin intro hc, cases hc end
| (z::zs) h :=
  begin
    unfold zlcms, unfold list.map, unfold lcms,
    apply of_nat_neq_zero, apply lcm_neq_zero, 
    apply nat_abs_neq_zero, apply h, apply or.inl rfl,
    let ih := @zlcms_neq_zero zs _, unfold zlcms at ih,
    apply neq_zero_of_of_nat_neq_zero, apply ih, 
    apply allp_tail_of_allp h 
  end