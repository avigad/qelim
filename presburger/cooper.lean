import .correctness ..common.arith

open pbgr

def hd_coeff_one : int → atom → atom 
| m (atom.le i (0::ks)) := (atom.le i (0::ks))   
| m (atom.le i (k::ks)) := 
  let m' := int.div m (abs k) in 
  atom.le (m' * i) (int.sign k :: list.map (λ x, m' * x) ks)
| m (atom.dvd d i (0::ks)) := (atom.dvd d i (0::ks)) 
| m (atom.dvd d i (k::ks)) := 
  let m' := int.div m k in 
  atom.dvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m (atom.ndvd d i (0::ks)) := (atom.ndvd d i (0::ks)) 
| m (atom.ndvd d i (k::ks)) := 
  let m' := int.div m k in 
  atom.ndvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m a := a 

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

def hd_coeffs_one (p : fm atom) : fm atom := 
let m := int.zlcms (list.map hd_coeff (atoms_dep0 int p)) in 
A' (atom.dvd m 0 [1]) ∧' (map_fm (hd_coeff_one m) p)

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

def inf_minus : fm atom → fm atom 
| ⊤' := ⊤' 
| ⊥' := ⊥' 
| (A' (atom.le i (k::ks))) := 
  if k < 0 
  then ⊤' 
  else if k > 0
       then ⊥' 
       else A' (atom.le i (0::ks))
| (A' a) := A' a
| (p ∧' q) := and_o (inf_minus p) (inf_minus q)
| (p ∨' q) := or_o (inf_minus p) (inf_minus q)
| (¬' p) := ¬' p
| (∃' p) := ∃' p

def subst (i ks p) := map_fm (asubst i ks) p

variables {α β : Type}

def get_lb : atom → option (int × list int) 
| (atom.le i (k::ks)) :=
  if k > 0 then (i,ks) else none
| (atom.le _ []) := none
| (atom.dvd _ _ _) := none
| (atom.ndvd _ _ _) := none

def list.irange (z : int) : list int :=
list.map int.of_nat (list.range (int.nat_abs z))

def map_neg [has_neg α] (l : list α) : list α := 
list.map (λ x, -x) l 

def qe_cooper_one (p : fm atom) : fm atom := 
  let as := atoms_dep0 int p in 
  let d := int.zlcms (list.map divisor as) in
  let lbs := list.omap get_lb as in
  or_o 
    (disj (list.irange d) (λ n, subst n [] (inf_minus p))) 
    (disj lbs 
      (λ iks, disj (list.irange d) 
                (λ n, subst (iks^.fst + n) (map_neg iks^.snd) p)))

def sqe_cooper := λ x, qe_cooper_one (hd_coeffs_one x)

lemma qe_cooper_one_normal_prsv : preserves qe_cooper_one (fnormal int) := sorry

lemma sqe_cooper_normal_prsv : preserves sqe_cooper (fnormal int) := 
begin
  intros p hp, unfold sqe_cooper,
  apply qe_cooper_one_normal_prsv,
  apply hd_coeffs_one_normal_prsv, 
  apply hp
end

lemma qfree_sqe_cooper_of_nqfree : qfree_of_nqfree sqe_cooper := sorry

def qe_cooper := lift_nnf_qe int sqe_cooper

lemma sqe_cooper_prsv :  
  ∀ (p : fm atom), nqfree p → fnormal ℤ p 
  → ∀ (bs : list ℤ), I (sqe_cooper p) bs ↔ ∃ (b : ℤ), I p (b :: bs) := sorry

lemma qe_cooper_prsv : 
  ∀ p, fnormal int p → ∀ (bs : list int), I (qe_cooper p) bs ↔ I p bs :=
  @pbgr.lnq_prsv sqe_cooper 
    sqe_cooper_normal_prsv 
    qfree_sqe_cooper_of_nqfree 
    sqe_cooper_prsv
    
  
