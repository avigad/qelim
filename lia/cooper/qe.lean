import ..common.correctness ...common.int

namespace lia

def hd_coeff_one : int → atom → atom 
| m (atom.le i (k::ks)) := 
  if k = 0 
  then (atom.le i (0::ks))  
  else let m' := has_div.div m (abs k) in 
       atom.le (m' * i) (int.sign k :: list.map (λ x, m' * x) ks)
| m (atom.dvd d i (k::ks)) :=
  if k = 0 
  then (atom.dvd d i (0::ks)) 
  else let m' := has_div.div m k in 
       atom.dvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m (atom.ndvd d i (k::ks)) := 
  if k = 0 
  then (atom.ndvd d i (0::ks)) 
  else let m' := has_div.div m k in 
       atom.ndvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m (atom.le i []) := (atom.le i [])
| m (atom.dvd d i []) := (atom.dvd d i []) 
| m (atom.ndvd d i []) := (atom.ndvd d i []) 

def hd_coeff_one' : int → atom → atom 
| m (atom.le i (0::ks)) := (atom.le i (0::ks))   
| m (atom.le i (int.of_nat (n+1) :: ks)) :=
  let k := int.of_nat (n+1) in 
  let m' := has_div.div m (abs k) in 
  atom.le (m' * i) (int.sign k :: list.map (λ x, m' * x) ks)
| m (atom.le i (int.neg_succ_of_nat n :: ks)) :=
  let k := int.neg_succ_of_nat n in 
  let m' := has_div.div m (abs k) in 
  atom.le (m' * i) (int.sign k :: list.map (λ x, m' * x) ks)
| m (atom.dvd d i (0::ks)) := (atom.dvd d i (0::ks)) 
| m (atom.dvd d i (int.of_nat (n+1) :: ks)) := 
  let k := int.of_nat (n+1) in 
  let m' := has_div.div m k in 
  atom.dvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m (atom.dvd d i (int.neg_succ_of_nat n ::ks)) := 
  let k := int.neg_succ_of_nat n in 
  let m' := has_div.div m k in 
  atom.dvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m (atom.ndvd d i (0::ks)) := (atom.ndvd d i (0::ks)) 
| m (atom.ndvd d i (int.of_nat (n+1) :: ks)) := 
  let k := int.of_nat (n+1) in 
  let m' := has_div.div m k in 
  atom.ndvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m (atom.ndvd d i (int.neg_succ_of_nat n :: ks)) := 
  let k := int.neg_succ_of_nat n in 
  let m' := has_div.div m k in 
  atom.ndvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m (atom.le i []) := (atom.le i [])
| m (atom.dvd d i []) := (atom.dvd d i []) 
| m (atom.ndvd d i []) := (atom.ndvd d i []) 

def coeffs_lcm (p) := 
  int.lcms (list.map hd_coeff (atoms_dep0 int p))

def divisors_lcm (p) := 
  int.lcms (list.map divisor (atoms_dep0 int p))

def hd_coeffs_one (p : fm atom) : fm atom := 
A' (atom.dvd (coeffs_lcm p) 0 [1]) ∧' (map_fm (hd_coeff_one (coeffs_lcm p)) p)

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


def get_lb : atom → option (int × list int) 
| (atom.le i (k::ks)) :=
  if k > 0 then (i,ks) else none
| (atom.le _ []) := none
| (atom.dvd _ _ _) := none
| (atom.ndvd _ _ _) := none

def bnd_points (p) := 
  list.filter_map get_lb (atoms_dep0 ℤ p)

def list.irange (z : int) : list int :=
list.map int.of_nat (list.range (int.nat_abs z))

lemma list.mem_irange (z y : int) : 
  0 ≤ z → 0 ≤ y → z < y → z ∈ list.irange y := 
begin
  intros hz hy hzy, unfold list.irange,
  rewrite list.mem_map, 
  rewrite int.nonneg_iff_exists at hz,
  cases hz with n hn, subst hn, existsi n,
  apply and.intro _ rfl,
  rewrite list.mem_range, 
  rewrite iff.symm int.coe_nat_lt,
  have heq : ↑(int.nat_abs y) = int.of_nat (int.nat_abs y),
  refl, rewrite heq,
  rewrite int.of_nat_nat_abs_eq_of_nonneg hy, apply hzy,
end

def qe_cooper_one (p : fm atom) : fm atom := 
  let as := atoms_dep0 int p in 
  let d := int.lcms (list.map divisor as) in
  let lbs := list.filter_map get_lb as in
  or_o 
    (disj (list.irange d) (λ n, subst n [] (inf_minus p))) 
    (disj lbs 
      (λ iks, disj (list.irange d) 
                (λ n, subst (iks^.fst + n) (map_neg iks^.snd) p)))

def sqe_cooper := λ x, qe_cooper_one (hd_coeffs_one x)

def qe_cooper := lift_nnf_qe int sqe_cooper

end lia