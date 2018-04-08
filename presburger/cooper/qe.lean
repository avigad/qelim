import ..common.correctness ...common.arith

open pbgr

def hd_coeff_one : int → atom → atom 
| m (atom.le i (0::ks)) := (atom.le i (0::ks))   
| m (atom.le i (k::ks)) := 
  let m' := has_div.div m (abs k) in 
  atom.le (m' * i) (int.sign k :: list.map (λ x, m' * x) ks)
| m (atom.dvd d i (0::ks)) := (atom.dvd d i (0::ks)) 
| m (atom.dvd d i (k::ks)) := 
  let m' := has_div.div m k in 
  atom.dvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m (atom.ndvd d i (0::ks)) := (atom.ndvd d i (0::ks)) 
| m (atom.ndvd d i (k::ks)) := 
  let m' := has_div.div m k in 
  atom.ndvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)
| m a := a 

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

lemma subst_prsv (i ks xs) : 
  ∀ p, I (subst i ks p) xs ↔ I p ((i + list.dot_prod ks xs)::xs) := sorry 

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

lemma list.mem_irange (z y) : 0 ≤ z → z < y → z ∈ list.irange y := sorry

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
