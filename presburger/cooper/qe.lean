import ..common.correctness ...common.arith

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

def hd_coeffs_one (p : fm atom) : fm atom := 
let m := int.zlcms (list.map hd_coeff (atoms_dep0 int p)) in 
A' (atom.dvd m 0 [1]) ∧' (map_fm (hd_coeff_one m) p)

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

def list.irange (z : int) : list int :=
list.map int.of_nat (list.range (int.nat_abs z))

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

def qe_cooper := lift_nnf_qe int sqe_cooper
