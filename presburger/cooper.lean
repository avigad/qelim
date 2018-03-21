import .correctness

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
let m := zlcms (list.map hd_coeff (atoms_dep0 int p)) in 
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

