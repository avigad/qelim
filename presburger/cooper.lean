import .correctness ..common.arith

open pbgr

#check nat.has_div
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

lemma hd_coeffs_one_normal_prsv_aux  
(p : fm atom)
(hp : fnormal ℤ p)
(z : int)
(hne : z ≠ 0)
(a : atom)
(ha1 : atom_type.normal ℤ a)
(ha2 : divides (hd_coeff a) z)
: atom_type.normal ℤ (hd_coeff_one (z) a) := sorry

lemma hd_coeffs_one_normal_prsv : 
  preserves hd_coeffs_one (fnormal int) := 
begin
  intros p hp, unfold hd_coeffs_one, simp, 
  unfold fnormal, 
  have hne : zlcms (list.map hd_coeff (atoms_dep0 ℤ p)) ≠ 0, 
  apply zlcms_neq_zero, 
  apply allp_map (atom_type.dep0 int) _ _, 
  apply pbgr.atom_type, unfold atoms_dep0,
  apply allp_filter_cond _ _, 
  intros a ha, apply ha, 
  apply and.intro, intro hc, apply hne hc,
  rewrite fnormal_iff_fnormal_alt,
  unfold fnormal_alt, 
  apply map_fm_prsv 
    (λ x, atom_type.normal int x ∧ 
          divides 
            (hd_coeff x) 
            (zlcms (list.map hd_coeff (atoms_dep0 ℤ p)))),
  intros a ha, cases ha with ha1 ha2,
  apply hd_coeffs_one_normal_prsv_aux p hp _ hne _ ha1 ha2,
  intros a ha, apply and.intro, 
  rewrite fnormal_iff_fnormal_alt at hp, apply hp, 
  apply ha, 
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
  let d := zlcms (list.map divisor as) in
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

def qe_cooper := lift_nnf_qe int sqe_cooper

#check @pbgr.lnq_prsv 
lemma qe_cooper_prsv : 
  ∀ p, fnormal int p → ∀ (bs : list int), I (qe_cooper p) bs ↔ I p bs :=
  @pbgr.lnq_prsv sqe_cooper _ _ _ _
  
