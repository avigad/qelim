import .atom .auxiliary

namespace pbgr 

variables {α β : Type}

inductive atom : Type 
| le : int → list int → atom
| dvd : int → int → list int → atom
| ndvd : int → int → list int → atom

def dec_eq : decidable_eq atom := 
by tactic.mk_dec_eq_instance

open atom 

def divides (m n : int) : Prop := int.rem n m = 0

def val : atom → list int → Prop 
| (le i ks) xs := i ≤ dot_prod ks xs
| (dvd d i ks) xs := divides d (i + dot_prod ks xs)
| (ndvd d i ks) xs := ¬ (divides d (i + dot_prod ks xs))

def aneg : atom → fm atom
| (le i ks) := fm.atom (atom.le (1 - i) (list.map has_neg.neg ks))
| (dvd d i ks)  := fm.atom (ndvd d i ks)
| (ndvd d i ks) := fm.atom (dvd d i ks)

def aneg_prsv : ∀ (a : atom) (xs : list ℤ), interp val xs (aneg a) ↔ interp val xs (¬' A' a) 
| (le i ks)     xs := 
  begin 
    unfold aneg, unfold interp, 
    unfold val, 
    apply 
    (calc 
          (1 - i ≤ dot_prod (list.map has_neg.neg ks) xs) 
        ↔ (has_neg.neg (dot_prod (list.map has_neg.neg ks) xs) ≤ has_neg.neg (1 - i)) : 
          by {apply iff.intro, apply neg_le_neg, apply le_of_neg_le_neg}
    ... ↔ (dot_prod ks xs ≤ has_neg.neg (1 - i)) : 
          begin rewrite (@exp_neg_dot_prod int _ ks xs), simp, end
    ... ↔ (dot_prod ks xs ≤ i - 1) : 
           by rewrite neg_sub
    ... ↔ (dot_prod ks xs < i) : 
          begin
            apply iff.intro,
            apply int.lt_of_le_sub_one,
            apply int.le_sub_one_of_lt 
          end
    ... ↔ ¬i ≤ dot_prod ks xs : 
          begin
            apply iff.intro,
            apply not_le_of_gt,
            apply lt_of_not_ge
          end )
  end
| (dvd d i ks)  xs := by refl
| (ndvd d i ks) xs := by apply iff_not_not

def decr : atom → atom 
| (le i ks)     := le i (list.tail ks)
| (dvd d i ks)  := dvd d i (list.tail ks)
| (ndvd d i ks) := ndvd d i (list.tail ks)

def hd_coeff : atom → int 
| (le i ks)     := list.head_dft 0 ks
| (dvd d i ks)  := list.head_dft 0 ks
| (ndvd d i ks) := list.head_dft 0 ks

def dep0 (a) := hd_coeff a ≠ 0

instance : atom_type atom int := 
{ val := val,
  aneg := aneg,
  aneg_nqfree := 
    begin intro a, cases a; trivial, end,
  aneg_prsv := aneg_prsv,
  dep0 := dep0,
  dec_dep0 := 
    begin intro a, apply dec_not_pred_of_dec_pred end,
  decr := decr,
  decr_prsv := sorry ,
  inh := 0,
  dec_eq := dec_eq }

end pbgr
