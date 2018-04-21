import ...common.int ...common.atom ...common.list 

namespace lia 

open list

variables {α β : Type}

inductive atom : Type 
| le : int → list int → atom
| dvd : int → int → list int → atom
| ndvd : int → int → list int → atom

-- | (atom.le i ks) := sorry
-- | (atom.dvd d i ks) := sorry
-- | (atom.ndvd d i ks) := sorry

meta def coeffs_to_format : nat → list int → format 
| _ [] := "_"
| n [k] := to_fmt k ++ "x" ++ to_fmt n
| n (k1::k2::ks) := to_fmt k1 ++ "x" ++ to_fmt n ++ " + " ++ coeffs_to_format (n+1) (k2::ks)

meta def atom_to_format : atom → format 
| (atom.le i ks) := to_fmt i ++ " ≤ " ++ coeffs_to_format 0 ks
| (atom.dvd d i ks) := to_fmt d ++ " | " ++ to_fmt i ++ " + " ++ coeffs_to_format 0 ks
| (atom.ndvd d i ks) := "¬(" ++ atom_to_format (atom.dvd d i ks) ++ ")"

meta instance : has_to_format atom := 
⟨atom_to_format⟩ 

meta instance : has_to_tactic_format atom := 
has_to_format_to_has_to_tactic_format _

meta instance : has_reflect int :=
by tactic.mk_has_reflect_instance 

meta instance has_reflect_atom : has_reflect atom :=
by tactic.mk_has_reflect_instance 

instance dec_eq : decidable_eq atom := 
by tactic.mk_dec_eq_instance

open atom 

def val : list int → atom → Prop 
| xs (le i ks) := i ≤ list.dot_prod ks xs
| xs (dvd d i ks) := has_dvd.dvd d (i + list.dot_prod ks xs)
| xs (ndvd d i ks) := ¬ (has_dvd.dvd d (i + list.dot_prod ks xs))

def neg : atom → fm atom
| (le i ks) := fm.atom (atom.le (1 - i) (list.map has_neg.neg ks))
| (dvd d i ks)  := fm.atom (ndvd d i ks)
| (ndvd d i ks) := fm.atom (dvd d i ks)

def neg_prsv : ∀ (a : atom) (xs : list ℤ), interp val xs (neg a) ↔ interp val xs (¬' A' a) 
| (le i ks)     xs := 
  begin 
    unfold neg, unfold interp, 
    unfold val, 
    apply 
    (calc 
          (1 - i ≤ list.dot_prod (list.map has_neg.neg ks) xs) 
        ↔ (has_neg.neg (dot_prod (list.map has_neg.neg ks) xs) ≤ has_neg.neg (1 - i)) : 
          by {apply iff.intro, apply neg_le_neg, apply le_of_neg_le_neg}
    ... ↔ (dot_prod ks xs ≤ has_neg.neg (1 - i)) : 
          begin rewrite (@neg_dot_prod int _ ks xs), simp, end
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

meta def decr_prsv_aux : tactic unit := 
`[unfold decr, unfold val, 
  cases ks with k ks, 
  simp, repeat {rewrite nil_dot_prod},
  unfold dep0 at h, unfold hd_coeff at h, 
  unfold list.head_dft at h, 
  have h' := classical.by_contradiction h, 
  clear h, subst h', cases bs with b' bs', 
  simp, rewrite cons_dot_prod_cons,
  rewrite zero_mul, rewrite zero_add, simp]

lemma decr_prsv : ∀ (a : atom), ¬dep0 a → ∀ (b : ℤ) (bs : list ℤ), 
  val bs (decr a) ↔ val (b :: bs) a
| (le i ks)      h b bs := by decr_prsv_aux
| (dvd d i ks)   h b bs := by decr_prsv_aux
| (ndvd d i ks)  h b bs := by decr_prsv_aux

def normal : atom → Prop 
| (le i ks)     := true
| (dvd d i ks)  := d ≠ 0
| (ndvd d i ks) := d ≠ 0 

def divisor : atom → int 
| (le i ks)     := 1
| (dvd d i ks)  := d 
| (ndvd d i ks) := d 

lemma normal_iff_divisor_nonzero {a : atom} :
  normal a ↔ divisor a ≠ 0 :=
begin
  cases a with i ks d i ks d i ks,
  apply true_iff_true, trivial, 
  intro hc, cases hc, refl, refl
end

def dec_normal : decidable_pred normal  
| (le i ks)     := decidable.is_true trivial
| (dvd d i ks)  := by apply dec_not_pred_of_dec_pred
| (ndvd d i ks) := by apply dec_not_pred_of_dec_pred

meta def neg_prsv_normal_aux :=
  `[unfold neg at hb, unfold atoms at hb, 
    rewrite (eq_of_mem_singleton hb), trivial]

lemma neg_prsv_normal : ∀ (a : atom), normal a → ∀ (b : atom), b ∈ @atoms _ _ (neg a) → normal b 
| (le i ks)     h b hb := by neg_prsv_normal_aux
| (dvd d i ks)  h b hb := by neg_prsv_normal_aux
| (ndvd d i ks) h b hb := by neg_prsv_normal_aux

lemma decr_prsv_normal : ∀ (a : atom), normal a → ¬dep0 a → normal (decr a) 
| (le i ks)     hn hd := by unfold decr
| (dvd d i ks)  hn hd := begin intro hc, apply hn hc end 
| (ndvd d i ks) hn hd := begin intro hc, apply hn hc end 

instance : atom_type atom int := 
{ val := val,
  neg := neg,
  neg_nqfree := 
    begin intro a, cases a; trivial, end,
  neg_prsv := neg_prsv,
  dep0 := dep0,
  dec_dep0 := 
    begin intro a, apply dec_not_pred_of_dec_pred end,
  decr := decr,
  decr_prsv := decr_prsv,
  inh := 0,
  dec_eq := _,
  normal := normal, 
  dec_normal := dec_normal,
  neg_prsv_normal := neg_prsv_normal,
  decr_prsv_normal := decr_prsv_normal }

def asubst (i') (ks') : atom → atom 
| (le i (k::ks))     := le (i - (k * i')) (comp_add (map_mul k ks') ks)
| (dvd d i (k::ks))  := dvd d (i + (k * i')) (comp_add (map_mul k ks') ks)
| (ndvd d i (k::ks)) := ndvd d (i + (k * i')) (comp_add (map_mul k ks') ks)
| a := a

meta def asubst_prsv_tac := 
`[unfold asubst, unfold val, rewrite add_assoc,
  have he : (i' * k + dot_prod (comp_add (map_mul k ks') ks) xs) 
            = (dot_prod (k :: ks) ((i' + dot_prod ks' xs) :: xs)),
  rewrite cons_dot_prod_cons,
  rewrite mul_add, rewrite mul_comm, simp, 
  rewrite comp_add_dot_prod, 
  simp, rewrite mul_comm at he, rewrite he]

meta def asubst_prsv_aux := 
`[unfold asubst, unfold val, 
  repeat {rewrite nil_dot_prod}]

lemma asubst_prsv (i' ks' xs) : 
  ∀ a, val xs (asubst i' ks' a) ↔ val ((i' + dot_prod ks' xs)::xs) a 
| (le i (k::ks))     := 
  begin
    unfold asubst, simp, unfold val, 
    rewrite add_le_iff_le_sub, simp, 
    have he : (i' * k + dot_prod (comp_add (map_mul k ks') ks) xs) 
               = (dot_prod (k :: ks) ((i' + dot_prod ks' xs) :: xs)),
    rewrite cons_dot_prod_cons,
    rewrite mul_add, rewrite mul_comm, simp, 
    rewrite comp_add_dot_prod, 
    simp, rewrite mul_comm at he, 
    simp at *, rewrite he
  end
| (dvd d i (k::ks))  := by asubst_prsv_tac
| (ndvd d i (k::ks)) := by asubst_prsv_tac
| (le i [])     := by asubst_prsv_aux
| (dvd d i [])  := by asubst_prsv_aux
| (ndvd d i []) := by asubst_prsv_aux


end lia
