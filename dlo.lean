import .lnf

variables {α β : Type}

class dlo (α : Type) extends decidable_linear_order α :=
(inh : α)
(btw : ∀ (x z : α), x < z → ∃ (y : α), x < y ∧ y < z)
(blw : ∀ (y : α), ∃ (x : α), x < y)
(abv : ∀ (x : α), ∃ (y : α), x < y)

open dlo

inductive adlo : Type 
| lt : nat → nat → adlo
| eq : nat → nat → adlo

notation x `<'` y := adlo.lt x y 
notation x `='` y := adlo.eq x y 

def I_adlo [dlo β] : adlo → list β → Prop 
| (adlo.lt m n) l := (nth_def (inh _) l m) < (nth_def (inh _) l n) 
| (adlo.eq m n) l := (nth_def (inh _) l m) = (nth_def (inh _) l n) 

def adlo_aneg : adlo → fm adlo
| (adlo.lt m n) := (A' (adlo.eq m n)) ∨' (A' (adlo.lt n m))
| (adlo.eq m n) := (A' (adlo.lt m n)) ∨' (A' (adlo.lt n m))

lemma adlo_aneg_nqfree : ∀ (d : adlo), nqfree (adlo_aneg d)  
| (adlo.lt m n) := and.intro trivial trivial
| (adlo.eq m n) := and.intro trivial trivial

lemma adlo_aneg_prsv [dlo β] : ∀ (d : adlo) (l : list β), 
  interp I_adlo l (adlo_aneg d) = interp I_adlo l (¬' A' d) 
| (adlo.lt m n) l := 
  begin
    unfold adlo_aneg, unfold interp, 
    unfold I_adlo, apply propext, 
    apply iff.intro, 
    intro H, apply not_lt_of_ge,
    apply le_of_lt_or_eq, 
    cases H with H H, apply or.inr, 
    apply eq.symm H, apply or.inl, apply H,
    intro H, apply eq_or_lt_of_not_lt, 
    apply H
  end
| (adlo.eq m n) l := 
  begin
    unfold adlo_aneg, unfold interp, unfold I_adlo,
    apply propext, apply iff.intro, 
    intro H, cases H with H H, 
    apply ne_of_lt H, apply ne_of_gt H, 
    intro H, apply lt_or_gt_of_ne H  
  end

def dlo_dep0 : adlo → Prop 
| (adlo.lt m n) := m = 0 ∨ n = 0
| (adlo.eq m n) := m = 0 ∨ n = 0

def dlo_decr : adlo → adlo
| (adlo.lt m n) := (adlo.lt (m-1) (n-1))
| (adlo.eq m n) := (adlo.eq (m-1) (n-1))

theorem atom_adlo [dlo β] : atom adlo β := 
{ I_a := I_adlo,
  aneg := adlo_aneg,
  aneg_nqfree := adlo_aneg_nqfree,
  aneg_prsv := adlo_aneg_prsv,
  dep0 := dlo_dep0,
  decr := dlo_decr } 

def dlo_sovable0 : adlo → Prop  
| (adlo.lt m n) := false
| (adlo.eq m n) := m = 0 ∨ n = 0 

def dlo_trivial : adlo → Prop  
| (adlo.lt m n) := false
| (adlo.eq m n) := m = n

def dlo_subst0 : nat → nat → adlo → adlo
| i j (m <' n) := subst_idx i j m <' subst_idx i j n
| i j (m =' n) := subst_idx i j m =' subst_idx i j n

theorem atomeq_adlo [dlo β] : atomeq adlo β := 
{ I_a := I_adlo,
  aneg := adlo_aneg,
  aneg_nqfree := adlo_aneg_nqfree,
  aneg_prsv := adlo_aneg_prsv,
  dep0 := dlo_dep0,
  decr := dlo_decr,
  solv0 := dlo_sovable0,
  trivial := dlo_trivial,
  subst0 := dlo_subst0 } 

#exit

def lt_has_0 : adlo → Prop 
| (adlo.eq _ _) := false
| (adlo.lt _ 0) := true
| (adlo.lt 0 _) := true
| (adlo.lt _ _) := false

def lt_single_0 : adlo → Prop 
| (adlo.eq _ _) := false
| (adlo.lt 0 0) := false
| (adlo.lt _ 0) := true
| (adlo.lt 0 _) := true
| (adlo.lt (i+1) (j+1)) := false

def qe_dlo_aux : ∀ (l : list adlo) (H : allp l lt_single_0), (list nat × list nat)
| [] := λ _, ([],[]) 
| (a::as) :=
  match a with 
  | (adlo.eq _ _) := begin intro H, exfalso, apply H^.elim_left end
  | (adlo.lt 0 0) := begin intro H, exfalso, apply H^.elim_left end
  | (adlo.lt (i+1) 0) := λ H, let (lbs,rbs) := qe_dlo_aux as (H^.elim_right) in (i::lbs,rbs)
  | (adlo.lt 0 (j+1)) := λ H, let (lbs,rbs) := qe_dlo_aux as (H^.elim_right) in (lbs,j::rbs)
  | (adlo.lt (i+1) (j+1)) := begin intro H, exfalso, apply H^.elim_left end
  end

lemma allp_single_0_of : ∀ (as : list adlo) (H : allp as lt_has_0) (HZ : (0 <' 0) ∉ as), allp as lt_single_0  
| [] _ _ := trivial 
| ((adlo.eq _ _)::as) H HZ := 
  begin exfalso, apply H^.elim_left end
| ((adlo.lt 0 0)::as) H HZ := 
  begin exfalso, apply HZ, apply or.inl, refl end
| ((adlo.lt (i+1) 0)::as) H HZ := 
  begin 
    apply and.intro trivial, 
    apply allp_single_0_of as H^.elim_right, 
    intro HC, apply HZ, apply or.inr HC
  end
| ((adlo.lt 0 (j+1))::as) H HZ := 
  begin
    apply and.intro trivial, 
    apply allp_single_0_of as H^.elim_right, 
    intro HC, apply HZ, apply or.inr HC
  end
| ((adlo.lt (i+1) (j+1))::as) H HZ := 
  begin exfalso, apply H^.elim_left end

def qe_dlo [decidable_eq adlo] (as : list adlo) (H : allp as lt_has_0) : fm adlo := 
if HZ : (adlo.lt 0 0) ∈ as
then ⊥' 
else let (lbs,rbs) := qe_dlo_aux as (allp_single_0_of as H HZ) in 
     let prs := list.product lbs rbs in 
     list_conj $ list.map (λ pr, A' (prod.fst pr <' prod.snd pr)) prs



#exit


def dlo_qelim [atom adlo β] : fm adlo → fm adlo :=   
@lift_nnf_qe _ β _ dlo_qe 

lemma dlo_qe_qfree : ∀ (p : fm adlo), nqfree p → qfree (dlo_qe p) := sorry

lemma dlo_qe_prsv [atom adlo β] : ∀ (p : fm adlo) (xs : list β), I (dlo_qe p) xs = ∃ x, I p (x::xs) := sorry

theorem dlo_qelim_prsv [atom adlo β] : 
  ∀ (p : fm adlo) (xs : list β), I (@dlo_qelim β _ p) xs = I p xs :=  
lnq_prsv dlo_qe dlo_qe_qfree dlo_qe_prsv