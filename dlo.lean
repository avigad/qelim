import .ldeq

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

def dlo_val [dlo β] : adlo → list β → Prop 
| (adlo.lt m n) l := (list.nth_dft (inh _) l m) < (list.nth_dft (inh _) l n) 
| (adlo.eq m n) l := (list.nth_dft (inh _) l m) = (list.nth_dft (inh _) l n) 

def adlo_aneg : adlo → fm adlo
| (adlo.lt m n) := (A' (adlo.eq m n)) ∨' (A' (adlo.lt n m))
| (adlo.eq m n) := (A' (adlo.lt m n)) ∨' (A' (adlo.lt n m))

lemma adlo_aneg_nqfree : ∀ (d : adlo), nqfree (adlo_aneg d)  
| (adlo.lt m n) := and.intro trivial trivial
| (adlo.eq m n) := and.intro trivial trivial

lemma adlo_aneg_prsv [dlo β] : ∀ (d : adlo) (l : list β), 
  interp dlo_val l (adlo_aneg d) = interp dlo_val l (¬' A' d) 
| (adlo.lt m n) l := 
  begin
    unfold adlo_aneg, unfold interp, 
    unfold dlo_val, apply propext, 
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
    unfold adlo_aneg, unfold interp, unfold dlo_val,
    apply propext, apply iff.intro, 
    intro H, cases H with H H, 
    apply ne_of_lt H, apply ne_of_gt H, 
    intro H, apply lt_or_gt_of_ne H  
  end

def dlo_dep0 : adlo → Prop 
| (adlo.lt m n) := m = 0 ∨ n = 0
| (adlo.eq m n) := m = 0 ∨ n = 0

lemma adlo_dec_dep0 : decidable_pred dlo_dep0  
| (adlo.lt 0 n) := decidable.is_true (or.inl (eq.refl _))
| (adlo.lt m 0) := decidable.is_true (or.inr (eq.refl _))
| (adlo.lt (m+1) (n+1)) := 
 decidable.is_false 
  (begin 
    intro H, cases H with H H,
    cases H, cases H
   end)
| (adlo.eq 0 n) := decidable.is_true (or.inl (eq.refl _))
| (adlo.eq m 0) := decidable.is_true (or.inr (eq.refl _))
| (adlo.eq (m+1) (n+1)) := 
 decidable.is_false 
  (begin 
    intro H, cases H with H H,
    cases H, cases H
   end)

def dlo_decr : adlo → adlo
| (adlo.lt m n) := (adlo.lt (m-1) (n-1))
| (adlo.eq m n) := (adlo.eq (m-1) (n-1))

def pos_of_not_dep0_lt (m n) (H : ¬ dlo_dep0 (m <' n)) : (m > 0 ∧ n > 0) := 
begin
  cases m, apply absurd _ H, 
  apply or.inl, refl, 
  cases n, apply absurd _ H, 
  apply or.inr, refl, 
  apply and.intro, 
  apply nat.zero_lt_succ,
  apply nat.zero_lt_succ,
end

def pos_of_not_dep0_eq (m n) (H : ¬ dlo_dep0 (m =' n)) : (m > 0 ∧ n > 0) := 
begin
  cases m, apply absurd _ H, 
  apply or.inl, refl, 
  cases n, apply absurd _ H, 
  apply or.inr, refl, 
  apply and.intro, 
  apply nat.zero_lt_succ,
  apply nat.zero_lt_succ,
end

theorem dlo_atom [dlo β] : atom adlo β := 
{ val := dlo_val,
  aneg := adlo_aneg,
  aneg_nqfree := adlo_aneg_nqfree,
  aneg_prsv := adlo_aneg_prsv,
  dep0 := dlo_dep0,
  dec_dep0 := adlo_dec_dep0,
  decr := dlo_decr,
  decr_prsv := 
    begin
      intros a Ha b bs, 
      cases a with m n m n, 
      unfold dlo_decr, 
      repeat {unfold dlo_val}, 
      repeat {rewrite nth_dft_pred}, 
      apply (pos_of_not_dep0_lt m n Ha)^.elim_right,
      apply (pos_of_not_dep0_lt m n Ha)^.elim_left,
      unfold dlo_decr, 
      repeat {unfold dlo_val}, 
      repeat {rewrite nth_dft_pred}, 
      repeat {rewrite nth_dft_pred}, 
      apply (pos_of_not_dep0_eq m n Ha)^.elim_right,
      apply (pos_of_not_dep0_eq m n Ha)^.elim_left,
    end,
  inh := dlo.inh β,
  dec_eq := by tactic.mk_dec_eq_instance } 

def dlo_solv0 : adlo → Prop  
| (adlo.lt m n) := false
| (adlo.eq m n) := m = 0 ∨ n = 0 

lemma dlo_dec_solv0 : decidable_pred dlo_solv0 
| (adlo.lt m n) := is_false (λ H, by cases H)
| (adlo.eq m n) := 
  begin
    cases m with m m, apply is_true, apply or.inl, refl,
    cases n with n n, apply is_true, apply or.inr, refl,
    apply is_false, intro H, cases H with H H,
    cases H, cases H 
  end

def dlo_dest_solv0 : ∀ (a : adlo) (H : dlo_solv0 a), nat 
| (adlo.lt m n) H := by cases H
| (adlo.eq 0 n) _ := n
| (adlo.eq (m+1) 0) _ := m+1
| (adlo.eq (m+1) (n+1)) H := 
  begin exfalso, cases H with H H; cases H end

lemma exp_dlo_dest_solv0_0n (n : nat) (H : dlo_solv0 (0 ='n)) : 
  dlo_dest_solv0 (0 =' n) H = n := by refl 

lemma exp_dlo_dest_solv0_m0 (m : nat) (H : dlo_solv0 ((m+1) =' 0)) : 
  dlo_dest_solv0 ((m+1) =' 0) H = m+1 := by refl

lemma dlo_solv0_eq [dlo β] : ∀ {e : adlo} (He : dlo_solv0 e) {b} {bs}, dlo_val e (b::bs) 
  → list.nth_dft (dlo.inh β) (b::bs) (dlo_dest_solv0 e He) = b   
| (adlo.lt m n) He _ _ _ := by cases He
| (adlo.eq 0 n) He b bs HI := 
  begin
    cases n; unfold dlo_dest_solv0, refl, 
    unfold dlo_val at HI, apply eq.symm HI
  end
| (adlo.eq m 0) He b bs HI := 
  begin
    cases m with m; unfold dlo_dest_solv0, refl, 
    unfold dlo_val at HI, apply HI
  end
| (adlo.eq (m+1) (n+1)) He _ _ _ := 
  begin cases He with He He; cases He end

def dlo_triv : adlo → Prop  
| (adlo.lt m n) := false
| (adlo.eq m n) := m = n

lemma dlo_dec_triv : decidable_pred dlo_triv
| (adlo.lt m n) := begin apply is_false, apply id end
| (adlo.eq m n) := 
  begin
    cases (nat.decidable_eq m n) with HD HD, 
    apply is_false, intro HC, apply HD HC, 
    apply is_true, apply HD
  end

lemma dlo_true_triv [dlo β] : ∀ a, dlo_triv a → ∀ (bs : list β), dlo_val a bs 
| (adlo.lt m n) HT := by cases HT 
| (adlo.eq m n) HT := 
  begin 
    intro bs, unfold dlo_triv at HT, 
    rewrite HT, unfold dlo_val 
  end

def dlo_subst0 : adlo → adlo → adlo
| (i =' j) (m <' n) := subst_idx i j m <' subst_idx i j n
| (i =' j) (m =' n) := subst_idx i j m =' subst_idx i j n
| _        a        := a

lemma dlo_true_subst [dlo β] : ∀ e, dlo_solv0 e 
  → ∀ (bs : list β), dlo_val (dlo_subst0 e e) bs  
| (adlo.lt m n) HT := by cases HT 
| (adlo.eq m n) HT := 
  begin 
    intro bs, cases HT with HT HT, 
    subst HT, unfold dlo_subst0, 
    cases n with n, 
    repeat {unfold subst_idx},
    unfold dlo_val, 
    repeat {unfold subst_idx},
    unfold dlo_val, refl,
    rewrite HT, unfold dlo_subst0, 
    cases m with m, unfold dlo_val, 
    repeat {unfold subst_idx}, 
    unfold dlo_val, refl
  end

lemma dlo_subst_prsv_aux_0n [dlo β] (n x) (bs) (H) : list.nth_dft (inh β) bs (subst_idx 0 n x) 
  = list.nth_dft (inh β) (list.nth_dft (inh β) bs (dlo_dest_solv0 (0 =' n) H - 1) :: bs) x := 
begin
  cases x with x, unfold subst_idx,
  rewrite exp_dlo_dest_solv0_0n, 
  rewrite nth_dft_head, refl
end

lemma dlo_subst_prsv_aux_m0 [dlo β] (m x) (bs) (H) : list.nth_dft (inh β) bs (subst_idx m 0 x) 
  = list.nth_dft (inh β) (list.nth_dft (inh β) bs (dlo_dest_solv0 (m =' 0) H - 1) :: bs) x := 
begin
  cases m with m, apply dlo_subst_prsv_aux_0n,
  cases x with x, unfold subst_idx,
  rewrite exp_dlo_dest_solv0_m0, 
  rewrite nth_dft_head, refl, refl
end

lemma dlo_subst_prsv [dlo β] : ∀ {e : adlo} (He : dlo_solv0 e) {a : adlo} {bs : list β}, 
  dlo_val (dlo_subst0 e a) bs ↔ dlo_val a ((list.nth_dft (dlo.inh β) bs (dlo_dest_solv0 e He - 1))::bs) 
| (adlo.lt m n) H _ := by cases H
| (adlo.eq 0 n) _ (x <' y) := 
  begin
    intro bs, unfold dlo_subst0,
    repeat {unfold dlo_val},  
    repeat {rewrite dlo_subst_prsv_aux_0n}
  end
| (adlo.eq 0 n) _ (x =' y) :=
  begin
    intro bs, unfold dlo_subst0,
    repeat {unfold dlo_val},  
    repeat {rewrite dlo_subst_prsv_aux_0n}
  end
| (adlo.eq m 0) _ (x <' y) := 
  begin
    intro bs, unfold dlo_subst0,
    repeat {unfold dlo_val},  
    repeat {rewrite dlo_subst_prsv_aux_m0}
  end
| (adlo.eq m 0) _ (x =' y) := 
  begin
    intro bs, unfold dlo_subst0,
    repeat {unfold dlo_val},  
    repeat {rewrite dlo_subst_prsv_aux_m0}
  end
| (adlo.eq (m+1) (n+1)) H _ := by cases H with H H ; cases H

lemma dlo_dest_pos : ∀ {a} {Ha : dlo_solv0 a}, ¬ dlo_triv a → dlo_dest_solv0 a Ha > 0 :=
begin
  intros a Ha HT, cases a with m n m n, 
  cases Ha, cases m ; cases n, 
  exfalso, apply HT, unfold dlo_triv, 
  unfold dlo_dest_solv0, apply nat.zero_lt_succ,
  unfold dlo_dest_solv0, apply nat.zero_lt_succ,
  unfold dlo_solv0 at Ha, cases Ha with Ha Ha ; 
  cases Ha
end

lemma dlo_atomeq [H : dlo β] : atomeq adlo β := 
{ val := dlo_val,
  aneg := adlo_aneg,
  aneg_nqfree := adlo_aneg_nqfree,
  aneg_prsv := adlo_aneg_prsv,
  dep0 := dlo_dep0,
  dec_dep0 := adlo_dec_dep0,
  decr := dlo_decr,
  decr_prsv := 
    begin
      intros a Ha b bs, 
      cases a with m n m n, 
      unfold dlo_decr, 
      repeat {unfold dlo_val}, 
      repeat {rewrite nth_dft_pred}, 
      apply (pos_of_not_dep0_lt m n Ha)^.elim_right,
      apply (pos_of_not_dep0_lt m n Ha)^.elim_left,
      unfold dlo_decr, 
      repeat {unfold dlo_val}, 
      repeat {rewrite nth_dft_pred}, 
      repeat {rewrite nth_dft_pred}, 
      apply (pos_of_not_dep0_eq m n Ha)^.elim_right,
      apply (pos_of_not_dep0_eq m n Ha)^.elim_left,
    end,
  inh := dlo.inh β,
  dec_eq := by tactic.mk_dec_eq_instance, 
  solv0 := dlo_solv0,
  dec_solv0 := dlo_dec_solv0,
  dest_solv0 := dlo_dest_solv0,
  solv0_eq := @dlo_solv0_eq β _, 
  trivial := dlo_triv,
  dec_triv := dlo_dec_triv,  
  true_triv := dlo_true_triv,
  subst0 := dlo_subst0,
  true_subst := dlo_true_subst,
  subst_prsv := @dlo_subst_prsv β _,
  dest_pos := @dlo_dest_pos }

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

def qe_dlo_aux : ∀ (l : list adlo) (H : allp lt_single_0 l), (list nat × list nat)
| [] := λ _, ([],[]) 
| (a::as) :=
  match a with 
  | (adlo.eq m n) := begin intro H, exfalso, apply H _ (or.inl (eq.refl _)) end
  | (adlo.lt 0 0) := begin intro H, exfalso, apply H _ (or.inl (eq.refl _)) end
  | (adlo.lt (i+1) 0) := 
    λ H, let (lbs,rbs) := qe_dlo_aux as 
      (begin intros a' Ha', apply H a' (or.inr Ha') end) in 
      (i::lbs,rbs)
  | (adlo.lt 0 (j+1)) := 
    λ H, let (lbs,rbs) := qe_dlo_aux as 
      (begin intros a' Ha', apply H a' (or.inr Ha') end) in 
      (lbs,j::rbs)
  | (adlo.lt (i+1) (j+1)) := begin intro H, exfalso, apply H _ (or.inl (eq.refl _)) end
  end

#exit
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