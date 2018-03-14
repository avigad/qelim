import .atom 

variables {α β : Type}

/-
Requires : qfree arg0
Ensures : nqfree ret
-/
def nnf (β) [@atom_type α β] : fm α → fm α 
| (fm.true α) := ⊤'  
| (fm.false α) := ⊥' 
| (fm.atom a) := A' a
| (fm.not (fm.true α)) := ⊥' 
| (fm.not (fm.false α)) := ⊤' 
| (fm.not (fm.atom a)) := atom_type.neg β a
| (fm.not (fm.not p)) := nnf p
| (fm.not (fm.or p q)) := fm.and (nnf (¬' p)) (nnf (¬' q))
| (fm.not (fm.and p q)) := fm.or (nnf (¬' p)) (nnf (¬' q))
| (fm.not (fm.ex p)) := ⊥' -- Invalid input
| (fm.or p q) := fm.or (nnf p) (nnf q)
| (fm.and p q) := fm.and (nnf p) (nnf q)
| (fm.ex p) := ⊥' -- Invalid input

lemma nnf_exp_and [atom_type α β] (p q : fm α) :
@nnf α β _ (fm.and p q) = fm.and (@nnf α β _ p) (@nnf α β _ q) := 
by unfold nnf

lemma nnf_exp_or [atom_type α β] (p q : fm α) : 
@nnf α β _ (p ∨' q) = (@nnf α β _ p ∨' @nnf α β _ q) := by unfold nnf

lemma nnf_exp_not_and [H : atom_type α β] (p q : fm α) : 
@nnf α β _ (¬' (p ∧' q)) = (@nnf α β _ (¬' p) ∨' @nnf α β _ (¬' q)) := 
by unfold nnf

lemma nnf_exp_not_or [H : atom_type α β] (p q : fm α) : 
@nnf α β _ (¬' (p ∨' q)) = (@nnf α β _ (¬' p) ∧' @nnf α β _ (¬' q)) := 
by unfold nnf

lemma nqfree_not_eq_nqfree [atom_type α β] : ∀ (p : fm α) (Hp : qfree p), 
nqfree (@nnf α β _ (¬' p)) = nqfree (@nnf α β _  p) :=
λ p, fm.rec_on p 
  (λ _, eq.refl _) 
  (λ _, eq.refl _) 
  (λ _ a, propext (iff.intro (λ _, trivial) (λ H, atom_type.neg_nqfree _ _)))
  (λ q r Hq Hr Hqr,  
    begin
       unfold nnf, unfold nqfree, 
        rw [Hq Hqr^.elim_left, Hr Hqr^.elim_right]
    end)
  (λ q r Hq Hr Hqr,  
    begin
       unfold nnf, unfold nqfree, 
        rw [Hq Hqr^.elim_left, Hr Hqr^.elim_right]
    end)
  (λ q Hq Hp, begin rewrite (Hq Hp), unfold nnf end) 
  (λ _ _ Hp, 
    begin 
      unfold qfree at Hp,
      cases Hp 
    end)

lemma nnf_nqfree [atom_type α β] : 
  ∀ (p : fm α), qfree p → nqfree (@nnf α β _ p) := 
λ p, fm.rec_on p  
(λ _, trivial) 
(λ _, trivial) 
(λ _ _, trivial) 
(λ q r Hq Hr Hqr, 
  begin
    rewrite nnf_exp_and, cases Hqr, 
    apply (and.intro (Hq left) (Hr right))
  end)
(λ q r Hq Hr Hqr, 
  begin
    rewrite nnf_exp_or, cases Hqr, 
    apply (and.intro (Hq left) (Hr right))
  end)
(λ q, fm.rec_on q 
  (λ _ _, trivial) 
  (λ _ _, trivial) 
  (λ _ _ _, by apply atom_type.neg_nqfree) 
  (λ r s Hr Hs H1 H2, 
    begin
      rewrite nnf_exp_not_and,
      rewrite nnf_exp_and at H1, 
      apply (and.intro 
              (Hr (λ _, (H1 H2)^.left) H2^.left) 
              (Hs (λ _, (H1 H2)^.right) H2^.right)),
    end) 
  (λ r s Hr Hs H1 H2, 
    begin
      rewrite nnf_exp_not_or,
      rewrite nnf_exp_or at H1, 
      apply (and.intro 
              (Hr (λ _, (H1 H2)^.left) H2^.left) 
              (Hs (λ _, (H1 H2)^.right) H2^.right)),
    end) 
  (λ r Hr1 Hr2 Hr3, 
    begin
      unfold nnf, 
      rewrite nqfree_not_eq_nqfree at Hr2,
      apply (Hr2 Hr3), apply Hr3
    end
    ) 
  (λ _ _ _ Hr, by cases Hr)) 
(λ _ _ Hr, by cases Hr)

meta def nnf_prsv_lit : tactic unit := 
`[apply and.intro, refl, unfold nnf, 
  unfold I, unfold interp, simp]

meta def nnf_prsv_normal_core_tac := 
  `[unfold nnf, unfold fnormal, 
    unfold fnormal at hnm, cases hnm with hnmp hnmq, 
    cases (@nnf_prsv_normal_core p hnmp) with ihp1 ihp2,  
    cases (@nnf_prsv_normal_core q hnmq) with ihq1 ihq2,
    apply and.intro;  apply and.intro; assumption]

lemma nnf_prsv_normal_core [atom_type α β] : 
  ∀ {p : fm α}, fnormal β p → fnormal β (nnf β p) ∧ fnormal β (nnf β ¬' p)
| (fm.true α) hnm := and.intro trivial trivial 
| (fm.false α) hnm := and.intro trivial trivial 
| (fm.atom a) hnm := 
  begin
    apply and.intro hnm, 
    unfold nnf, rewrite fnormal_iff_fnormal_alt,
    apply atom_type.neg_prsv_normal, apply hnm
  end
| (fm.not p) hnm := 
  begin
    cases (@nnf_prsv_normal_core p _) with ih1 ih2,  
    unfold nnf,apply and.intro; assumption, apply hnm
  end
| (fm.or p q) hnm := by nnf_prsv_normal_core_tac
| (fm.and p q) hnm := by nnf_prsv_normal_core_tac
| (fm.ex p) hnm := 
  begin unfold nnf, apply and.intro; trivial end

lemma nnf_prsv_normal [atom_type α β] {p : fm α} (h : fnormal β p) : fnormal β (nnf β p) :=
(nnf_prsv_normal_core h)^.elim_left

lemma nnf_prsv_core [atom_type α β] : ∀ (p : fm α), qfree p → 
  (∀ (xs : list β), (I (@nnf α β _ p) xs ↔ I p xs) ∧ (I (@nnf α β _ ¬' p) xs ↔ I (¬' p) xs))   
| (fm.true α)  Hp xs := by nnf_prsv_lit
| (fm.false α) Hp xs := by nnf_prsv_lit
| (fm.atom a)  Hp xs := 
  by {apply and.intro, refl, 
      unfold nnf, apply atom_type.neg_prsv} 
| (fm.and p q) Hp xs := 
  and.intro
    (begin
      unfold nnf, rewrite exp_I_and,   
      rewrite (nnf_prsv_core p _ xs)^.elim_left,
      rewrite (nnf_prsv_core q _ xs)^.elim_left, refl, 
      apply Hp^.elim_right, apply Hp^.elim_left
     end)
    (begin
      unfold nnf, rewrite exp_I_or, 
      rewrite (nnf_prsv_core p _ xs)^.elim_right,
      rewrite (nnf_prsv_core q _ xs)^.elim_right,
      repeat {rewrite exp_I_not}, rewrite exp_I_and, 
      apply iff_not_and, 
      apply Hp^.elim_right, apply Hp^.elim_left
     end)
| (fm.or p q)  Hp xs := 
  and.intro
    (begin
      unfold nnf, rewrite exp_I_or,  
      rewrite (nnf_prsv_core p _ xs)^.elim_left,
      rewrite (nnf_prsv_core q _ xs)^.elim_left, refl, 
      apply Hp^.elim_right, apply Hp^.elim_left
     end)
    (begin
      unfold nnf, rewrite exp_I_and, 
      rewrite (nnf_prsv_core p _ xs)^.elim_right,
      rewrite (nnf_prsv_core q _ xs)^.elim_right,
      repeat {rewrite exp_I_not}, rewrite exp_I_or, 
      apply iff_not_or, 
      apply Hp^.elim_right, apply Hp^.elim_left
     end)
| (fm.not p) Hp xs := 
  and.intro 
    (nnf_prsv_core p Hp xs)^.elim_right 
    (begin 
      unfold nnf, repeat {rewrite exp_I_not}, 
      rewrite (nnf_prsv_core p Hp xs)^.elim_left, 
      apply iff_not_not
     end)
| (fm.ex p) Hp xs := by cases Hp

lemma nnf_prsv [atom_type α β] (p : fm α) (Hp : qfree p) (xs : list β) : 
I (@nnf α β _ p) xs ↔ I p xs := (nnf_prsv_core p Hp xs)^.elim_left

