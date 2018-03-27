import .nnf .predicates

variables {α β : Type}

def lift_nnf_qe (β) [Hα : atom_type α β] (qe : fm α → fm α) : fm α → fm α 
| (p ∧' q) := and_o (lift_nnf_qe p) (lift_nnf_qe q)
| (p ∨' q) := or_o  (lift_nnf_qe p) (lift_nnf_qe q)
| (¬' p) := not_o (lift_nnf_qe p)
| (∃' p) := qe (@nnf α β Hα (lift_nnf_qe p))
| p := p

lemma and_o_prsv_qfree (p q : fm α) : 
  qfree p → qfree q → qfree (and_o p q) := 
λ Hp Hq, 
  begin 
    cases p; cases q; 
    {trivial <|> apply Hp <|> apply Hq <|> {apply (and.intro Hp Hq)}}
  end

lemma or_o_prsv_qfree (p q : fm α) : 
  qfree p → qfree q → qfree (or_o p q) := 
λ Hp Hq, 
  begin 
    cases p; cases q; 
    {trivial <|> apply Hp <|> apply Hq <|> {apply (and.intro Hp Hq)}}
  end

lemma not_o_prsv_qfree (p : fm α) (H : qfree p) : qfree (not_o p) := 
begin cases p; {trivial <|> apply H} end

lemma lnq_qfree [Hα : atom_type α β] (qe : fm α → fm α) 
(H : ∀ (f : fm α), nqfree f → qfree (qe f)) : 
  ∀ (f : fm α), qfree (@lift_nnf_qe α β Hα qe f) :=
λ f, fm.rec_on f trivial trivial 
  (λ a, trivial)
  (λ f1 f2 H1 H2, and_o_prsv_qfree _ _ H1 H2)
  (λ f1 f2 H1 H2, or_o_prsv_qfree _ _ H1 H2)
  (λ f1 H1, not_o_prsv_qfree _ H1)
  (λ f1 H1, begin apply H, apply nnf_nqfree, apply H1 end)

open tactic

lemma lnq_prsv_gen 
  [Hα : atom_type α β] (qe : fm α → fm α) 
  (hqe : qfree_prsv qe) 
  (r : fm α → Prop) 
  (hdc : down_closed r)
  (hqc : preserves qe r)
  (hnc : preserves (nnf β) r)
  (hlc : ∀ f, preserves f r → preserves (lift_nnf_qe β f) r)
  (hi : ∀ (p : fm α), nqfree p → r p → ∀ (xs : list β), I (qe p) xs ↔ ∃ x, I p (x::xs)) : 
  ∀ (p : fm α), r p → ∀ (xs : list β), I (lift_nnf_qe β qe p) xs ↔ I p xs 
| ⊤' _ bs := iff.refl _
| ⊥' _ bs := iff.refl _
| (A' a) _ bs := iff.refl _
| (p ∧' q) hr xs := 
  begin 
    unfold lift_nnf_qe, rewrite exp_I_and, 
    rewrite exp_I_and_o, 
    repeat {rewrite lnq_prsv_gen}, 
    apply hdc _ _ (down.andr _ _) hr, 
    apply hdc _ _ (down.andl _ _) hr 
  end 
| (p ∨' q) hr xs := 
  begin 
    unfold lift_nnf_qe, rewrite exp_I_or, 
    rewrite exp_I_or_o, repeat {rewrite lnq_prsv_gen},
    apply hdc _ _ (down.orr _ _) hr, 
    apply hdc _ _ (down.orl _ _) hr 
  end 
| (¬' p) hr xs := 
  begin 
    unfold lift_nnf_qe, rewrite exp_I_not,  
    rewrite exp_I_not_o, repeat {rewrite lnq_prsv_gen},
    apply hdc _ _ (down.not _) hr 
  end
| (∃' p) hr xs := 
  begin 
    unfold lift_nnf_qe, rewrite exp_I_ex,
    rewrite hi, apply ex_iff_ex, intro b, 
    rewrite nnf_prsv, apply lnq_prsv_gen, 
    apply hdc _ _ (down.ex _) hr, 
    apply lnq_qfree, apply hqe, 
    apply nnf_nqfree, apply lnq_qfree,
    apply hqe, apply hnc, apply hlc, apply hqc, 
    apply hdc _ _ (down.ex _) hr 
  end

lemma lnq_prsv [Hα : atom_type α β] (qe : fm α → fm α) 
  (hqe : qfree_prsv qe) 
  (hi : ∀ (p : fm α), nqfree p → ∀ (xs : list β), I (qe p) xs ↔ ∃ x, I p (x::xs)) : 
  ∀ (p : fm α) (xs : list β), I (lift_nnf_qe β qe p) xs ↔ I p xs :=
begin
  intro p, apply (lnq_prsv_gen _ _ (λ _, true)),
  intros _ _ _ _, trivial, 
  intros _ _,  trivial, 
  intros _ _,  trivial, 
  intros _ _ _ _, trivial, 
  intros q hf h', apply hi, 
  apply hf, trivial, apply hqe
end
