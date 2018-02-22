import .nnf

variables {α β : Type}

def lift_nnf_qe [Hα : @atom α β] (qe : fm α → fm α) : fm α → fm α 
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

lemma lift_nnf_qe_qfree [Hα : atom α β] (qe : fm α → fm α) 
(H : ∀ (f : fm α), nqfree f → qfree (qe f)) : 
  ∀ (f : fm α), qfree (@lift_nnf_qe α β Hα qe f) :=
λ f, fm.rec_on f trivial trivial 
  (λ a, trivial)
  (λ f1 f2 H1 H2, and_o_prsv_qfree _ _ H1 H2)
  (λ f1 f2 H1 H2, or_o_prsv_qfree _ _ H1 H2)
  (λ f1 H1, not_o_prsv_qfree _ H1)
  (λ f1 H1, begin apply H, apply nnf_nqfree, apply H1 end)

open tactic

lemma lnq_prsv [Hα : atom α β] (qe : fm α → fm α) 
  (Hqe : ∀ (f : fm α), nqfree f → qfree (qe f)) 
  (HI : ∀ (p : fm α) (xs : list β), I (qe p) xs = ∃ x, I p (x::xs)) : 
  ∀ (p : fm α) (xs : list β), I (@lift_nnf_qe _ β _ qe p) xs = I p xs := 
λ p, fm.rec_on p 
  (λ xs, eq.refl _) 
  (λ xs, eq.refl _) 
  (λ a xs, eq.refl _)
  (begin 
    intros q r Hq Hr xs, unfold lift_nnf_qe, rewrite exp_I_and, 
    rewrite (eq.symm (Hq xs)), rewrite (eq.symm (Hr xs)), apply eq.symm,
    cases (top_or_not (lift_nnf_qe qe q)) with HqT HqNT, 
    rewrite HqT, rewrite exp_I_top, rewrite exp_top_and_o, 
    apply propext, apply true_and,
    cases (bot_or_not (lift_nnf_qe qe q)) with HqB HqNB, 
    rewrite HqB, rewrite exp_bot_and_o, rewrite exp_I_bot, 
    apply propext, apply false_and,
    cases (top_or_not (lift_nnf_qe qe r)) with HrT HrNT, 
    rewrite HrT, rewrite exp_I_top, rewrite exp_and_o_top, 
    apply propext, apply and_true, 
    cases (bot_or_not (lift_nnf_qe qe r)) with HrB HrNB, 
    rewrite HrB, rewrite exp_and_o_bot, rewrite exp_I_bot, 
    apply propext, apply and_false, 
    rewrite (exp_and_o_nc _ _ HqNT HqNB HrNT HrNB), refl
   end) 
  (begin
    intros q r Hq Hr xs, unfold lift_nnf_qe, rewrite exp_I_or, 
    rewrite (eq.symm (Hq xs)), rewrite (eq.symm (Hr xs)), apply eq.symm,
    cases (top_or_not (lift_nnf_qe qe q)) with HqT HqNT, 
    rewrite HqT, rewrite exp_top_or_o, rewrite exp_I_top, simp, 
    cases (bot_or_not (lift_nnf_qe qe q)) with HqB HqNB, 
    rewrite HqB, rewrite exp_bot_or_o, rewrite exp_I_bot, simp, 
    cases (top_or_not (lift_nnf_qe qe r)) with HrT HrNT, 
    rewrite HrT, rewrite exp_or_o_top, rewrite exp_I_top, simp, 
    cases (bot_or_not (lift_nnf_qe qe r)) with HrB HrNB, 
    rewrite HrB, rewrite exp_or_o_bot, rewrite exp_I_bot, simp, 
    rewrite (exp_or_o_nc _ _ HqNT HqNB HrNT HrNB), refl
   end) 
  (begin 
    intros q Hq xs, unfold lift_nnf_qe, rewrite exp_I_not,
    rewrite (eq.symm (Hq xs)),  
    cases (top_or_not (lift_nnf_qe qe q)) with HqT HqNT, 
    rewrite HqT, rewrite exp_not_o_top, 
    rewrite exp_I_top, rewrite exp_I_bot, simp,
    cases (bot_or_not (lift_nnf_qe qe q)) with HqB HqNB, 
    rewrite HqB, rewrite exp_not_o_bot, 
    rewrite exp_I_top, rewrite exp_I_bot, simp,
    rewrite (exp_not_o_nc _ HqNT HqNB), rewrite exp_I_not, 
   end) 
  (begin
    intros q Hq xs, unfold lift_nnf_qe, 
    apply eq.trans, apply (HI _ xs), 
    rewrite exp_I_ex, apply propext,
    apply iff.intro, intro HL, 
    cases HL with x HL', existsi x, 
    rewrite nnf_prsv at HL', 
    rewrite Hq at HL', apply HL', 
    apply lift_nnf_qe_qfree, apply Hqe,
    intro HR, cases HR with x HR', existsi x, 
    rewrite nnf_prsv, rewrite Hq, apply HR', 
    apply lift_nnf_qe_qfree, apply Hqe
   end)