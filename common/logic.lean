import .list

inductive fm (α : Type) : Type 
| true  : fm
| false : fm
| atom : α → fm 
| and : fm → fm → fm  
| or  : fm → fm → fm  
| not : fm → fm 
| ex  : fm → fm 

notation `⊤'`     := fm.true _
notation `⊥'`     := fm.false _
notation `A'` a   := fm.atom a
notation `¬'` p   := fm.not p
notation p `∧'` q := fm.and p q 
notation p `∨'` q := fm.or p q 
notation `∃'` p   := fm.ex p

-- | (fm.true α) := 
-- | (fm.false α) := 
-- | (fm.atom a) :=  
-- | (fm.and p q) :=
-- | (fm.or p q) :=
-- | (fm.not p) :=
-- | (fm.ex p) :=

-- | ⊤' := sorry
-- | ⊥' := sorry
-- | (A' a) := sorry
-- | (p ∧' q) := sorry
-- | (p ∨' q) := sorry
-- | (¬' p) := sorry
-- | (∃' p) := sorry

variables {α β : Type}

meta def fm_to_format [has_to_format α] : fm α → format 
| (fm.true α) := "⊤"
| (fm.false α) := "⊥"
| (fm.atom a) := to_fmt a
| (fm.and p q) := "(" ++ (fm_to_format p) ++ " ∧ " ++ (fm_to_format q) ++ ")"
| (fm.or p q) := "(" ++ (fm_to_format p) ++ " ∨ " ++ (fm_to_format q) ++ ")"
| (fm.not p) := "¬(" ++ (fm_to_format p) ++ ")" 
| (fm.ex p)  := "∃(" ++ (fm_to_format p) ++ ")"

meta instance [has_to_format α] : has_to_format (fm α) := ⟨fm_to_format⟩

meta instance [has_to_format α] : has_to_tactic_format (fm α) := 
has_to_format_to_has_to_tactic_format _

def top_or_not (p : fm α) : p = ⊤' ∨ p ≠ ⊤' :=
by cases p; {{apply or.inl, refl} <|> {apply or.inr, intro HC, cases HC}}

def bot_or_not (p : fm α) : p = ⊥' ∨ p ≠ ⊥' :=
by cases p; {{apply or.inl, refl} <|> {apply or.inr, intro HC, cases HC}}

def and_o : fm α → fm α → fm α  
| (fm.true α) q' := q'
| p' (fm.true α) := p'
| (fm.false α) q' := fm.false α  
| p' (fm.false α) := fm.false α 
| p' q' := fm.and p' q'

-- Q : Why can't I prove this with refl?
lemma exp_top_and_o (p : fm α) : (@and_o α ⊤' p) = p := 
by induction p; {intro_refl} 

lemma exp_and_o_top (p : fm α) : (@and_o α p ⊤') = p := 
by induction p; {intro_refl} 

lemma exp_bot_and_o (p : fm α) : (@and_o α ⊥' p) = ⊥' := 
by induction p; {intro_refl} 

lemma exp_and_o_bot (p : fm α) : (@and_o α p ⊥') = ⊥' := 
by induction p; {intro_refl} 

lemma exp_and_o_nc (p q : fm α) : 
(p ≠ ⊤') → (p ≠ ⊥') → (q ≠ ⊤') → (q ≠ ⊥') → (@and_o α p q) = (p ∧' q) :=
by intros H1 H2 H3 H4; cases p; cases q; {refl <|> contradiction}  

lemma cases_and_o (P : fm α → Prop) (p q : fm α)  
  (HB : P ⊥') (Hp : P p) (Hq : P q) (Hpq : P (p ∧' q)) : P (and_o p q) :=  
begin
  cases (top_or_not p) with H1 H1, rewrite H1, 
  rewrite exp_top_and_o, apply Hq, 
  cases (bot_or_not p) with H2 H2, rewrite H2, 
  rewrite exp_bot_and_o, apply HB, 
  cases (top_or_not q) with H3 H3, rewrite H3, 
  rewrite exp_and_o_top, apply Hp, 
  cases (bot_or_not q) with H4 H4, rewrite H4, 
  rewrite exp_and_o_bot, apply HB, 
  rewrite exp_and_o_nc _ _ H1 H2 H3 H4, 
  apply Hpq 
end

lemma cases_and_o' (P : fm α → fm α → fm α → Prop) (p q : fm α)  
  (HTq : P ⊤' q q) (HBq : P ⊥' q ⊥') 
  (HpT : P p ⊤' p) (HpB : P p ⊥' ⊥') 
  (Hpq : P p q (p ∧' q)) : P p q (and_o p q) :=  
begin
  cases (top_or_not p) with H1 H1, rewrite H1, 
  rewrite exp_top_and_o, apply HTq, 
  cases (bot_or_not p) with H2 H2, rewrite H2, 
  rewrite exp_bot_and_o, apply HBq, 
  cases (top_or_not q) with H3 H3, rewrite H3, 
  rewrite exp_and_o_top, apply HpT, 
  cases (bot_or_not q) with H4 H4, rewrite H4, 
  rewrite exp_and_o_bot, apply HpB, 
  rewrite exp_and_o_nc _ _ H1 H2 H3 H4, 
  apply Hpq 
end

def or_o : fm α → fm α → fm α  
| (fm.true α) _ := ⊤'
| _ (fm.true α) := ⊤'
| (fm.false α) q := q
| p (fm.false α) := p
| p q := fm.or p q 

lemma exp_top_or_o (p : fm α) : (@or_o α ⊤' p) = ⊤' := 
by induction p; {intro_refl} 

lemma exp_bot_or_o (p : fm α) : (@or_o α ⊥' p) = p := 
by induction p; {intro_refl} 

lemma exp_or_o_top (p : fm α) : (@or_o α p ⊤') = ⊤' := 
by induction p; {intro_refl} 

lemma exp_or_o_bot (p : fm α) : (@or_o α p ⊥') = p := 
by induction p; {intro_refl} 

lemma exp_or_o_nc (p q : fm α) : 
(p ≠ ⊤') → (p ≠ ⊥') → (q ≠ ⊤') → (q ≠ ⊥') → (@or_o α p q) = (p ∨' q) :=
by intros H1 H2 H3 H4; cases p; cases q; {refl <|> contradiction}  

lemma cases_or_o (P : fm α → Prop) (p q : fm α)  
  (HT : P ⊤') (Hp : P p) (Hq : P q) (Hpq : P (p ∨' q)) : P (or_o p q) :=  
begin
  cases (top_or_not p) with H1 H1, rewrite H1, 
  rewrite exp_top_or_o, apply HT, 
  cases (bot_or_not p) with H2 H2, rewrite H2, 
  rewrite exp_bot_or_o, apply Hq, 
  cases (top_or_not q) with H3 H3, rewrite H3, 
  rewrite exp_or_o_top, apply HT, 
  cases (bot_or_not q) with H4 H4, rewrite H4, 
  rewrite exp_or_o_bot, apply Hp, 
  rewrite exp_or_o_nc _ _ H1 H2 H3 H4, 
  apply Hpq 
end

lemma cases_or_o' (P : fm α → fm α → fm α → Prop) (p q : fm α)  
  (HTq : P ⊤' q ⊤') (HBq : P ⊥' q q) 
  (HpT : P p ⊤' ⊤') (HpB : P p ⊥' p) 
  (Hpq : P p q (p ∨' q)) : P p q (or_o p q) :=  
begin
  cases (top_or_not p) with H1 H1, rewrite H1, 
  rewrite exp_top_or_o, apply HTq, 
  cases (bot_or_not p) with H2 H2, rewrite H2, 
  rewrite exp_bot_or_o, apply HBq, 
  cases (top_or_not q) with H3 H3, rewrite H3, 
  rewrite exp_or_o_top, apply HpT, 
  cases (bot_or_not q) with H4 H4, rewrite H4, 
  rewrite exp_or_o_bot, apply HpB, 
  rewrite exp_or_o_nc _ _ H1 H2 H3 H4, 
  apply Hpq 
end

def not_o : fm α → fm α  
| ⊤' := ⊥' 
| ⊥' := ⊤'
| p := ¬' p

lemma cases_not_o_core (P : fm α → fm α → Prop) (p : fm α)  
  (ht : P p ⊤' ) (hb : P p ⊥') (hnp : P p (¬' p)) : P p (not_o p) :=  
begin cases p, apply hb, apply ht, repeat {apply hnp}, end

lemma cases_not_o (P : fm α → Prop) (p : fm α)  
  (ht : P ⊤' ) (hb : P ⊥') (hnp : P (¬' p)) : P (not_o p) :=  
cases_not_o_core (λ _ q, P q) p ht hb hnp

lemma exp_not_o_top : not_o ⊤' = (fm.false α) := eq.refl _

lemma exp_not_o_bot : not_o ⊥' = (fm.true α) := eq.refl _

lemma exp_not_o_nc (p : fm α) : 
(p ≠ ⊤') → (p ≠ ⊥') → (@not_o α p) = ¬' p :=
by intros H1 H2; cases p; {refl <|> contradiction}  

def nfree : fm α → bool
| ⊤' := tt
| ⊥' := tt
| A' a := tt
| (¬' p) := ff
| (p ∨' q) := nfree p && nfree q
| (p ∧' q) := nfree p && nfree q
| (∃' p) := nfree p

def qfree : fm α → Prop
| ⊤' := true
| ⊥' := true
| A' a := true
| (¬' p) := qfree p
| (p ∨' q) := qfree p ∧ qfree q
| (p ∧' q) := qfree p ∧ qfree q
| (∃' p) :=  false

def nqfree : fm α → Prop
| ⊤' := true
| ⊥' := true
| A' a := true
| (¬' p) := false
| (p ∨' q) := nqfree p ∧ nqfree q
| (p ∧' q) := nqfree p ∧ nqfree q
| (∃' p) := false

def list_conj : list (fm α) → fm α 
| [] := ⊤' 
| (p::ps) := and_o p $ list_conj ps 

lemma list_conj_qfree : ∀ (ps : list (fm α)), (∀ p ∈ ps, qfree p) → qfree (list_conj ps)  
| [] _ := trivial 
| (p::ps) h := 
  begin 
    unfold list_conj, apply cases_and_o, trivial, 
    apply h, simp, apply list_conj_qfree,
    intros q Hq, apply h, apply or.inr, apply Hq,
    unfold qfree, apply and.intro, 
    apply h, simp, apply list_conj_qfree,
    intros q Hq, apply h, apply or.inr, apply Hq
  end

def list_disj : list (fm α) → fm α 
| [] := ⊥' 
| (p::ps) := or_o p $ list_disj ps 

def disj (bs : list β) (f : β → fm α) := list_disj (list.map f bs) 

def dnf_to_fm (ls : list (list α)) (f : list α → fm α) := list_disj (list.map f ls)

lemma disj_qfree (f : list α → fm α) (H : ∀ l, qfree (f l)) : ∀ (ls : list (list α)), qfree (dnf_to_fm ls f)  
| [] := trivial 
| (l::ls) := 
  begin 
    unfold dnf_to_fm, unfold list.map, unfold list_disj,
    apply cases_or_o qfree _ _ trivial, 
    apply H, apply disj_qfree, 
    unfold qfree, apply and.intro, 
    apply H, apply disj_qfree 
  end

/-
Requires : qfree arg-0
-/
def map_fm (f : α → β) : fm α → fm β 
| ⊤' := ⊤' 
| ⊥' := ⊥' 
| A' a := A' (f a)
| (¬' p) := ¬' (map_fm p)
| (p ∨' q) := (map_fm p) ∨' (map_fm q)
| (p ∧' q) := (map_fm p) ∧' (map_fm q)
| (∃' p) := ⊥' 

/-
Requires : qfree arg-0
-/
def amap (f : α → fm β) : fm α → fm β 
| ⊤' := ⊤' 
| ⊥' := ⊥' 
| A' a := f a
| (¬' p) := not_o (amap p)
| (p ∨' q) := or_o (amap p) (amap q)
| (p ∧' q) := and_o (amap p) (amap q)
| (∃' p) := ⊥' 


def atoms [decidable_eq α] : fm α → list α 
| ⊤' := [] 
| ⊥' := [] 
| A' a := [a]
| (¬' p) := atoms p
| (p ∨' q) := (atoms p) ∪ (atoms q)
| (p ∧' q) := (atoms p) ∪ (atoms q)
| (∃' p) := atoms p

meta def map_fm_prsv_tac :=
`[unfold map_fm, unfold atoms, 
  rewrite list.forall_mem_union, unfold atoms at h,
  rewrite list.forall_mem_union at h, cases h with hp hq,
  apply and.intro; apply map_fm_prsv; assumption]

lemma map_fm_prsv [decidable_eq α] [decidable_eq β] (P : α → Prop) {Q : β → Prop} 
  {f : α → β} (hf : ∀ a, P a → Q (f a)) :
  ∀ {p} {hp : ∀ a ∈ (atoms p), P a}, ∀ a ∈ (atoms (map_fm f p)), Q a 
| ⊤' h := begin apply list.forall_mem_nil end
| ⊥' h := begin apply list.forall_mem_nil end
| (A' a) h := 
  begin 
    unfold map_fm, unfold atoms, intros b hb, 
    rewrite list.mem_singleton at hb, subst hb,
    apply hf, apply h, unfold atoms, apply or.inl rfl
  end
| (¬' p) h := 
  begin
    unfold map_fm, unfold atoms, unfold atoms at h,
    apply map_fm_prsv, apply h
  end
| (p ∧' q) h := by map_fm_prsv_tac
| (p ∨' q) h := by map_fm_prsv_tac
| (∃' p) h := 
  begin unfold map_fm, unfold atoms, apply list.forall_mem_nil end


def interp (h : list β → α → Prop) : list β → fm α → Prop 
| xs ⊤' := true
| xs ⊥' := false 
| xs (A' a) := h xs a  
| xs (¬' p) := ¬ (interp xs p)
| xs (p ∨' q) := (interp xs p) ∨ (interp xs q)
| xs (p ∧' q) := (interp xs p) ∧ (interp xs q)
| xs ∃' p := exists (x : β), interp (x::xs) p 

