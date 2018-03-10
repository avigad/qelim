import .logic

variable {α : Type}

def size : fm α → nat  
| (fm.true α) := 1
| (fm.false α) := 1
| (fm.atom a) := 1 
| (fm.and p q) := size p + size q + 1
| (fm.or p q) := size p + size q + 1
| (fm.not p) := size p + 1
| (fm.ex p) := size p + 1 

notation p `≃` q := size p = size q 
notation p `≺` q := size p < size q 

#check nat.less_than_or_equal

lemma eq_zero_of_lt_one (n) : n < 1 → n = 0 := sorry 
lemma size_pos (p : fm α) : size p > 0 := sorry
lemma not_pred_top (p : fm α) : ¬ (p ≺ (fm.true α)) := sorry
lemma not_pred_bot (p : fm α) : ¬ (p ≺ (fm.false α)) := sorry
lemma not_pred_atom (p : fm α) (a : α) : ¬ (p ≺ (fm.atom a)) := sorry
lemma pred_not (p q : fm α) : (p ≺ ¬' q) → (p ≃ q) ∨ (p ≺ q) := sorry 
lemma pred_ex (p q : fm α) : (p ≺ ∃' q) → (p ≃ q) ∨ (p ≺ q) := sorry 

lemma crec_on_aux {C : fm α → Prop} (H : ∀ p, (∀ (q : fm α), (q ≺ p) → C q) → C p) : 
∀ (p q : fm α), (q ≺ p) → C q := 
λ p, fm.rec_on p 
  (λ q Hq, false.rec _ (not_pred_top q Hq)) 
  (λ q Hq, false.rec _ (not_pred_bot q Hq)) 
  (λ a q Hq, false.rec _ (not_pred_atom q a Hq)) 
  (λ q r Hq Hr s Hs, _) 
  _ 
  (λ q Hq r Hr, 
    begin
      cases (pred_not r q Hr) with H1 H2, apply H, 
      intros s Hs, apply Hq, rewrite (eq.symm H1), 
      apply Hs, apply (Hq _ H2)
    end) 
  (λ q Hq r Hr, 
    begin
      cases (pred_ex r q Hr) with H1 H2, apply H, 
      intros s Hs, apply Hq, rewrite (eq.symm H1), 
      apply Hs, apply (Hq _ H2)
    end) 

lemma crec_on {C : fm α → Prop} : 
  (∀ p, (∀ (q : fm α), (q ≺ p) → C q) → C p) → ∀ (p : fm α), C p := 
by {intros H p, apply H, apply crec_on_aux, apply H}