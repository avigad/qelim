import ...mathlib.logic.basic

lemma or_iff_or (p p' q q' : Prop) :
  (p ↔ p') → (q ↔ q') → ((p ∨ q) ↔ (p' ∨ q')) := 
begin
  intros hp hq, rewrite hp, rewrite hq
end

lemma and_iff_and (p p' q q' : Prop) :
  (p ↔ p') → (q ↔ q') → ((p ∧ q) ↔ (p' ∧ q')) := 
begin
  intros hp hq, rewrite hp, rewrite hq
end

lemma forall_iff_not_exists_not {α : Type} {p : α → Prop} :
   (∀ x, p x) ↔ (¬ ∃ x, ¬ p x) :=
by rewrite (@not_exists_not _ p (λ x, classical.dec _))