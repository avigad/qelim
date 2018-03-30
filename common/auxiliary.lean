variables {α β γ : Type}



lemma add_le_iff_le_sub (a b c : int) : a + b ≤ c ↔ a ≤ c - b := 
iff.intro (le_sub_right_of_add_le) (add_le_of_le_sub_right)

lemma add_left [has_add α] {a b c : α} (h : b = c) : a + b = a + c := 
h ▸ eq.refl _

lemma le_iff_add_le_add_right [ordered_cancel_comm_monoid α] (a b c : α) : 
(a ≤ b) ↔ (a + c ≤ b + c) := 
begin 
  apply iff.intro;  
  intros h, apply add_le_add_right h,
  apply le_of_add_le_add_right h
end

lemma ite_true {p : Prop} [hd : decidable p] (h : p) (x y : α) : ite p x y = x := 
begin
  unfold ite, 
  tactic.unfreeze_local_instances, 
  cases hd with hd hd, simp, 
  exfalso, apply hd h, simp
end

lemma ite_false {p : Prop} [hd : decidable p] (h : ¬ p) (x y : α) : ite p x y = y := 
begin
  unfold ite, 
  tactic.unfreeze_local_instances, 
  cases hd with hd hd, simp, 
  exfalso, apply h hd
end

lemma exp_forall_eq {P : α → Prop} {a' : α} : 
  (∀ a, a = a' → P a) ↔ P a' := 
begin
  apply iff.intro; intro h, 
  apply h _ rfl, intros a' ha',
  subst ha', apply h 
end

def converse_linear_order (hlo : linear_order β) : linear_order β := 
{ le := λ x y, x ≥ y,
  le_refl := preorder.le_refl, 
  le_trans := λ x y z hxy hyz, preorder.le_trans z y x hyz hxy,
  le_antisymm := λ x y hxy hyx, partial_order.le_antisymm _ _ hyx hxy,
  le_total := λ x y, linear_order.le_total _ _ }


lemma dest_option : ∀ (o : option α), o = none ∨ ∃ a, o = some a  
| none := or.inl rfl 
| (some a) := begin apply or.inr, existsi a, refl end

lemma cases_ite {P} {Q : α → Prop} {HD : decidable P} {f g : α} 
  (Hf : P → Q f) (Hg : ¬ P → Q g) : Q (@ite P HD α f g) := 
begin
  unfold ite, 
  tactic.unfreeze_local_instances, 
  cases HD with h h, simp, apply Hg h,
  simp, apply Hf h
end

lemma true_iff_true {p q} : p → q → (p ↔ q) := 
by {intros hp hq, apply iff.intro ; intro _, apply hq, apply hp}

lemma false_iff_false {p q} : ¬ p → ¬ q → (p ↔ q) := 
begin
  intros hnp hnq, apply iff.intro, 
  intro hp, apply absurd hp hnp,
  intro hq, apply absurd hq hnq
end

lemma eq_true_or_eq_false_of_dec (P) [HP : decidable P] : P = true ∨ P = false :=
begin
  tactic.unfreeze_local_instances, 
  cases HP, 
  apply or.inr, rewrite eq_false, simp *,
  apply or.inl, rewrite eq_true, simp *,
end

lemma map_compose (f : α → β) (g : β → γ) : ∀ (as : list α), list.map g (list.map f as) = list.map (λ x, g (f x)) as 
| [] :=eq.refl _
| (a::as) := by simp 

lemma exp_compose (f : α → β) (g : β → γ) (a : α) : (λ x, g (f x)) a = g (f a) := eq.refl _ 

def dec_not_pred_of_dec_pred (P : α → Prop) [H : decidable_pred P] : decidable_pred (λ x, ¬ P x) := 
begin
  intro a, cases (H a) with H H, 
  apply decidable.is_true H, 
  apply decidable.is_false (not_not_intro H)
end

lemma iff_not_not {p : Prop} : p ↔ ¬¬p := 
iff.intro (not_not_intro) (classical.by_contradiction)

lemma iff_not_and {p q : Prop} : ¬ p ∨ ¬ q ↔ ¬(p ∧ q) := 
iff.intro 
 (λ H1 H2, or.elim H1 (λ H3, H3 H2^.elim_left) (λ H3, H3 H2^.elim_right)) 
 (λ H, @classical.by_cases p _ 
   (λ Hp, @classical.by_cases q _ 
     (λ Hq, @false.rec _ (H $ and.intro Hp Hq)) 
     (λ Hq, or.inr Hq))
   (λ Hp, or.inl Hp))

lemma iff_not_or {p q : Prop} : ¬ p ∧ ¬ q ↔ ¬(p ∨ q) :=  
iff.intro 
  (λ H, not_or H^.elim_left H^.elim_right)
  (λ H, and.intro (λ Hp, H $ or.inl Hp) (λ Hq, H $ or.inr Hq)) 

lemma ex_iff_ex (P Q : α → Prop) (H : ∀ a, P a ↔ Q a) : (∃ x, P x) ↔ (∃ x, Q x) :=
begin
  apply iff.intro, intro HP, cases HP with a Ha,
  existsi a, apply (H a)^.elim_left Ha, 
  intro HQ, cases HQ with a Ha,
  existsi a, apply (H a)^.elim_right Ha 
end

lemma ex_eq_ex (P Q : α → Prop) (H : ∀ a, P a = Q a) : (∃ x, P x) = (∃ x, Q x) :=
begin
  apply propext, apply iff.intro, 
  intro HP, cases HP with a Ha,
  existsi a, rewrite H at Ha, apply Ha,
  intro HQ, cases HQ with a Ha,
  existsi a, rewrite H, apply Ha
end

lemma ex_to_ex (P Q : α → Prop) (H : ∀ a, P a → Q a) : (∃ x, P x) → (∃ x, Q x) := 
begin
  intro HP, cases HP with x Hx, 
  existsi x, apply (H x Hx)
end

def lcms : list nat → nat 
| [] := 1
| (n::ns) := nat.lcm n (lcms ns)

def zlcms (zs : list int) : int :=
lcms (list.map int.nat_abs zs)

open tactic

meta def split_em (p : Prop) : tactic unit := 
`[cases (classical.em p)]


meta def papply (pe : pexpr) := to_expr pe >>= apply  

meta def intro_fresh : tactic expr :=
get_unused_name `h none >>= tactic.intro 

meta def intro_refl : tactic unit := 
do t ← target, 
   match t with 
   | `(_ = _) := papply ``(eq.refl _) >> skip
   | `(_ → _) := intro_fresh >> intro_refl
   | _ := failed 
   end

meta def papply_trans (pe : pexpr) := 
do papply ``(eq.trans), papply pe
