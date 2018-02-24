import .logic

class atom (α β : Type) :=
(val : α → list β → Prop)
(aneg : α → fm α) 
(aneg_nqfree : ∀ (a : α), nqfree (aneg a))
(aneg_prsv : ∀ (a : α) (xs : list β), (interp val xs (aneg a)) = (interp val xs (¬' A' a)))
(dep0 : α → Prop)
(dec_dep0 : decidable_pred dep0)
(decr : α → α)
(decr_prsv : ∀ (a : α), ¬ (dep0 a) → ∀ (b : β) (bs : list β), (val (decr a) bs = val a (b::bs)))
(inh : β)
(dec_eq : decidable_eq α)

class atomeq (α β : Type) extends atom α β :=
(solv0 : α → Prop)
(dec_solv0 : decidable_pred solv0)
(dest_solv0 : ∀ a, solv0 a → nat)
(solv0_eq : ∀ {e : α} (He : solv0 e) {b} {bs}, val e (b::bs) 
  → list.nth_dft (atom.inh α β) (b::bs) (dest_solv0 e He) = b)
(trivial : α → Prop)
(dec_triv : decidable_pred trivial)
(true_triv : ∀ a, trivial a → ∀ xs, val a xs)
(subst0 : α → α → α)
(true_subst : ∀ e, solv0 e → ∀ bs, val (subst0 e e) bs)
(subst_prsv : ∀ {e : α} (He : solv0 e), ∀ {a : α} {bs : list β}, 
  val (subst0 e a) bs ↔ val a ((list.nth_dft (atom.inh α β) bs (dest_solv0 e He - 1))::bs))
(dest_pos : ∀ {a} {Ha : solv0 a}, ¬ trivial a → dest_solv0 a Ha > 0)

-- Requires : j = 0 ↔ ¬(i = 0)
def subst_idx : nat → nat → nat → nat 
| 0 j 0 := j - 1
| (i+1) _ 0 := i  
| _ _ k := k - 1 

-- Qstn : Why do I need this? (Why doesn't unfold work?)
lemma exp_subst_idx_i0 (i) : subst_idx (i+1) 0 0 = i := 
begin refl end

variables {α β : Type}

def I [atom α β] (p : fm α) (xs : list β) := interp (atom.val) xs p 

lemma exp_I_and [atom α β] (p q : fm α) (xs : list β) : 
  I (p ∧' q) xs = ((I p xs) ∧ (I q xs)) := eq.refl _

lemma exp_I_and_o [atom α β] (p q : fm α) (xs : list β) : 
  I (and_o p q) xs = ((I p xs) ∧ (I q xs)) := 
begin
  apply (cases_and_o' (λ p q pq, ((I pq xs) = ((I p xs) ∧ (I q xs)))) p q), 
  repeat {unfold I, unfold interp, simp},
  unfold I, unfold interp 
end

lemma exp_I_or [atom α β] (p q : fm α) (xs : list β) : 
  I (p ∨' q) xs = ((I p xs) ∨ (I q xs)) := eq.refl _

lemma exp_I_or_o [atom α β] (p q : fm α) (xs : list β) : 
  I (or_o p q) xs = ((I p xs) ∨ (I q xs)) := 
begin
  apply (cases_or_o' (λ p q pq, ((I pq xs) = ((I p xs) ∨ (I q xs)))) p q), 
  repeat {unfold I, unfold interp, simp},
  unfold I, unfold interp 
end

lemma exp_I_not [atom α β] (p : fm α) (xs : list β) : 
  I (¬' p) xs = ¬ (I p xs) := eq.refl _

lemma exp_I_ex [atom α β] (p : fm α) (xs) : @I α β _ (∃' p) xs = ∃ x, (I p (x::xs)) := 
by unfold I; unfold interp

lemma exp_I_top [atom α β] (xs) : @I α β _ ⊤' xs = true := 
by unfold I; unfold interp

lemma exp_I_bot [atom α β] (xs) : @I α β _ ⊥' xs = false := 
by unfold I; unfold interp

