import .logic

class atom_type (α β : Type) :=
(val : list β → α → Prop)
(neg : α → fm α) 
(neg_nqfree : ∀ (a : α), nqfree (neg a))
(neg_prsv : ∀ (a : α) (xs : list β), (interp val xs (neg a)) ↔ (interp val xs (¬' A' a)))
(dep0 : α → Prop)
(dec_dep0 : decidable_pred dep0)
(decr : α → α)
(decr_prsv : ∀ {a : α} {hd : ¬ (dep0 a)} {b : β} {bs : list β}, (val bs (decr a) ↔ val (b::bs) a))
(inh : β)
(dec_eq : decidable_eq α)
(normal : α → Prop)
(dec_normal : decidable_pred normal)
(neg_prsv_normal : ∀ a, normal a → allp normal (atoms (neg a)))
(decr_prsv_normal : ∀ a, normal a → ¬ dep0 a → normal (decr a))

class atom_eq_type (α β : Type) extends atom_type α β :=
(solv0 : α → Prop)
(dec_solv0 : decidable_pred solv0)
(dest_solv0 : ∀ a, solv0 a → nat)
(solv0_eq : ∀ {e : α} (He : solv0 e) {b} {bs}, val (b::bs) e
  → list.nth_dft (atom_type.inh α β) (b::bs) (dest_solv0 e He) = b)
(trivial : α → Prop)
(dec_triv : decidable_pred trivial)
(true_triv : ∀ a, trivial a → ∀ xs, val xs a)
(subst0 : α → α → α)
(true_subst : ∀ e, solv0 e → ∀ bs, val bs (subst0 e e))
(subst_prsv : ∀ {e : α} (He : solv0 e), ∀ {a : α} {bs : list β}, 
  val bs (subst0 e a) ↔ val ((list.nth_dft (atom_type.inh α β) bs (dest_solv0 e He - 1))::bs) a)
(dest_pos : ∀ {a} {Ha : solv0 a}, ¬ trivial a → dest_solv0 a Ha > 0)

-- subst_eqn i j k returns the result of taking an 
-- identity atom of form (i = j) and using it to 
-- substitute a de Brujin variable k.
-- Requires : j = 0 ↔ ¬(i = 0)
def subst_eqn : nat → nat → nat → nat 
| 0 j 0 := j - 1
| (i+1) _ 0 := i  
| _ _ k := k - 1 

def isubst (k) : nat → nat 
| 0 := k
| (i + 1) := i

-- Qstn : Why do I need this? (Why doesn't unfold work?)
lemma exp_subst_eqn_i0 (i) : subst_eqn (i+1) 0 0 = i := 
begin refl end

variables {α β : Type}

def I [atom_type α β] (p : fm α) (xs : list β) := interp (atom_type.val) xs p 

lemma exp_I_and [atom_type α β] (p q : fm α) (xs : list β) : 
  I (p ∧' q) xs = ((I p xs) ∧ (I q xs)) := eq.refl _

lemma exp_I_and_o [atom_type α β] (p q : fm α) (xs : list β) : 
  I (and_o p q) xs = ((I p xs) ∧ (I q xs)) := 
begin
  apply (cases_and_o' (λ p q pq, ((I pq xs) = ((I p xs) ∧ (I q xs)))) p q), 
  repeat {unfold I, unfold interp, simp},
  unfold I, unfold interp 
end

lemma exp_I_or [atom_type α β] (p q : fm α) (xs : list β) : 
  I (p ∨' q) xs = ((I p xs) ∨ (I q xs)) := eq.refl _

lemma exp_I_or_o [atom_type α β] (p q : fm α) (xs : list β) : 
  I (or_o p q) xs ↔ ((I p xs) ∨ (I q xs)) := 
begin
  apply (cases_or_o' (λ p q pq, ((I pq xs) ↔ ((I p xs) ∨ (I q xs)))) p q), 
  repeat {unfold I, unfold interp, simp},
  unfold I, unfold interp 
end

lemma exp_I_not [atom_type α β] (p : fm α) (xs : list β) : 
  I (¬' p) xs = ¬ (I p xs) := eq.refl _

lemma exp_I_not_o [atom_type α β] (p : fm α) :
  ∀ (xs : list β), I (not_o p) xs ↔ ¬ (I p xs) :=
by cases p; {unfold not_o, unfold I, unfold interp, try {simp}}

lemma exp_I_ex [atom_type α β] (p : fm α) (xs) : @I α β _ (∃' p) xs = ∃ x, (I p (x::xs)) := 
by unfold I; unfold interp

lemma exp_I_top [atom_type α β] (xs) : @I α β _ ⊤' xs = true := 
by unfold I; unfold interp

lemma exp_I_bot [atom_type α β] (xs) : @I α β _ ⊥' xs = false := 
by unfold I; unfold interp

def fnormal_alt (β) [atom_type α β] (p : fm α) := 
  allp (atom_type.normal β) (@atoms _ (atom_type.dec_eq _ β) p)

def fnormal (β) [atom_type α β] : fm α → Prop 
| ⊤' := true
| ⊥' := true
| (A' a) := atom_type.normal β a 
| (p ∧' q) := fnormal p ∧ fnormal q
| (p ∨' q) := fnormal p ∧ fnormal q
| (¬' p) := fnormal p
| (∃' p) := fnormal p

lemma fnormal_iff_fnormal_alt [atom_type α β] : 
  ∀ {p : fm α}, fnormal β p ↔ fnormal_alt β p 
| ⊤' := true_iff_true trivial (λ a ha, by cases ha)
| ⊥' := true_iff_true trivial (λ a ha, by cases ha)
| (A' a) := 
  begin 
    unfold fnormal, 
    unfold fnormal_alt, unfold atoms,
    apply iff.intro; intro h, 
    intros a' ha', cases ha' with he he,
    subst he, apply h, cases he, 
    apply h, apply or.inl rfl
  end
| (p ∧' q) := 
  begin 
    unfold fnormal, 
    repeat {rewrite fnormal_iff_fnormal_alt}, 
    apply iff.symm, apply exp_allp_union
  end
| (p ∨' q) := 
  begin 
    unfold fnormal, 
    repeat {rewrite fnormal_iff_fnormal_alt}, 
    apply iff.symm, apply exp_allp_union
  end
| (¬' p) := 
  begin 
    unfold fnormal, 
    rewrite fnormal_iff_fnormal_alt, refl
  end
| (∃' p) := 
  begin 
    unfold fnormal, 
    rewrite fnormal_iff_fnormal_alt, refl
  end

def disj_to_prop (β) [atom_type α β] (as : list α) (bs : list β) : Prop :=
  allp (atom_type.val bs) as

instance atoms_dec_eq [atom_type α β] : decidable_eq α := 
atom_type.dec_eq α β

instance atoms_dec_dep0 [atom_type α β] : decidable_pred (atom_type.dep0 β) := 
atom_type.dec_dep0 α β

def atoms_dep0 (β) [atom_type α β] (p : fm α) := 
list.filter (atom_type.dep0 β) (atoms p)