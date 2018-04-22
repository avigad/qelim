import .auxiliary ...mathlib.data.list.basic

variables {α β γ : Type}

namespace list

def update_nth_force : list α → ℕ → α → α → list α
| (x::xs) 0     a a' := a :: xs
| (x::xs) (i+1) a a' := x :: update_nth_force xs i a a'
| []      0     a a' := [a] 
| []      (i+1) a a' := a' :: update_nth_force [] i a a'

def zip_pad (a' b') : list α → list β → list (α × β)
| [] [] := []
| [] (b::bs) := (a',b)::(zip_pad [] bs)
| (a::as) [] := (a,b')::(zip_pad as [])
| (a::as) (b::bs) := (a,b)::(zip_pad as bs)

lemma cons_zip_pad_cons {a b a' b'} {as : list α} {bs : list β} : 
  zip_pad a' b' (a::as) (b::bs) = (a,b)::(zip_pad a' b' as bs) :=
begin unfold zip_pad end

@[simp] def map_mul [has_mul α] (a) (as : list α) : list α :=
list.map (λ x, a * x) as

@[simp] def map_neg [has_neg α] (as : list α) : list α :=
list.map (λ x, -x) as

def comp_add [has_zero α] [has_add α] (as1 as2 : list α) : list α := 
list.map (λ xy, prod.fst xy + prod.snd xy) (list.zip_pad 0 0 as1 as2)

def comp_sub [has_zero α] [has_neg α] [has_add α] (as1 as2 : list α) : list α := 
comp_add as1 (map_neg as2)

def dot_prod [has_zero α] [has_add α] [has_mul α] (as1 as2 : list α) : α := 
list.sum (list.map (λ xy, prod.fst xy * prod.snd xy) (list.zip_pad 0 0 as1 as2))

@[simp] lemma nil_dot_prod [semiring α] :
  ∀ (as : list α), dot_prod [] as = 0  
| [] := 
  begin
    unfold dot_prod, unfold list.zip_pad, simp
  end
| (a::as) := 
  begin
    unfold dot_prod, unfold list.zip_pad,
    simp, apply nil_dot_prod
  end

@[simp] lemma dot_prod_nil [semiring α] :
  ∀ (as : list α), dot_prod as [] = 0  
| [] := 
  begin
    unfold dot_prod, unfold list.zip_pad, simp
  end
| (a::as) := 
  begin
    unfold dot_prod, unfold list.zip_pad,
    simp, apply dot_prod_nil
  end

@[simp] lemma cons_dot_prod_cons [semiring α] (a1 a2 : α) (as1 as2 : list α) : 
dot_prod (a1::as1) (a2::as2) = (a1 * a2) + dot_prod as1 as2 := 
begin unfold dot_prod, rewrite cons_zip_pad_cons, simp end

lemma nil_comp_add [semiring α] :
  ∀ (as : list α), comp_add [] as = as 
| [] := rfl 
| (a::as) := 
  begin
    unfold comp_add, unfold list.zip_pad,
    unfold list.map, simp, 
    have h := nil_comp_add as,
    unfold comp_add at h, rewrite h
  end

lemma comp_add_nil [semiring α] :
  ∀ (as : list α), comp_add as [] = as 
| [] := rfl
| (a::as) := 
  begin
    unfold comp_add, unfold list.zip_pad, 
    simp, have h := comp_add_nil as, 
    unfold comp_add at h, rewrite h 
  end

lemma cons_comp_add_cons [semiring α] (a1 a2 : α) (as1 as2) :
comp_add (a1::as1) (a2::as2) = (a1 + a2)::(comp_add as1 as2) := 
begin unfold comp_add, unfold list.zip_pad, simp end

lemma comp_add_dot_prod [semiring α] :
  ∀ (as1 as2 as3 : list α), dot_prod (comp_add as1 as2) as3 = (dot_prod as1 as3) + (dot_prod as2 as3)
| [] as2 as3 := 
  begin
    rewrite nil_comp_add, 
    rewrite nil_dot_prod, simp
  end
| as1 [] as3 := 
  begin
    rewrite comp_add_nil, 
    rewrite nil_dot_prod, simp
  end
| as1 as2 [] := 
  begin repeat {rewrite dot_prod_nil}, simp end
| (a1::as1) (a2::as2) (a3::as3) := 
  begin
    rewrite cons_comp_add_cons, 
    repeat {rewrite cons_dot_prod_cons},
    simp, rewrite add_mul, rewrite add_assoc,
    rewrite comp_add_dot_prod
  end

lemma map_mul_dot_prod [semiring α] (a : α) :
  ∀ (as1 as2), dot_prod (map_mul a as1) as2 = a * (dot_prod as1 as2) 
| [] as2 := 
  begin
    unfold map_mul, simp,
    repeat {rewrite nil_dot_prod}
  end
| as1 [] := 
  begin
    repeat {rewrite dot_prod_nil},
    rewrite mul_zero
  end
| (a1::as1) (a2::as2) := 
  begin
    unfold map_mul, simp, repeat {rewrite cons_dot_prod_cons}, 
    have h := map_mul_dot_prod as1 as2, unfold map_mul at h, 
    rewrite h, rewrite mul_add, simp, rewrite mul_assoc
  end

@[simp] lemma mul_dot_prod [semiring α] {a : α} {as1 as2} :
   a * (dot_prod as1 as2) = dot_prod (map_mul a as1) as2 :=
by rewrite map_mul_dot_prod  

def neg_dot_prod [ring α] : ∀ (as1 as2 : list α),  
  dot_prod (list.map (λ x, -x) as1) as2 = -(dot_prod as1 as2) := 
begin
  intros as1 as2,
  rewrite eq.symm (one_mul (dot_prod as1 as2)),
  rewrite neg_mul_eq_neg_mul, simp,
end

lemma sum_exp [has_zero α] [has_add α] (as : list α) :
  sum as = foldl (+) 0 as:= refl _

--def omap (f : α → option β) : list α → list β  
--| [] := []
--| (a::as) := 
--  match f a with 
--  | none := omap as 
--  | (some b) := b::(omap as) 
--  end
--
--lemma mem_omap {f : α → option β} {a} {b} (he : f a = some b) : 
--  ∀ {as : list α} (HM : a ∈ as), b ∈ omap f as  
--| [] hm := by cases hm
--| (a'::as) hm :=
--  begin 
--    unfold has_mem.mem at hm, unfold list.mem at hm,
--    cases hm with hm hm, subst hm,
--    unfold omap, rewrite he, apply or.inl rfl,
--    unfold omap, cases (f a'), 
--    apply mem_omap, apply hm, 
--    apply or.inr, apply mem_omap, apply hm 
--  end 
--
--lemma mem_omap_of_mem_omap_tail {f : α → option β} {a} {b} :
--  ∀ {as : list α}, b ∈ omap f as → b ∈ omap f (a::as) := 
--begin
--  intros as h, unfold omap, cases (f a),
--  apply h, apply or.inr h
--end
--
--lemma exp_mem_omap {f : α → option β} {b : β} : ∀ {as : list α}, (b ∈ omap f as) ↔ ∃ a, a ∈ as ∧ some b = f a 
--| [] := 
--  iff.intro 
--    (by {intro h, cases h}) 
--    (begin intro h, cases h with a ha, cases ha^.elim_left end)
--| (a::as) := 
-- iff.intro 
-- (begin
--    intro h, unfold omap at h, 
--    cases (dest_option (f a)) with ho ho, 
--    rewrite ho at h, 
--    cases (exp_mem_omap^.elim_left h) with a' ha', 
--    cases ha' with ha1' ha2',
--    existsi a', apply and.intro (or.inr ha1') ha2',
--    cases ho with b' hb', rewrite hb' at h,
--    unfold omap at h, rewrite mem_cons_iff at h,
--    cases h with h h, existsi a,
--    apply and.intro (or.inl rfl), rewrite h,
--    apply eq.symm hb',
--    cases (exp_mem_omap^.elim_left h) with a' ha', 
--    cases ha' with ha1' ha2',
--    existsi a', apply and.intro (or.inr ha1') ha2'
--  end)
-- (begin 
--   intro h, cases h with a' ha', 
--   cases ha' with h1 h2, rewrite mem_cons_iff at h1, 
--   cases h1 with h1 h1, 
--   unfold omap, subst h1, rewrite eq.symm h2, 
--   apply or.inl rfl, apply mem_omap_of_mem_omap_tail,
--   apply exp_mem_omap^.elim_right, existsi a',
--   apply and.intro h1 h2
--  end)

lemma exists_maximum [linear_order β] : 
∀ (bs : list β) (hi : bs ≠ []), ∃ b, b ∈ bs ∧ ∀ b' ∈ bs, b' ≤ b 
| [] hi := begin exfalso, apply hi rfl end
| [b] hi := 
  begin
    existsi b, apply and.intro (or.inl rfl), 
    intros b' hb', cases hb' with hb' hb', 
    subst hb', cases hb',
  end
| (b::b'::bs') hi := 
  begin
    cases (exists_maximum (b'::bs') _) with bm hbm, 
    cases hbm with hbm1 hbm2,
    apply @classical.by_cases (b ≤ bm); intro hle,

    existsi bm, apply and.intro (or.inr hbm1), 
    intros bl hbl, rewrite mem_cons_iff at hbl, 
    cases hbl with hbl hbl, subst hbl, apply hle, 
    apply hbm2 _ hbl,

    existsi b, apply and.intro (or.inl rfl),
    intros bl hbl, rewrite mem_cons_iff at hbl, 
    cases hbl with hbl hbl, subst hbl, 
    apply le_trans, apply hbm2 _ hbl, 
    apply le_of_not_le hle, 
    intro hc, cases hc 
  end

lemma exists_minimum [hlo : linear_order β] : 
∀ (bs : list β) (hi : bs ≠ []), ∃ b, b ∈ bs ∧ ∀ b' ∈ bs, b' ≥ b :=  
@exists_maximum _ (converse_linear_order hlo)


lemma dest_list : ∀ (as : list α), as = [] ∨ ∃ a' as', as = (a'::as')
| [] := or.inl rfl 
| (a::as) := begin apply or.inr, existsi a, existsi as, refl end


-- def list.product : list α → list β → list (α × β) 
-- | [] _ := []
-- | (a1::l1) l2 := (list.map (λ a2, ⟨a1,a2⟩) l2) ++ list.product l1 l2 

def pluck (p : α → Prop) [decidable_pred p] : list α → option (α × list α)
| []      := none 
| (a::as) := 
  if p a 
  then some (a, as) 
  else do (a',as') ← pluck as, 
          some (a',a::as')

def pluck_true (p : α → Prop) [decidable_pred p] (a as) (ha : p a) :
  pluck p (a::as) = some (a,as) := 
begin unfold pluck, rewrite ite_eq_of, apply ha end

def pluck_false (p : α → Prop) [decidable_pred p] (a as) (ha : ¬ p a) :
  pluck p (a::as) 
  = (do (a',as') ← pluck p as, some (a',a::as') ) := 
begin unfold pluck, rewrite ite_eq_of_not, refl, apply ha end

/- equiv -/

def equiv (l1 l2 : list α) := l1 ⊆ l2 ∧ l2 ⊆ l1

notation l1 `≃` l2 := equiv l1 l2

def equiv.refl {l : list α} : l ≃ l := 
and.intro (subset.refl _) (subset.refl _)

def equiv.symm {as1 as2 : list α} : (as1 ≃ as2) → (as2 ≃ as1) :=
begin
  intro h, cases h with h1 h2, 
  apply and.intro; assumption
end 

lemma equiv.trans {l1 l2 l3 : list α} : (l1 ≃ l2) → (l2 ≃ l3) → (l1 ≃ l3) :=  
begin
  intros h1 h2,
  cases h1 with h1a h1b, cases h2 with h2a h2b, 
  apply and.intro (subset.trans h1a h2a) (subset.trans h2b h1b),
end 

lemma subset.swap {a1 a2 : α} {l} : (a1::a2::l) ⊆ (a2::a1::l) :=  
begin
  intros a ha, cases ha with ha ha,
  apply or.inr (or.inl ha), cases ha with ha ha,
  apply or.inl ha, apply or.inr (or.inr ha)
end

lemma equiv.swap {a1 a2 : α} {l} : (a1::a2::l) ≃ (a2::a1::l) :=  
begin apply and.intro; apply subset.swap end

lemma cons_equiv_cons {a : α} {l1 l2} : (l1 ≃ l2) → ((a::l1) ≃ (a::l2)) := 
begin
  intro h, cases h with hl hr,
  apply and.intro; apply cons_subset_cons; assumption
end

lemma mem_iff_mem_of_equiv {as1 as2 : list α} :
  (as1 ≃ as2) → ∀ (a : α), a ∈ as1 ↔ a ∈ as2 := 
begin
  intros heqv a, cases heqv with hss1 hss2, 
  apply iff.intro; intro hm,
  apply hss1; assumption,
  apply hss2; assumption
end

lemma map_union [decidable_eq α] [decidable_eq β] 
  {f : α → β} {as1 as2 : list α} :
  map f (as1 ∪ as2) ≃ (map f as1) ∪ (map f as2) := 
begin
  apply and.intro; intros x hx,
  rewrite mem_map at hx, cases hx with y hy,
  cases hy with hy1 hy2, subst hy2, 
  rewrite mem_union at hy1,
  cases hy1 with hym hym, 
  apply mem_union_left, rewrite mem_map,
  existsi y, apply and.intro, assumption, refl,
  apply mem_union_right, rewrite mem_map,
  existsi y, apply and.intro, assumption, refl,
  rewrite mem_union at hx, cases hx with hx hx;
  rewrite mem_map at hx; cases hx with y hy;
  rewrite mem_map; existsi y; cases hy with hy1 hy2;
  apply and.intro _ hy2,
  apply mem_union_left hy1, 
  apply mem_union_right _ hy1
end

lemma map_subset_map_of_subset 
  {f : α → β} {as1 as2 : list α} :
  (as1 ⊆ as2) → (map f as1 ⊆ map f as2) :=
begin
  intros hss b hb,
  rewrite mem_map at *, cases hb with a ha,
  cases ha with ha1 ha2, subst ha2, 
  existsi a, apply and.intro _ rfl,
  apply hss ha1
end 

lemma map_equiv_map_of_equiv 
  {f : α → β} {as1 as2 : list α} :
  (as1 ≃ as2) → (map f as1 ≃ map f as2) :=
begin
  intro heqv, cases heqv with hss1 hss2,
  apply and.intro; 
  apply map_subset_map_of_subset; assumption
end 

lemma union_subset_union_of_subset [decidable_eq α]
  {as1 as1' as2 : list α} : (as1 ⊆ as1') → (as1 ∪ as2 ⊆ as1' ∪ as2) :=
begin
  intros h a ha, rewrite mem_union at ha,
  cases ha with ha ha, 
  apply mem_union_left, apply h ha,
  apply mem_union_right, apply ha
end

lemma union_equiv_union_of_equiv [decidable_eq α]
  {as1 as1' as2 : list α} : (as1 ≃ as1') → (as1 ∪ as2 ≃ as1' ∪ as2) :=
begin
  intro h, cases h with h1 h2,
  apply and.intro; 
  apply union_subset_union_of_subset; assumption
end

lemma union_comm [decidable_eq α]
 {as1 as2 : list α} : (as1 ∪ as2 ≃ as2 ∪ as1) :=
begin
  apply and.intro; intros a ha;
  rewrite mem_union at ha; cases ha with ha ha;
  {apply mem_union_left ha <|> apply mem_union_right _ ha}
end

lemma filter_union [decidable_eq α]
  {P : α → Prop} [decidable_pred P]
  {as1 as2 : list α} :
  filter P (as1 ∪ as2) ≃ (filter P as1 ∪ filter P as2) :=
begin
  apply and.intro; intros a ha;
  rewrite mem_union at *; repeat {rewrite mem_filter at *};
  cases ha with ha1 ha2, rewrite mem_union at ha1,
  cases ha1 with hm hm, apply or.inl, 
  apply and.intro; assumption, apply or.inr, 
  apply and.intro; assumption,
  cases ha1 with hm hP,
  apply and.intro _ hP, apply mem_union_left hm,
  cases ha2 with hm hP,
  apply and.intro _ hP, apply mem_union_right _ hm
end



def anyp (P : α → Prop) (l : list α) := ∃ a, a ∈ l ∧ P a

lemma cases_pluck (P : α → Prop) [hd : decidable_pred P] : ∀ (as : list α), 
(pluck P as = none ∧ (∀ x ∈ as, ¬ P x)) 
∨ ∃ (a) (as'), (pluck P as = some (a,as') ∧ P a ∧ (as ≃ (a::as')))
| [] := 
  begin 
    apply or.inl, apply and.intro, 
    unfold pluck, intros _ H, cases H
  end
| (a::as) :=
  begin
    cases (hd a) with ha ha, 
    cases (cases_pluck as) with has has,

    apply or.inl, cases has with has1 has2,
    apply and.intro, rewrite pluck_false,
    rewrite has1, refl, apply ha,
    rewrite forall_mem_cons,
    apply and.intro ha has2,

    apply or.inr, cases has with a' has,
    cases has with as' has',
    cases has' with h1 has', cases has' with h2 h3,
    existsi a', existsi (a::as'),
    apply and.intro, rewrite pluck_false, 
    rewrite h1, refl, apply ha, apply and.intro h2,
    apply equiv.trans, apply cons_equiv_cons, 
    apply h3, apply equiv.swap,
    
    apply or.inr, existsi a, existsi as,
    apply and.intro, rewrite pluck_true, apply ha,
    apply and.intro ha equiv.refl
  end



@[simp] def nth_dft (a : α) (l : list α) (n : nat) : α :=  
match nth l n with 
| none := a 
| (some a') := a'
end

def head_dft (a' : α) : list α → α 
| [] := a'
| (a::as) := a 

lemma nth_pred (a : α) (l : list α) (n : nat) (H : n > 0) : 
nth (a::l) n = nth l (n - 1) := 
begin cases n, cases H, simp end

lemma nth_dft_pred {a a' : α} {l : list α} {n : nat} (H : n > 0) : 
nth_dft a (a'::l) n = nth_dft a l (n - 1) :=
begin unfold nth_dft, rewrite nth_pred, apply H  end

lemma nth_dft_succ {a a' : α} {l : list α} {n : nat} : 
nth_dft a (a'::l) (n+1) = nth_dft a l n :=
begin unfold nth_dft, simp  end

lemma nth_dft_head {a a' : α} {as : list α} : nth_dft a' (a::as) 0 = a := 
begin unfold nth_dft, simp end

@[simp] def append_pair {α : Type} : (list α × list α) → list α  
| (l1,l2) := l1 ++ l2 

def all_true (ps : list Prop) : Prop := ∀ (p : Prop), p ∈ ps → p

lemma all_true_nil : all_true [] := 
by {intros _ H, cases H}

-- def disj_list : list Prop → Prop 
-- | [] := false
-- | (p::ps) := p ∨ disj_list ps

def some_true (ps : list Prop) : Prop := ∃ (p : Prop), p ∈ ps ∧ p

lemma some_true_nil : some_true [] ↔ false :=
begin
  apply iff.intro; intro h, cases h with p hp,
  cases hp^.elim_left, cases h
end

lemma some_true_cons (p ps) : some_true (p::ps) ↔ (p ∨ some_true ps) :=
begin
  apply iff.intro; intro h, cases h with q hq,
  cases hq with hq1 hq2, rewrite mem_cons_iff at hq1,
  cases hq1 with hq1 hq1, subst hq1, apply or.inl hq2,
  apply or.inr, existsi q, apply and.intro hq1 hq2,
  cases h with h h, existsi p, simp, apply h,
  cases h with q hq, cases hq with hq1 hq2,
  existsi q, apply and.intro (or.inr hq1) hq2
end

lemma some_true_append {ps1 ps2} : some_true (ps1 ++ ps2) ↔ (some_true ps1 ∨ some_true ps2) := 
begin
  apply iff.intro; intro h, cases h with p hp,
  cases hp with hp1 hp2, rewrite mem_append at hp1,
  cases hp1 with hp1 hp1, 
  apply or.inl, existsi p, apply and.intro; assumption, 
  apply or.inr, existsi p, apply and.intro; assumption, 
  cases h with h h; cases h with p hp; cases hp with hp1 hp2;
  existsi p; apply and.intro, 
  apply mem_append_left, apply hp1, apply hp2,
  apply mem_append_right, apply hp1, apply hp2
end

lemma forall_mem_append {P : α → Prop} {as1 as2 : list α} : 
  (∀ a ∈ (as1 ++ as2), P a) ↔ ((∀ a ∈ as1, P a) ∧ (∀ a ∈ as2, P a)) := 
begin
  apply iff.intro; intro h, 
  apply and.intro; intros a ha; apply h,
  apply mem_append_left _ ha,
  apply mem_append_right _ ha,
  intros a ha, rewrite mem_append at ha,
  cases h with hl hr, cases ha with ha ha,
  apply hl _ ha, apply hr _ ha
end
/-
lemma some_true_iff_disj_list : 
  ∀ {ps : list Prop}, some_true ps ↔ disj_list ps 
| [] :=
  begin 
    unfold some_true, unfold disj_list, 
    apply iff.intro; intro h, cases h with x hx,
    cases hx^.elim_left, exfalso, apply h
  end
| (p::ps) := 
  begin
    unfold some_true, unfold disj_list, 
    apply iff.intro; intro h, cases h with x hx,
    cases hx with hx1 hx2, rewrite mem_cons_iff at hx1,
    cases hx1 with hx1 hx1, subst hx1, apply or.inl hx2, 
    rewrite iff.symm some_true_iff_disj_list,
    apply or.inr, existsi x, apply and.intro hx1 hx2,
    cases h with h h, existsi p, 
    apply and.intro (or.inl rfl) h, 
    rewrite iff.symm some_true_iff_disj_list at h,
    cases h with x hx, existsi x, cases hx with hx1 hx2,
    apply and.intro (or.inr hx1) hx2 
  end

lemma disj_list_iff_some_true : ∀ (ps : list Prop), disj_list ps ↔ some_true ps 
| [] := 
  begin
    apply iff.intro, intro H, cases H, 
    intro H, cases H with H1 H2, cases (H2^.elim_left) 
  end
| (p::ps) :=
  begin
    apply iff.intro, intro H, cases H with H H, 
    existsi p, apply and.intro, 
    apply or.inl (eq.refl _), apply H, 
    cases ((disj_list_iff_some_true ps)^.elim_left H) with p Hp,
    existsi p, apply and.intro, 
    apply or.inr (Hp^.elim_left),
    apply Hp^.elim_right, 
    unfold some_true, unfold disj_list,
    unfold has_mem.mem, unfold list.mem,
    intro H, cases H with p' Hp', 
    cases (Hp'^.elim_left) with HM HM,
    apply or.inl, rewrite (eq.symm HM), 
    apply Hp'^.elim_right, 
    apply or.inr, rewrite disj_list_iff_some_true,
    existsi p', apply (and.intro HM Hp'^.elim_right)

  end
-/


-- lemma disj_list_dist_append (l1 l2 : list Prop) : disj_list (l1 ++ l2) = (disj_list l1 ∨ disj_list l2) :=  
-- begin
--   repeat {rewrite disj_list_iff_some_true}, 
--   apply propext, apply iff.intro,
--   intro H, cases H with x Hx, 
--   cases Hx with Hl Hr, cases (mem_or_mem_of_mem_append Hl) with HM HM, 
--   apply or.inl, existsi x, apply and.intro HM Hr,
--   apply or.inr, existsi x, apply and.intro HM Hr,
--   intro H, cases H with H H; cases H with x Hx ; cases Hx with Hl Hr ; existsi x ; apply and.intro, 
--   apply mem_append_of_mem_or_mem, 
--   apply or.inl, apply Hl, apply Hr, 
--   apply mem_append_of_mem_or_mem, 
--   apply or.inr, apply Hl, apply Hr 
-- end


-- def ex_arg_of_mem_map {f : α → β} {b : β} : 
--   ∀ {as : list α}, (b ∈ list.map f as) → ∃ a, a ∈ as ∧ b = f a 
-- | [] H := by cases H 
-- | (a::as) H := 
--   begin
--     simp at H, cases H with H H, existsi a, 
--     apply and.intro (or.inl (eq.refl _)) H,  
--     cases (list.exists_of_mem_map H) with a' Ha',
--     existsi a', apply and.intro, 
--     apply or.inr (Ha'^.elim_left), 
--     apply Ha'^.elim_right
--   end


lemma fst_mem_of_mem_product : 
  ∀ {as : list α} {bs : list β} {p : α × β}, 
    p ∈ (product as bs) → (prod.fst p) ∈ as  
| [] bs b H := begin unfold product at H, cases H end
| (a::as) bs ab h := 
  begin
    unfold product at h, simp at h, cases h with h h,
    
    cases h with b hb, cases hb with hb1 hb2,
    rewrite eq.symm hb2, apply or.inl rfl, 

    cases h with a' h, cases h with h1 h2, 
    cases h2 with b hb, cases hb with hb1 hb2, 
    rewrite eq.symm hb2, apply or.inr, apply h1
  end

lemma snd_mem_of_mem_product : 
  ∀ {as : list α} {bs : list β} {p : α × β}, 
    p ∈ (product as bs) → (prod.snd p) ∈ bs 
| [] bs b H := begin unfold product at H, cases H end
| (a::as) bs ab h := 
  begin
    unfold product at h, simp at h, cases h with h h,
    
    cases h with b hb, cases hb with hb1 hb2,
    rewrite eq.symm hb2, apply hb1, 

    cases h with a' h, cases h with h1 h2, 
    cases h2 with b hb, cases hb with hb1 hb2, 
    rewrite eq.symm hb2, apply hb1
  end


lemma forall_mem_map_of_forall_mem (P : α → Prop) {Q : β → Prop} {f : α → β} {as} : 
(∀ a ∈ as, P a) → (∀ a, P a → Q (f a)) → (∀ b ∈ (map f as), Q b) := 
begin
  intros has hf b hb, 
  rewrite mem_map at hb, 
  cases hb with a ha, cases ha with ha1 ha2,
  subst ha2, apply hf, apply has, apply ha1
end

lemma mem_product_of_mem_and_mem {as : list α} {bs : list β} 
  {a : α} {b : β} (h : a ∈ as ∧ b ∈ bs) : (a,b) ∈ product as bs := 
begin rewrite mem_product, apply h end


lemma map_eq (f g : α → β) : ∀ (as : list α) (H : ∀ a ∈ as, f a = g a), map f as = map g as 
| [] _ := eq.refl _
| (a::as) H := 
  begin 
    unfold map, rewrite H, rewrite map_eq,
    intros a Ha, apply (H _ (or.inr Ha)),  
    apply (or.inl (eq.refl _))
  end

meta def first_arg (f : α → tactic β) : list α → tactic β 
| [] := tactic.failed 
| (a::as) := f a <|> (first_arg as)

lemma forall_mem_filter_of_forall_mem {P Q : α → Prop} [H : decidable_pred Q] 
  {as : list α} (h : ∀ a ∈ as, P a) : ∀ a ∈ (list.filter Q as), P a := 
begin
  intros a ha, apply h, 
  apply mem_of_mem_filter ha 
end

@[simp] def allp (P : α → Prop) (as : list α) := ∀ a ∈ as, P a

lemma allp_iff_forall_mem (P : α → Prop) (as : list α) :
  (allp P as) ↔ (∀ a ∈ as, P a) :=
by unfold allp

lemma map_one_mul [monoid α] : 
  ∀ (l : list α), map (has_mul.mul (1 : α)) l = l 
| [] := refl _
| (a::as) := begin simp, apply map_one_mul end

end list