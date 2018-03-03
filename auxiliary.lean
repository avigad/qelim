variables {α β γ : Type}

lemma iff_of_eq {p q} : p = q → (p ↔ q) :=
begin intro h, rewrite h end

lemma exp_ite_true (p : Prop) [hd : decidable p] (h : p) (x y : α) : ite p x y = x := 
begin
  unfold ite, cases hd with hd hd, exfalso, 
  apply hd h, simp, 
end

lemma exp_ite_false (p : Prop) [hd : decidable p] (h : ¬ p) (x y : α) : ite p x y = y := 
begin
  unfold ite, cases hd with hd hd, simp, 
  exfalso, apply h hd
end

def list.omap (f : α → option β) : list α → list β  
| [] := []
| (a::as) := 
  match f a with 
  | none := list.omap as 
  | (some b) := b::(list.omap as) 
  end

lemma exp_mem {a' a : α} {as} : a' ∈ a::as ↔ (a' = a ∨ a' ∈ as) := 
by {unfold has_mem.mem, unfold list.mem}

lemma eq_nil_of_map_eq_nil {f : α → β} {as}  
  (h : list.map f as = []) : as = [] :=
begin cases as, refl, cases h end

def converse_linear_order (hlo : linear_order β) : linear_order β := 
{ le := λ x y, x ≥ y,
  le_refl := preorder.le_refl, 
  le_trans := λ x y z hxy hyz, preorder.le_trans z y x hyz hxy,
  le_antisymm := λ x y hxy hyx, partial_order.le_antisymm _ _ hyx hxy,
  le_total := λ x y, linear_order.le_total _ _ }

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
    intros bl hbl, rewrite exp_mem at hbl, 
    cases hbl with hbl hbl, subst hbl, apply hle, 
    apply hbm2 _ hbl,

    existsi b, apply and.intro (or.inl rfl),
    intros bl hbl, rewrite exp_mem at hbl, 
    cases hbl with hbl hbl, subst hbl, 
    apply le_trans, apply hbm2 _ hbl, 
    apply le_of_not_le hle, 
    intro hc, cases hc 
  end

lemma exists_minimum [hlo : linear_order β] : 
∀ (bs : list β) (hi : bs ≠ []), ∃ b, b ∈ bs ∧ ∀ b' ∈ bs, b' ≥ b :=  
@exists_maximum _ (converse_linear_order hlo)

lemma mem_omap {f : α → option β} {a} {b} (he : f a = some b) : 
  ∀ {as : list α} (HM : a ∈ as), b ∈ list.omap f as  
| [] hm := by cases hm
| (a'::as) hm :=
  begin 
    unfold has_mem.mem at hm, unfold list.mem at hm,
    cases hm with hm hm, subst hm,
    unfold list.omap, rewrite he, apply or.inl rfl,
    unfold list.omap, cases (f a'), 
    apply mem_omap, apply hm, 
    apply or.inr, apply mem_omap, apply hm 
  end 

lemma mem_omap_of_mem_omap_tail {f : α → option β} {a} {b} :
  ∀ {as : list α}, b ∈ list.omap f as → b ∈ list.omap f (a::as) := 
begin
  intros as h, unfold list.omap, cases (f a),
  apply h, apply or.inr h
end

lemma dest_option : ∀ (o : option α), o = none ∨ ∃ a, o = some a  
| none := or.inl rfl 
| (some a) := begin apply or.inr, existsi a, refl end

lemma dest_list : ∀ (as : list α), as = [] ∨ ∃ a' as', as = (a'::as')
| [] := or.inl rfl 
| (a::as) := begin apply or.inr, existsi a, existsi as, refl end

lemma exp_mem_omap {f : α → option β} {b : β} : ∀ {as : list α}, (b ∈ list.omap f as) ↔ ∃ a, a ∈ as ∧ some b = f a 
| [] := 
  iff.intro 
    (by {intro h, cases h}) 
    (begin intro h, cases h with a ha, cases ha^.elim_left end)
| (a::as) := 
 iff.intro 
 (begin
    intro h, unfold list.omap at h, 
    cases (dest_option (f a)) with ho ho, 
    rewrite ho at h, 
    cases (exp_mem_omap^.elim_left h) with a' ha', 
    cases ha' with ha1' ha2',
    existsi a', apply and.intro (or.inr ha1') ha2',
    cases ho with b' hb', rewrite hb' at h,
    unfold list.omap at h, rewrite exp_mem at h,
    cases h with h h, existsi a,
    apply and.intro (or.inl rfl), rewrite h,
    apply eq.symm hb',
    cases (exp_mem_omap^.elim_left h) with a' ha', 
    cases ha' with ha1' ha2',
    existsi a', apply and.intro (or.inr ha1') ha2'
  end)
 (begin 
   intro h, cases h with a' ha', 
   cases ha' with h1 h2, rewrite exp_mem at h1, 
   cases h1 with h1 h1, 
   unfold list.omap, subst h1, rewrite eq.symm h2, 
   apply or.inl rfl, apply mem_omap_of_mem_omap_tail,
   apply exp_mem_omap^.elim_right, existsi a',
   apply and.intro h1 h2
  end)

def list.product : list α → list β → list (α × β) 
| [] _ := []
| (a1::l1) l2 := (list.map (λ a2, ⟨a1,a2⟩) l2) ++ list.product l1 l2 

lemma product_nil : ∀ {l : list α}, list.product l (@list.nil β) = [] 
| [] := by unfold list.product   
| (a::as) := 
  begin unfold list.product, rewrite product_nil, simp, end

def list.first (p : α → Prop) [decidable_pred p] : list α → option (α × list α)
| []      := none 
| (a::as) := 
  if p a 
  then some (a, as) 
  else do (a',as') ← list.first as, 
          some (a',a::as')

def list.eqmem (l1 l2 : list α) := ∀ (a : α), (a ∈ l1 ↔ a ∈ l2)

lemma eqmem_refl {l : list α} : list.eqmem l l := λ a, iff.refl _

lemma eqmem_trans {l1 l2 l3 : list α} : list.eqmem l1 l2 → list.eqmem l2 l3 → list.eqmem l1 l3 :=  
begin
  intros H1 H2, intro x, apply iff.trans,
  apply H1, apply H2
end 

lemma eqmem_swap {a1 a2 : α} {l} : list.eqmem (a1::a2::l) (a2::a1::l) :=  
begin
  intro a, apply iff.intro, 
  intro H, cases H with H H, subst H, 
  apply or.inr, apply or.inl, refl,
  cases H with H H, subst H, 
  apply or.inl, refl,
  apply or.inr, apply or.inr, apply H,
  intro H, cases H with H H, subst H, 
  apply or.inr, apply or.inl, refl,
  cases H with H H, subst H, 
  apply or.inl, refl,
  apply or.inr, apply or.inr, apply H,
end

lemma eqmem_cons {a : α} {l1 l2} : list.eqmem l1 l2 → list.eqmem (a::l1) (a::l2) := 
begin
  intros H a', apply iff.intro, 
  intro HM, cases HM with HM HM, 
  apply or.inl HM, apply or.inr, 
  apply (H a')^.elim_left, apply HM,
  intro HM, cases HM with HM HM, 
  apply or.inl HM, apply or.inr, 
  apply (H a')^.elim_right, apply HM,
end

def allp (P : α → Prop) (l : list α) := ∀ a, a ∈ l → P a

def anyp (P : α → Prop) (l : list α) := ∃ a, a ∈ l ∧ P a

lemma allp_nil {P : α → Prop} : allp P [] :=
begin intros _ H, cases H end

lemma allp_of_allp {P Q : α → Prop} (H : ∀ a, P a → Q a) 
  (as) (HP : allp P as) : allp Q as :=
begin intros a Ha, apply H, apply HP, apply Ha end

lemma cases_ite {P} {Q : α → Prop} {HD : decidable P} {f g : α} 
  (Hf : P → Q f) (Hg : ¬ P → Q g) : Q (@ite P HD α f g) := 
begin
  unfold ite, cases HD with h h, simp, apply Hg h,
  simp, apply Hf h
end

lemma eq_true_or_eq_false_of_dec (P) [HP : decidable P] : P = true ∨ P = false :=
begin
  cases HP, 
  apply or.inr, rewrite eq_false, simp *,
  apply or.inl, rewrite eq_true, simp *,
end

def dec_allp {P : α → Prop} [HP : decidable_pred P] : decidable_pred (allp P)  
| [] := is_true (by apply allp_nil)
| (a::as) := 
  begin
    cases (HP a) with HP HP, apply is_false, intro HC,  
    apply absurd (HC a (or.inl (by refl))) HP,
    cases (dec_allp as) with Has Has, 
    apply is_false, intro HC, apply Has, 
    intros x Hx, apply HC, apply or.inr Hx, 
    apply is_true, intros x Hx, cases Hx with Hx Hx,
    rewrite Hx, apply HP, apply Has x Hx 
  end

lemma cases_first (P : α → Prop) [HD : decidable_pred P] : ∀ (as : list α), 
(list.first P as = none ∧ allp (λ x, ¬ P x) as) 
∨ ∃ (a) (as'), (list.first P as = some (a,as') ∧ P a ∧ list.eqmem as (a::as'))
| [] := 
  begin 
    apply or.inl, apply and.intro, 
    unfold list.first, intros _ H, cases H
  end
| (a::as) :=
  begin
    repeat {unfold list.first, unfold ite}, simp,
    cases (HD a) with Ha Ha, simp, 
    cases (cases_first as) with Has Has,  
    cases Has with Has1 Has2, 
    apply or.inl, apply and.intro, 
    intros x Hx, cases Hx with Hx Hx,
    rewrite Hx, apply Ha, apply Has2, apply Hx,
    rewrite Has1, refl, 
    cases Has with x Has, cases Has with xs Hx,  
    apply or.inr, existsi x, existsi (a::xs),
    cases Hx with Hx1 Hx, cases Hx with Hx2 Hx3, 
    apply and.intro, apply Hx2, 
    apply and.intro, 
    apply eqmem_trans _ eqmem_swap,
    apply eqmem_cons Hx3, rewrite Hx1,
    refl, apply or.inr, existsi a, existsi as,
    apply and.intro Ha, apply and.intro, 
    apply eqmem_refl, simp
  end

@[simp] def list.nth_dft (a : α) (l : list α) (n : nat) : α :=  
match list.nth l n with 
| none := a 
| (some a') := a'
end

lemma nth_pred (a : α) (l : list α) (n : nat) (H : n > 0) : 
list.nth (a::l) n = list.nth l (n - 1) := 
begin cases n, cases H, simp end

lemma nth_dft_pred {a a' : α} {l : list α} {n : nat} (H : n > 0) : 
list.nth_dft a (a'::l) n = list.nth_dft a l (n - 1) :=
begin unfold list.nth_dft, rewrite nth_pred, apply H  end

lemma nth_dft_succ {a a' : α} {l : list α} {n : nat} : 
list.nth_dft a (a'::l) (n+1) = list.nth_dft a l n :=
begin unfold list.nth_dft, simp  end

lemma true_iff_true {p q} : p → q → (p ↔ q) := 
by {intros hp hq, apply iff.intro ; intro _, apply hq, apply hp}

lemma false_iff_false {p q} : ¬ p → ¬ q → (p ↔ q) := 
begin
  intros hnp hnq, apply iff.intro, 
  intro hp, apply absurd hp hnp,
  intro hq, apply absurd hq hnq
end

lemma nth_dft_head {a a' : α} {as : list α} : list.nth_dft a' (a::as) 0 = a := 
begin unfold list.nth_dft, simp end

def append_pair {α : Type} : (list α × list α) → list α  
| (l1,l2) := l1 ++ l2 

def all_true (ps : list Prop) : Prop := ∀ (p : Prop), p ∈ ps → p

lemma all_true_nil : all_true [] := 
by {intros _ H, cases H}

def disj_list : list Prop → Prop 
| [] := false
| (p::ps) := p ∨ disj_list ps

def some_true (ps : list Prop) : Prop := ∃ (p : Prop), p ∈ ps ∧ p

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

lemma mem_append_of_mem_or_mem : ∀ {l1 l2 : list α} {a : α}, a ∈ l1 ∨ a ∈ l2 → a ∈ (l1 ++ l2)  
| [] l2 a := 
  begin intro H, cases H with H H, cases H, simp, apply H end
| (a'::l1) l2 a:= 
  begin
    unfold has_mem.mem, unfold list.mem, intro H, 
    cases H with H H, cases H with H1 H2, 
    apply or.inl, apply H1, 
    apply or.inr, 
    apply mem_append_of_mem_or_mem,
    apply or.inl, apply H2, 
    apply or.inr, 
    apply mem_append_of_mem_or_mem,
    apply or.inr, apply H 
  end

lemma mem_or_mem_of_mem_append : ∀ {l1 l2 : list α} {a : α}, a ∈ (l1 ++ l2) → a ∈ l1 ∨ a ∈ l2 
| [] l2 a H := 
  begin 
    apply or.inr, apply H 
  end
| (a'::l1) l2 a H := 
  begin 
    cases H with H H, 
    apply or.inl, apply or.inl, apply H, 
    cases (mem_or_mem_of_mem_append H) with H1 H1 ; clear H,
    apply or.inl, apply or.inr H1,
    apply or.inr H1
  end

lemma disj_list_dist_append (l1 l2 : list Prop) : disj_list (l1 ++ l2) = (disj_list l1 ∨ disj_list l2) :=  
begin
  repeat {rewrite disj_list_iff_some_true}, 
  apply propext, apply iff.intro,
  intro H, cases H with x Hx, 
  cases Hx with Hl Hr, cases (mem_or_mem_of_mem_append Hl) with HM HM, 
  apply or.inl, existsi x, apply and.intro HM Hr,
  apply or.inr, existsi x, apply and.intro HM Hr,
  intro H, cases H with H H; cases H with x Hx ; cases Hx with Hl Hr ; existsi x ; apply and.intro, 
  apply mem_append_of_mem_or_mem, 
  apply or.inl, apply Hl, apply Hr, 
  apply mem_append_of_mem_or_mem, 
  apply or.inr, apply Hl, apply Hr 
end

def ex_arg_of_mem_map {f : α → β} {b : β} : ∀ {as : list α} (H : b ∈ list.map f as), ∃ a, a ∈ as ∧ b = f a 
| [] H := by cases H 
| (a::as) H := 
  begin
    simp at H, cases H with H H, existsi a, 
    apply and.intro (or.inl (eq.refl _)) H,  
    cases (ex_arg_of_mem_map H) with a' Ha',
    existsi a', apply and.intro, 
    apply or.inr (Ha'^.elim_left), 
    apply Ha'^.elim_right
  end

lemma fst_mem_of_mem_product : 
  ∀ {as : list α} {bs : list β} {p : α × β}, 
    p ∈ (list.product as bs) → (prod.fst p) ∈ as  
| [] bs b H := begin unfold list.product at H, cases H end
| (a::as) bs b H := 
  begin
    unfold list.product at H, simp at H, cases H with H H,
    apply or.inr, apply fst_mem_of_mem_product, apply H,
    cases (ex_arg_of_mem_map H) with x Hx, 
    rewrite Hx^.elim_right, apply or.inl, refl
  end

lemma snd_mem_of_mem_product : 
  ∀ {as : list α} {bs : list β} {p : α × β}, 
    p ∈ (list.product as bs) → (prod.snd p) ∈ bs 
| [] bs b H := begin unfold list.product at H, cases H end
| (a::as) bs b H := 
  begin
    unfold list.product at H, simp at H, cases H with H H,
    apply snd_mem_of_mem_product, apply H,
    cases (ex_arg_of_mem_map H) with x Hx, 
    rewrite Hx^.elim_right, apply Hx^.elim_left
  end

def mem_map_of_mem {f : α → β} : ∀ (as : list α) (a : α), a ∈ as → (f a) ∈ list.map f as 
| [] a H := by cases H 
| (a'::as) a H := 
  begin
    unfold list.map, cases H with H H,
    rewrite H, apply or.inl (eq.refl _),
    apply or.inr, apply mem_map_of_mem as a H
  end

lemma mem_product_of_mem_of_mem :
  ∀ {as : list α} {bs : list β} {a : α} {b : β}, 
    a ∈ as → b ∈ bs → (a,b) ∈ list.product as bs 
| [] _ _ _ H _ := by cases H
| _ [] _ _ _ H := by cases H
| (a::as) (b::bs) a' b' Ha Hb := 
  begin
    unfold has_mem.mem at Ha, unfold list.mem at Ha, 
    unfold has_mem.mem at Hb, unfold list.mem at Hb, 
    unfold has_mem.mem, unfold list.product, unfold list.map, 
    unfold append, simp, unfold list.mem,
    cases Ha with Ha Ha, cases Hb with Hb Hb, 
    apply or.inl, simp *, 
    apply or.inr, apply mem_append_of_mem_or_mem,
    apply or.inl, simp *, apply mem_map_of_mem bs b', 
    apply Hb, apply or.inr, apply mem_append_of_mem_or_mem,
    apply or.inr, apply mem_product_of_mem_of_mem,
    apply Ha, apply Hb
  end

lemma map_dist_append {f : α → β} : 
  ∀ (l1 l2 : list α), list.map f (l1 ++ l2) = (list.map f l1) ++ (list.map f l2) := 
begin
  intro l1, induction l1, intro l2, simp *,
  intro l2, rename a_1 l1,
  repeat {unfold append, unfold list.append}, 
  repeat {unfold list.map}, unfold list.append,
  apply congr_arg (list.cons (f a)), apply ih_1
end

def mem_filter_of_pred_and_mem {P : α → Prop} [HD : decidable_pred P] : ∀ (as : list α) (a : α), P a → a ∈ as → a ∈ list.filter P as 
| [] a HP HM := by cases HM 
| (a'::as) a HP HM := 
  begin
    unfold list.filter, unfold ite, 
    unfold has_mem.mem at HM, unfold list.mem at HM,
    cases HM with HM HM, 
    cases (HD a') with HD HD, 
    exfalso, apply HD, rewrite HM at HP, apply HP,
    simp, apply or.inl HM,  
    cases (HD a') with HD HD, simp, 
    apply mem_filter_of_pred_and_mem, apply HP, 
    apply HM, simp, 
    apply or.inr, apply mem_filter_of_pred_and_mem,
    apply HP, apply HM
  end

lemma map_compose (f : α → β) (g : β → γ) : ∀ (as : list α), list.map g (list.map f as) = list.map (λ x, g (f x)) as 
| [] :=eq.refl _
| (a::as) := by simp 

lemma exp_compose (f : α → β) (g : β → γ) (a : α) : (λ x, g (f x)) a = g (f a) := eq.refl _ 

lemma map_eq (f g : α → β)  : ∀ (as : list α) (H : ∀ a, a ∈ as → f a = g a), list.map f as = list.map g as 
| [] _ := eq.refl _
| (a::as) H := 
  begin 
    unfold list.map, rewrite H, rewrite map_eq,
    intros a Ha, apply (H _ (or.inr Ha)),  
    apply (or.inl (eq.refl _))
  end

def dec_not_pred_of_dec_pred (P : α → Prop) [H : decidable_pred P] : decidable_pred (λ x, ¬ P x) := 
begin
  intro a, cases (H a) with H H, 
  apply decidable.is_true H, 
  apply decidable.is_false (not_not_intro H)
end

open tactic

meta def papply pe := to_expr pe >>= apply  

meta def intro_fresh : tactic expr :=
get_unused_name `h none >>= tactic.intro 

meta def intro_refl : tactic unit := 
do t ← target, 
   match t with 
   | `(_ = _) := papply ``(eq.refl _)
   | `(_ → _) := intro_fresh >> intro_refl
   | _ := failed 
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

meta def first_arg (f : α → tactic β) : list α → tactic β 
| [] := failed 
| (a::as) := f a <|> (first_arg as)

meta def papply_trans (pe : pexpr) := 
do papply ``(eq.trans), papply pe

lemma allp_filter (P : α → Prop) [H : decidable_pred P] : ∀ (l : list α) , allp P (list.filter P l) 
| [] := begin intros _ Ha, cases Ha end 
| (x::xs) := 
  begin 
    unfold list.filter, unfold ite, 
    cases (H x) with H1 H1, simp, apply allp_filter, 
    simp, intros a Ha, cases Ha with H2 H3, rewrite H2,
    apply H1, apply allp_filter, apply H3
  end

lemma mem_of_mem_filter {P : α → Prop} {a : α} : 
  ∀ {l : list α} {HD : decidable_pred P}, a ∈ (@list.filter _ P HD l) → a ∈ l  
| [] _ := by {intro H, cases H} 
| (a'::as) HD := 
  begin
    unfold list.filter, unfold ite, 
    cases (HD a') with HD HD, simp, intro HM, 
    apply or.inr, apply mem_of_mem_filter HM,
    simp, intro HM, cases HM with H1 H2, 
    apply or.inl H1, apply or.inr, 
    apply mem_of_mem_filter H2,
  end 

lemma pred_of_mem_filter_pred {P : α → Prop} {a : α} : 
  ∀ {l : list α} {HD : decidable_pred P}, a ∈ (@list.filter _ P HD l) → P a 
| [] HD := by {intro H, cases H} 
| (a'::as) HD := 
  begin
    unfold list.filter, unfold ite, 
    cases (HD a') with HD HD, simp, 
    intro Ha, apply pred_of_mem_filter_pred, apply Ha,
    intro Ha, cases Ha with Ha Ha, rewrite Ha, apply HD,
    apply pred_of_mem_filter_pred, apply Ha
  end 

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