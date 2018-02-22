import .atom .ldq

variables {α β : Type}

open tactic atomeq

def lift_eq_qe (β : Type) [atomeq α β] (qe : list α → fm α) (as : list α) : fm α := 
  let ntas := @list.filter _ (λ (a : α), ¬ atomeq.trivial β a) 
    begin
      apply dec_not_pred_of_dec_pred (trivial β),  
      apply atomeq.dec_triv
    end as in 
  match @list.first _ (solv0 β) 
        begin apply atomeq.dec_solv0 end ntas with 
  | none := qe ntas 
  | some (eq,rest) := 
    list_conj  (list.map (λ (a : α), A' (subst0 β eq a)) rest)
  end

lemma ldqe_prsv [atomeq α β] (qe : list α → fm α) 
  (H : ∀ (as : list α), (∀ (a : α), a ∈ as → atom.dep0 β a ∧ ¬ solv0 β a) → is_dnf_qe β qe as) : 
  ∀ (as : list α), (∀ (a : α), a ∈ as → atom.dep0 β a) → is_dnf_qe β (lift_eq_qe β qe) as := 
begin
  intros as Has, unfold is_dnf_qe, intros bs, 
  unfold lift_eq_qe, simp, 
  cases (@cases_first _ (solv0 β) (dec_solv0 _ β) 
    (@list.filter _ (λ (a : α), ¬trivial β a) 
      (begin apply dec_not_pred_of_dec_pred (trivial β),  
      apply atomeq.dec_triv end) as)) with HC HC,
  rewrite HC^.elim_left, 
  unfold lift_eq_qe, unfold is_dnf_qe at H,
  apply eq.trans, apply H, intros a Ha, 
  apply and.intro, apply Has, apply mem_of_mem_filter Ha,
  apply HC^.elim_right, apply Ha, 
  apply propext, apply ex_iff_ex, intro b, 
  apply iff.intro, intros HL a Ha, 
  cases (dec_triv α β a) with HT HT, apply HL,
  apply mem_filter_of_pred_and_mem, apply HT, apply Ha,
  apply true_triv, apply HT, 
  intros HR a Ha, apply HR, apply mem_of_mem_filter,
  apply Ha, 
  cases HC with eqn HC, cases HC with as' HC, 
  cases HC with H1 H2, cases H2 with H2 H3, 
  rewrite H1, unfold lift_eq_qe,
  rewrite exp_I_list_conj, rewrite map_compose, 
  
  apply propext, apply iff.intro, 
  intro HL, 
  existsi (list.nth_dft (atom.inh α β) bs ((@atomeq.dest_solv0 α β _ eqn H2)-1)),
  intros a Ha, 
  cases (dec_triv α β a) with HT HT, 
  cases (atom.dec_eq α β a eqn) with HE HE,
  apply (atomeq.subst_prsv H2)^.elim_left,
  apply HL, apply mem_map_of_mem,
  have HM : a ∈ (eqn::as'), apply (H3 a)^.elim_left,
  apply mem_filter_of_pred_and_mem, apply HT,
  apply Ha, cases HM with HM HM, 
  apply absurd HM HE, apply HM,
  rewrite HE,  
  apply (atomeq.subst_prsv H2)^.elim_left,
  apply atomeq.true_subst, apply H2,
  apply true_triv, apply HT,
  intros HR p Hp, 
  cases (exp_mem_map Hp) with a Ha,
  cases Ha with Ha Ha', rewrite Ha', 
  clear Hp, clear Ha', clear p, 
  apply (atomeq.subst_prsv H2)^.elim_right,
  cases HR with b Hb,
  have Hbe := atomeq.solv0_eq H2 (Hb eqn _),
  have H4 := (H3 a)^.elim_right _,
  rewrite (nth_dft_pred _) at Hbe,
  rewrite Hbe, apply Hb, 
  apply mem_of_mem_filter H4, 
  apply dest_pos, 
  have H5 := (H3 eqn)^.elim_right _,
  apply pred_of_mem_filter_pred H5, 
  apply or.inl, refl, apply or.inr Ha,
  have H5 := (H3 eqn)^.elim_right _,
  apply mem_of_mem_filter H5, apply or.inl, refl
end

#check @nth_dft_pred

#exit 
  of_mem_of_mem :
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