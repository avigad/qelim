import .logic

variables {α β : Type}

inductive fm.dsub : fm α → fm α → Prop 
| andl : ∀ p q, fm.dsub p (p ∧' q)
| andr : ∀ p q, fm.dsub q (p ∧' q)
| orl : ∀ p q, fm.dsub p (p ∨' q)
| orr : ∀ p q, fm.dsub q (p ∨' q)
| not : ∀ p, fm.dsub p (¬' p)
| ex : ∀ p, fm.dsub p (∃' p)

inductive fm.sub : fm α → fm α → Prop 
| dir : ∀ p q, fm.dsub p q → fm.sub p q
| step : ∀ p q r, fm.sub p q → fm.dsub q r → fm.sub p r

lemma sub_and (p q r : fm α) : fm.sub p (q ∧' r) → 
(p = q) ∨ (p = r) ∨ (fm.sub p q) ∨ (fm.sub p r) := 
begin
  intro H, cases H with _ _ H1 _ s _ H2 H3, 
  cases H1, apply or.inl, refl, 
  apply or.inr, apply or.inl, refl, cases H3,  
  apply or.inr, apply or.inr, apply or.inl, assumption,
  apply or.inr, apply or.inr, apply or.inr, assumption
end

lemma sub_or (p q r : fm α) : fm.sub p (q ∨' r) → 
(p = q) ∨ (p = r) ∨ (fm.sub p q) ∨ (fm.sub p r) :=  
begin
  intro H, cases H with _ _ H1 _ s _ H2 H3, 
  cases H1, apply or.inl, refl, 
  apply or.inr, apply or.inl, refl, cases H3,  
  apply or.inr, apply or.inr, apply or.inl, assumption,
  apply or.inr, apply or.inr, apply or.inr, assumption
end

lemma sub_not (p q : fm α) : 
  fm.sub p (¬' q) → (p = q) ∨ (fm.sub p q) := 
begin
  intro H, cases H with _ _ H1 _ r _ H2 H3, 
  cases H1, apply or.inl, refl, 
  cases H3, apply or.inr, apply H2
end

lemma sub_ex (p q : fm α) : 
  fm.sub p (∃' q) → (p = q) ∨ (fm.sub p q) :=  
begin
  intro H, cases H with _ _ H1 _ r _ H2 H3, 
  cases H1, apply or.inl, refl, 
  cases H3, apply or.inr, apply H2
end

lemma srec_on_aux {C : fm α → Prop} (H : ∀ p, (∀ (q : fm α), fm.sub q p → C q) → C p) : 
∀ (p q : fm α), fm.sub q p → C q :=
λ p, fm.rec_on p 
  (begin 
     intros q Hq,
     cases Hq with _ _ H1 x y z _ H2, cases H1, cases H2
   end) 
  (begin 
     intros q Hq,
     cases Hq with _ _ H1 x y z _ H2, cases H1, cases H2
   end) 
  (begin 
     intros a q Hq,
     cases Hq with _ _ H1 x y z _ H2, cases H1, cases H2
   end) 
  (begin
    intros q r Hq Hr s Hs, 
    cases (sub_and _ _ _ Hs) with H1 H2, rewrite H1, 
    apply (H _ Hq), cases H2 with H3 H4, 
    rewrite H3, apply (H _ Hr), cases H4 with H5 H6, 
    apply (Hq _ H5), apply (Hr _ H6)  
   end) 
  (begin
    intros q r Hq Hr s Hs, 
    cases (sub_or _ _ _ Hs) with H1 H2, rewrite H1, 
    apply (H _ Hq), cases H2 with H3 H4, 
    rewrite H3, apply (H _ Hr), cases H4 with H5 H6, 
    apply (Hq _ H5), apply (Hr _ H6)  
   end) 
   (begin
     intros q Hq r Hr, cases (sub_not _ _ Hr) with H1 H2,  
     rewrite H1, apply (H _ Hq), apply (Hq _ H2)
    end) 
   (begin
     intros q Hq r Hr, cases (sub_ex _ _ Hr) with H1 H2,  
     rewrite H1, apply (H _ Hq), apply (Hq _ H2)
    end) 

lemma srec_on {C : fm α → Prop} : 
  (∀ p, (∀ (q : fm α), fm.sub q p → C q) → C p) → ∀ (p : fm α), C p := 
by {intros H p, apply H, apply srec_on_aux, apply H}