lemma add_assoc' {α : Type} [add_semigroup α] :
  ∀ (a b c : α), a + (b + c) = a + b + c :=
begin
  intros a b c, rewrite add_assoc
end

lemma mul_assoc' {α : Type} [comm_semigroup α] :
  ∀ (a b c : α), a * (b * c) = a * b * c :=
begin 
  intros a b c, rewrite mul_assoc 
end

#check add_right_comm
lemma mul_comm_assoc {α : Type} [comm_semigroup α] : 
  ∀ a b c : α, (a * b) * c = (a * c) * b := 
begin
  intros a b c, rewrite mul_assoc, 
  rewrite mul_comm b c, 
  rewrite mul_assoc
end

lemma mul_add_mul_add {α : Type} [ring α] (t c x d : α) : 
  (t + c * x) + (d * x)  = t + ((c + d) * x) := 
begin
  rewrite add_assoc,
  rewrite add_mul
end