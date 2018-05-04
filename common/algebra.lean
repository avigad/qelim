lemma mul_comm_assoc {α : Type} [comm_semigroup α] : 
  ∀ a b c : α, a * (b * c) = b * (a * c) := 
begin
  intros a b c,
  rewrite mul_comm b c,
  rewrite (eq.symm (mul_assoc a c b)),
  rewrite mul_comm _ b
end

lemma mul_add_mul_add {α : Type} [ring α] (x c d t : α) : 
  (x * c) + (x * d + t) = x * (c + d) + t := 
begin
  rewrite (eq.symm (add_assoc _ _ _)),
  rewrite mul_add
end