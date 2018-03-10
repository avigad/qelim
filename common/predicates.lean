import .atom

variables {α β : Type}

def qfree_prsv (qe : fm α → fm α) := 
∀ (p : fm α), nqfree p → qfree (qe p)

def normal_prsv (β) [atom_type α β] (qe : fm α → fm α) := 
∀ (p : fm α), nqfree p → fnormal β p → qfree (qe p)

def interp_prsv_ex (β) [atom_type α β] (qe : fm α → fm α) (p) := 
∀ (bs : list β), I (qe p) bs = ∃ b, (I p (b::bs))

def interp_prsv (β) [atom_type α β] (qe : fm α → fm α) (p) := 
∀ (bs : list β), I (qe p) bs = I p bs

inductive down : fm α → fm α → Prop 
| andl : ∀ p q, down (p ∧' q) p
| andr : ∀ p q, down (p ∧' q) q
| orl  : ∀ p q, down (p ∨' q) p
| orr  : ∀ p q, down (p ∨' q) q
| not  : ∀ p, down (¬' p) p
| ex   : ∀ p, down (∃' p) p

def down_closed (r : fm α → Prop) : Prop := 
∀ (p q : fm α), down p q → r p → r q

def closed (f : α → α) (r : α → Prop) : Prop := 
∀ a, r a → r (f a)