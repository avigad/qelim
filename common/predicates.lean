import .atom

variables {α β : Type}

def qfree_res_of_nqfree_arg (qe : fm α → fm α) := 
∀ (p : fm α), nqfree p → qfree (qe p)

def qfree_of_fnormal_of_nqfree (β) [atom_type α β] (qe : fm α → fm α) := 
∀ (p : fm α), nqfree p → fnormal β p → qfree (qe p)

def interp_prsv_ex (β) [atom_type α β] (qe : fm α → fm α) (p) := 
∀ (bs : list β), I (qe p) bs = ∃ b, (I p (b::bs))

def interp_prsv (β) [atom_type α β] (qe : fm α → fm α) (p) := 
∀ (bs : list β), I (qe p) bs = I p bs

def preserves (f : α → α) (r : α → Prop) : Prop := 
∀ a, r a → r (f a)