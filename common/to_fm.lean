import .logic

open tactic

-- def varstr (n : nat) := "x" ++ to_string n 11

variables {α : Type}

#check expr

meta def to_fm (α β : Type) (to_atom : nat → expr → tactic (α × list β)) : 
  nat → expr → tactic (fm α × list β) :=
let to_fm_bin (n) (c : fm α → fm α → fm α) (e1) (e2) := 
  do (p,bs1) ← to_fm n e1, 
     (q,bs2) ← to_fm (n + list.length bs1) e2, 
     return ((c p q), bs1++bs2) in
λ n e, 
  match e with 
  | `(true) := return (⊤',[]) 
  | `(false) := return (⊥',[]) 
  | `(¬ %%pe) := do (p,bs) ← to_fm n pe, return (¬' p, bs)
  | `(%%pe ∧ %%qe) := to_fm_bin n fm.and pe qe
  | `(%%pe ∨ %%qe) := to_fm_bin n fm.or  pe qe
  | `(Exists %%e) :=
    match e with 
    | (expr.lam _ _ d pe) := 
      do (p,bs) ← to_fm (n+1) pe, 
         return (∃' p, bs)
    | _ := failed
    end
  | e := do (a,bs) ← to_atom n e, 
            return (A' a, bs)
  end

#exit
meta def to_fm_rec : expr → tactic (fm α) :=
let to_fm_rec_bin (c : fm α → fm α → fm α) (e1) (e2) := 
  do φ ← to_fm_rec e1, ψ ← to_fm_rec e2, return $ c φ ψ in
λ e, 
  match e with 
  | `(%%e1 ∧ %%e2) := to_fm_rec_bin fm.and e1 e2
  | `(%%e1 ∨ %%e2) := to_fm_rec_bin fm.or  e1 e2
  -- | `(%%e1 ↔ %%e2) := to_fm_rec_bin fm.iff n e1 e2
  | `(Exists %%e2) :=
    let xs := varstr n in 
    do e' ← to_fm_rec (n+1) e2, 
       return $ fm.ex xs $ inst_dbv_frm xs e' 
  -- | (expr.pi _ _ e1 e2) :=
    -- monad.cond (is_prop e1) 
      -- (to_fm_rec_bin formula.Imp n e1 e2)
      -- (let xs := varstr n in 
       -- do e' ← to_fm_rec (n+1) e2, 
          -- return $ formula.Forall xs $ inst_dbv_frm xs e') 
  | _ := failed
  end

meta def to_fm (e) := to_fm_rec 0 e 


-- example : forall (x : nat), exists (y : nat), x = 2 * y ∨ x = 2 * y + 1 := sorry 