
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- In the term representation, we represent local variables as an index into
-- a list of bound names:
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

-- And, sometimes, it's convenient to manipulate variables separately.
-- Note the erasure properties of the following definition (it is just a Nat
-- at run time)
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

-- 1. Remove all references to the most recently bound variable
dropFirst : List (Var (v :: vs)) -> List (Var vs)
dropFirst [] = []
dropFirst ((MkVar {i = 0} p) :: xs) = dropFirst xs
dropFirst ((MkVar {i = (S k)} (Later p)) :: xs) = (MkVar {i=k} p) :: dropFirst xs

-- 2. Add a reference to a variable in the middle of a scope - we'll need 
-- something like this later.
-- Note: The type here isn't quite right, you'll need to modify it slightly.
insertName : {outer, inner: List Name} -> Var (outer ++ inner) -> Var (outer ++ n :: inner)
insertName {outer=[]} (MkVar p) = MkVar (Later p)
insertName {outer=o :: outer'} (MkVar {i=Z} First) = MkVar First
insertName {outer=o :: outer'} (MkVar {i=S k} (Later p)) =
     let MkVar q = insertName (MkVar p) in
          MkVar (Later q)

