import Decidable.Equality

-- This is the (simplified) definition of names in Core.TT
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- 1. Write an Eq instance for Name
-- (sorry, it's not derivable yet!)
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x m) (MN y n) = x == y && m == n
  (==) _ _ = False

-- 2. Sometimes, we need to compare names for equality and use a proof that
-- they're equal. So, implement the following 
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) = case decEq x y of
  Yes prf => rewrite prf in Just Refl
  No _ => Nothing
nameEq (UN x) (MN y z) = Nothing
nameEq (MN x z) (UN y) = Nothing
nameEq (MN x z) (MN y w) = case (decEq x y, decEq z w) of
  (Yes prf1, Yes prf2) => rewrite prf1 in rewrite prf2 in Just Refl
  _ => Nothing

unEqIsEq : {0 x : String} -> {0 y : String} -> (1 p : UN x = UN y) -> x = y
unEqIsEq {x=x} {y=x} Refl = Refl

mnEqIsEq: {0 x : String} -> {0 m : Int} -> {0 y : String} -> {0 n : Int} -> (1 p : MN x m = MN y n) -> (x=y, m=n)
mnEqIsEq {x=x} {y=x} {m=m} {n=m} Refl = (Refl,Refl)

unNeqMn : {0 x : String} -> {0 y : String} -> {0 n : Int} -> (1 p : UN x = MN y n) -> Void
unNeqMn Refl impossible

mnNeqUn : {0 x : String} -> {0 y : String} -> {0 n : Int} -> (1 p : MN x n = UN y) -> Void
mnNeqUn Refl impossible

-- 3. (Optional, since we don't need this in Idris 2, but it's a good
-- exercise to see if you can do it!) Implement decidable equality, so you
-- also have a proof if names are *not* equal.
DecEq Name where
  decEq (UN x) (UN y) = case decEq x y of
    Yes prf => Yes (cong UN prf)
    No prf => No \q => prf (unEqIsEq q)
  decEq (UN x) (MN y z) = No \p => unNeqMn p
  decEq (MN x z) (UN y) = No \p => mnNeqUn p
  decEq (MN x m) (MN y n) = case (decEq x y, decEq m n) of
    (Yes p, Yes q) => rewrite p in rewrite q in Yes Refl
    (_, No p) => No \q => p (snd (mnEqIsEq q))
    (No p, _) => No \q => p (fst (mnEqIsEq q))