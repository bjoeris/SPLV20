module Core.TT

import Data.List
import Decidable.Equality

-- In Idris2, this is defined in Core.Name
public export
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq _ _ = Nothing

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = i == j && x == y
  (==) _ _ = False

nameTag : Name -> Int
nameTag (UN _) = 0
nameTag (MN _ _) = 1

export
Ord Name where
  compare (UN x) (UN y) = compare x y
  compare (MN x i) (MN y j)
      = case compare x y of
             EQ => compare i j
             t => t
  compare x y = compare (nameTag x) (nameTag y)

public export
data NameType : Type where
     Func : NameType
     Bound : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon : (tag : Int) -> (arity : Nat) -> NameType

export
Show NameType where
  show Func = "Func"
  show (DataCon t a) = "DataCon " ++ show (t, a)
  show (TyCon t a) = "TyCon " ++ show (t, a)
  show Bound = "Bound"

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
dropVar : (ns : List Name) -> {idx : Nat} ->
          (0 p : IsVar name idx ns) -> List Name
dropVar (n :: ns) {idx = 0} p = ns
dropVar (n :: ns) {idx = (S k)} (Later p) = n :: (dropVar ns {idx=k} p)

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

public export
data PiInfo : Type where
     Implicit : PiInfo
     Explicit : PiInfo

public export
data Binder : Type -> Type where
     Lam : PiInfo -> ty -> Binder ty
     Pi : PiInfo -> ty -> Binder ty

     PVar : ty -> Binder ty -- pattern bound variables ...
     PVTy : ty -> Binder ty -- ... and their type

export
Functor Binder where
  map func (Lam x ty) = Lam x (func ty)
  map func (Pi x ty) = Pi x (func ty)
  map func (PVar ty) = PVar (func ty)
  map func (PVTy ty) = PVTy (func ty)

export
Foldable Binder where
  foldr f init (Lam i ty) = f ty init
  foldr f init (Pi i ty) = f ty init
  foldr f init (PVar ty) = f ty init
  foldr f init (PVTy ty) = f ty init
  foldl f init (Lam i ty) = f init ty
  foldl f init (Pi i ty) = f init ty
  foldl f init (PVar ty) = f init ty
  foldl f init (PVTy ty) = f init ty

export
Traversable Binder where
  traverse f (Lam i ty) = Lam i <$> f ty
  traverse f (Pi i ty) = Pi i <$> f ty
  traverse f (PVar ty) = PVar <$> f ty
  traverse f (PVTy ty) = PVTy <$> f ty

public export
data Term : List Name -> Type where
     Local : (idx : Nat) -> -- de Bruijn index
             (0 p : IsVar name idx vars) -> -- proof that index is valid
             Term vars
     Ref : NameType -> Name -> Term vars -- a reference to a global name
     Meta : Name -> List (Term vars) -> Term vars
     Bind : (x : Name) -> -- any binder, e.g. lambda or pi
            Binder (Term vars) ->
            (scope : Term (x :: vars)) -> -- one more name in scope
            Term vars
     App : Term vars -> Term vars -> Term vars -- function application
     TType : Term vars
     Erased : Term vars

-- Term manipulation

weakenVar : {outer : _} ->
            Var (outer ++ vars) ->
            Var (outer ++ (x :: vars))
weakenVar (MkVar p) {outer = []} = MkVar (Later p)
weakenVar (MkVar First) {outer = (y::ys)} = MkVar First
weakenVar (MkVar (Later p)) {outer = (y::ys)}
    = let MkVar p' = weakenVar {outer=ys} (MkVar p) in
      MkVar (Later p')

weakenHelper : {outer : _} ->
               Term (outer ++ vars) ->
               Term (outer ++ (x :: vars))
weakenHelper (Local idx p)
    = let (MkVar {i=i'} p') = weakenVar (MkVar p) in
      Local i' p'
weakenHelper (Ref y z) = Ref y z
weakenHelper (Meta y ys) = Meta y (map weakenHelper ys)
weakenHelper (Bind y b scope)
    = Bind y (map weakenHelper b) (weakenHelper {outer=y::outer} scope)
weakenHelper (App y z) = App (weakenHelper y) (weakenHelper z)
weakenHelper TType = TType
weakenHelper Erased = Erased

export
weaken : Term vars -> Term (x :: vars)
weaken = weakenHelper {outer=[]}

embedVar : Var (vars) ->
           Var (vars ++ more)
embedVar (MkVar First) = MkVar First
embedVar (MkVar (Later p))
    = let MkVar p' = embedVar (MkVar p) in
      MkVar (Later p')

export
embed : Term vars -> Term (vars ++ more)
embed (Local idx p)
    = let MkVar {i} p' = embedVar (MkVar p) in
      Local i p'
embed (Ref x y) = Ref x y
embed (Meta x xs) = Meta x (map embed xs)
embed (Bind x b scope) = Bind x (map embed b) (embed scope)
embed (App x y) = App (embed x) (embed y)
embed TType = TType
embed Erased = Erased

contractVar : {outer : _} ->
                Var (outer ++ x :: vars) -> 
                Maybe (Var (outer ++ vars))
contractVar (MkVar First) {outer = []} = Nothing
contractVar (MkVar (Later p)) {outer = []} = pure (MkVar p)
contractVar (MkVar First) {outer = (y::ys)} = pure (MkVar First)
contractVar (MkVar (Later p)) {outer = (y::ys)}
    = do MkVar q <- contractVar (MkVar p) {outer=ys}
         pure (MkVar (Later q))

contractHelper : {outer : _} ->
                 Term (outer ++ x :: vars) ->
                 Maybe (Term (outer ++ vars))
contractHelper (Local i p)
    = do MkVar {i=i'} p' <- contractVar (MkVar p)
         pure (Local i' p')
contractHelper (Ref x y) = pure (Ref x y)
contractHelper (Meta x xs)
    = do xs' <- traverse contractHelper xs
         pure (Meta x xs')
contractHelper (Bind n b scope)
    = do b' <- traverse contractHelper b
         scope'<- contractHelper {outer = n :: outer} scope
         pure (Bind n b' scope')
contractHelper (App y z)
    = do y' <- contractHelper y
         z' <- contractHelper z
         pure (App y' z')
contractHelper TType = pure TType
contractHelper Erased = pure Erased

export
contract : Term (x :: vars) -> Maybe (Term vars)
contract = contractHelper {outer=[]}

substHelper : {outer : _} ->
              Term (outer ++ vars) ->
              Term (outer ++ x :: vars) ->
              Term (outer ++ vars)
substHelper v (Local idx p)
    = case contractVar (MkVar p) of
           Nothing => v
           Just (MkVar {i} p') => Local i p'
substHelper v (Ref t n) = Ref t n
substHelper v (Meta n ctx) = Meta n (map (substHelper v) ctx)
substHelper v (Bind n b scope)
    = Bind n (map (substHelper v) b) (substHelper (weaken v) scope {outer=n::outer})
substHelper v (App y z) = App (substHelper v y) (substHelper v z)
substHelper v TType = TType
substHelper v Erased = Erased

export
subst : Term vars -> Term (x :: vars) -> Term vars
subst = substHelper {outer=[]}

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

renameVarsVar : CompatibleVars xs ys ->
                Var xs ->
                Var ys
renameVarsVar CompatPre v = v
renameVarsVar (CompatExt c) (MkVar First) = MkVar First
renameVarsVar (CompatExt c) (MkVar (Later p))
    = let MkVar p' = renameVarsVar c (MkVar p) in
      MkVar (Later p')

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys
renameVars c (Local i p)
    = let MkVar {i=i'} p' = renameVarsVar c (MkVar p) in
      Local i' p'
renameVars c (Ref t n) = Ref t n
renameVars c (Meta n ctx) = Meta n (map (renameVars c) ctx)
renameVars c (Bind n b scope)
    = Bind n (map (renameVars c) b) (renameVars (CompatExt c) scope)
renameVars c (App x y) = App (renameVars c x) (renameVars c y)
renameVars c TType = TType
renameVars c Erased = Erased

--- Show instances

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Name where
  show (UN n) = n
  show (MN n i) = "{" ++ n ++ ":" ++ show i ++ "}"

export
nameAt : {vars : _} ->
         (idx : Nat) -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = n :: ns} Z First = n
nameAt {vars = n :: ns} (S k) (Later p) = nameAt k p

export
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : {vars : _} -> Term vars -> List (Term vars) -> String
      showApp (Local {name} idx p) []
         = show (nameAt idx p) ++ "[" ++ show idx ++ "]"
      showApp (Ref _ n) [] = show n
      showApp (Meta n args) []
          = "?" ++ show n ++ "_" ++ show args
      showApp (Bind x (Lam p ty) sc) []
          = "\\" ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (Pi Explicit ty) sc) []
          = "((" ++ show x ++ " : " ++ show ty ++
            ") -> " ++ show sc ++ ")"
      showApp (Bind x (Pi Implicit ty) sc) []
          = "{" ++ show x ++ " : " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind x (PVar ty) sc) []
          = "pat " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (PVTy ty) sc) []
          = "pty " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (App _ _) [] = "[can't happen]"
      showApp TType [] = "Type"
      showApp Erased [] = "[_]"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map show args))
                     ++ ")"
