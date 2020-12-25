
-- 1. Prove that appending Nil is the identity
-- (Note: this is defined in Data.List, but have a go yourself!)
appendNilNeutral : (xs : List a) -> xs ++ [] = xs
appendNilNeutral [] = Refl
appendNilNeutral (x :: xs) = rewrite appendNilNeutral xs in Refl

-- 2. Prove that appending lists is associative.
-- (Note: also defined in Data.List)
appendAssoc : (xs : List a) -> (ys : List a) -> (zs : List a) ->
              xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
appendAssoc [] ys zs = Refl
appendAssoc (x :: xs) ys zs = rewrite appendAssoc xs ys zs in Refl

-- A tree indexed by the (inorder) flattening of its contents
data Tree : List a -> Type where
     Leaf : Tree []
     Node : Tree xs -> (x : a) -> Tree ys -> Tree (xs ++ x :: ys)

-- rotateLemma : {left, rightl, rightr : List a} -> {n, n' : a} -> Tree ((left ++ n :: rightl) ++ n' :: rightr) -> Tree (left ++ n :: (rightl ++ n' :: rightr))
-- rotateLemma n = ?rotateLemma_rhs

-- 3. Fill in rotateLemma. You'll need appendAssoc.
rotateL : Tree xs -> Tree xs
rotateL Leaf = Leaf
rotateL (Node left n Leaf) = Node left n Leaf
rotateL (Node {xs} left n (Node {xs=ys} {ys=zs} rightl n' rightr))
    = rewrite appendAssoc xs (n :: ys) (n' :: zs) in Node (Node left n rightl) n' rightr

-- 4. Complete the definition of rotateR
rotateR : Tree xs -> Tree xs
rotateR Leaf = Leaf
rotateR (Node Leaf n right) = Node Leaf n right
rotateR (Node {ys=zs} (Node {xs} {ys} leftl n leftr) n' right)
    = rewrite sym (appendAssoc xs (n :: ys) (n' :: zs)) in Node leftl n (Node leftr n' right)
