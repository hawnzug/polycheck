-- | Utilities for Template Haskell
{-# LANGUAGE TemplateHaskell #-}
module Test.PolyCheck.TH.TypeExp where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Datatype
import Data.Void (Void)

-- | i-th injection of n-ary sum
eitheri :: Int -> Int -> Q Exp
eitheri n 0 = [| Left |]
eitheri n i = if i == n-1 then go i else [| $(go i) . Left |]
  where
    go 1 = [| Right |]
    go k = [| Right . $(go (k-1)) |]

-- | i-th projection of n-ary tuple
proji :: Int -> Int -> Q Exp
proji n i = do
  x <- newName "x"
  let pats = replicate i WildP <> (VarP x : replicate (n-i-1) WildP)
  pure $ LamE [TupP pats] (VarE x)

mkTupleT :: [Type] -> Type
mkTupleT [] = TupleT 0
mkTupleT [t] = t
mkTupleT ts = foldl AppT (TupleT $ length ts) ts

-- C (proj1 e) (proj2 e) (proj3 e) ...
mkConE :: Name -> Int -> Q Exp -> Q Exp
mkConE c 0 e = conE c
mkConE c 1 e = appE (conE c) e
mkConE c n e = foldl appE (conE c) ((\i -> [| $(proji n i) $e |]) <$> [0..n-1])

-- | Create a normal data constructor
mkConD :: Name -> [Type] -> Con
mkConD name cons = NormalC name ((bang, ) <$> cons)  where
  bang = Bang NoSourceUnpackedness NoSourceStrictness

{-
[s, t, u, v]
==>
Either s (Either t (Either u v))
-}
mkEithersT :: [Type] -> Type
mkEithersT [] = ConT ''Void
mkEithersT ts = foldr1 f ts
  where f a b = AppT (AppT (ConT ''Either) a) b

{-
App (App (App constr a) b) c
==>
(constr, [a, b, c])
-}
flattenApps :: Type -> (Type, [Type])
flattenApps = go []
  where
    go ps (AppT rest p) = go (p:ps) rest
    go ps constr = (constr, ps)

{-
a -> b -> c -> r
==>
([a, b, c], r)
-}
flattenArrows :: Type -> ([Type], Type)
flattenArrows = go where
  go (AppT (AppT ArrowT arg) rest) =
    let (args, ret) = go rest in (arg:args, ret)
  go ret = ([], ret)

destructFnType :: Type -> Q ([Name], [Type], Type)
destructFnType (ForallT tvars _ ty) =
  let names = tvName <$> tvars in
  let (ps, r) = flattenArrows ty in
  pure (names, ps, r)
destructFnType _ = fail "Not supported"
