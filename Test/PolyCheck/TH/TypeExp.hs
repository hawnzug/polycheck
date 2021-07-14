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

appTuple :: [Type] -> Type
appTuple [] = TupleT 0
appTuple [t] = t
appTuple ts = foldl AppT (TupleT $ length ts) ts

-- C (proj1 e) (proj2 e) (proj3 e) ...
appCon :: Name -> Int -> Q Exp -> Q Exp
appCon c 0 e = conE c
appCon c 1 e = appE (conE c) e
appCon c n e = foldl appE (conE c) ((\i -> [| $(proji n i) $e |]) <$> [0..n-1])

destructPolyFn :: Type -> Q ([Name], Type, [Type], Type)
destructPolyFn (ForallT tvars _ ty) =
  let names = tvName <$> tvars in
  let (ps, r) = go ty in
  pure (names, ty, ps, r)
  where
    go (AppT (AppT ArrowT t) rest) =
      let (ts, r) = go rest in (t:ts, r)
    go r = ([], r)
destructPolyFn _ = fail "Not supported"

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
[s, t, u, v]
==>
Either s (Either t (Either u v))
-}
appEithers :: [Type] -> Type
appEithers [] = ConT ''Void
appEithers ts = foldr1 f ts
  where f a b = AppT (AppT (ConT ''Either) a) b

{-
a -> b -> c -> r
==>
([a, b, c], r)
-}
flattenArrows :: Type -> ([Type], Type)
flattenArrows = go [] where
  go args (AppT (AppT ArrowT arg) rest) = go (arg:args) rest
  go args t = (args, t)

-- | Create a normal data constructor
makeCon :: Name -> [Type] -> Con
makeCon name cons = NormalC name ((bang, ) <$> cons)  where
  bang = Bang NoSourceUnpackedness NoSourceStrictness
