{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# LANGUAGE DeriveGeneric   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Generics.Record.HasField
-- Copyright   :  (C) 2017 Csongor Kiss
-- License     :  BSD3
-- Maintainer  :  Csongor Kiss <kiss.csongor.kiss@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Derive prisms generically
--
-----------------------------------------------------------------------------

module Data.Generics.Sum.HasConstructor where

import Data.Generics.Internal.Lens

import GHC.TypeLits             (Symbol)
import Data.Kind                (Type)
import GHC.Generics

-- | Records that have a field with a given name.
class HasConstructor (con :: Symbol) a s | s con -> a where
  construct :: Prism' s a

-- | Instances are generated on the fly for all records that have the required
--   field.
instance
  ( Generic s
  , GHasConstructor field (Rep s) a
  ) => HasConstructor field a s where
  construct =  repIso . gconstruct @field

data HList (xs :: [Type]) where
  Nil  :: HList '[]
  (:>) :: x -> HList xs -> HList (x ': xs)

infixr 5 :>

append :: HList xs -> HList ys -> HList (xs ++ ys)
append Nil ys = ys
append (x :> xs) ys = x :> (xs `append` ys)

type family Product (xs :: [Type]) where
  Product '[a]
    = a
  Product '[a, b]
    = (a, b)
  Product '[a, b, c]
    = (a, b, c)
  Product '[a, b, c, d]
    = (a, b, c, d)
  Product '[a, b, c, d, e]
    = (a, b, c, d, e)
  Product '[a, b, c, d, e, f]
    = (a, b, c, d, e, f)
  Product '[a, b, c, d, e, f, g]
    = (a, b, c, d, e, f, g)
  Product '[a, b, c, d, e, f, g, h]
    = (a, b, c, d, e, f, g, h)
  Product '[a, b, c, d, e, f, g, h, j]
    = (a, b, c, d, e, f, g, h, j)
  Product '[a, b, c, d, e, f, g, h, j, k]
    = (a, b, c, d, e, f, g, h, j, k)
  Product '[a, b, c, d, e, f, g, h, j, k, l]
    = (a, b, c, d, e, f, g, h, j, k, l)

tuples :: HList xs -> Product xs
tuples (a :> Nil)
  = a
tuples (a :> b :> Nil)
  = (a, b)
tuples (a :> b :> c :> Nil)
  = (a, b, c)
tuples (a :> b :> c :> d :> Nil)
  = (a, b, c, d)
tuples (a :> b :> c :> d :> e :> Nil)
  = (a, b, c, d, e)
tuples (a :> b :> c :> d :> e :> f :> Nil)
  = (a, b, c, d, e, f)
tuples (a :> b :> c :> d :> e :> f :> g :> Nil)
  = (a, b, c, d, e, f, g)
tuples (a :> b :> c :> d :> e :> f :> g :> h :> Nil)
  = (a, b, c, d, e, f, g, h)
tuples (a :> b :> c :> d :> e :> f :> g :> h :> j :> Nil)
  = (a, b, c, d, e, f, g, h, j)
tuples (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> Nil)
  = (a, b, c, d, e, f, g, h, j, k)
tuples (a :> b :> c :> d :> e :> f :> g :> h :> j :> k :> l :> Nil)
  = (a, b, c, d, e, f, g, h, j, k, l)

class AsList (tup :: *) (xs :: [*]) | tup -> xs, xs -> tup where
  asList :: tup -> HList xs

instance AsList (a, b) '[a, b] where
  asList (a, b)
    = (a :> b :> Nil)

instance AsList (a, b, c) '[a, b, c] where
  asList (a, b, c)
    = (a :> b :> c :> Nil)

instance AsList (a, b, c, d) '[a, b, c, d] where
  asList (a, b, c, d)
    = (a :> b :> c :> d :> Nil)

instance AsList (a, b, c, d, e) '[a, b, c, d, e] where
  asList (a, b, c, d, e)
    = (a :> b :> c :> d :> e :> Nil)

instance AsList (a, b, c, d, e, f) '[a, b, c, d, e, f] where
  asList (a, b, c, d, e, f)
    = (a :> b :> c :> d :> e :> f :> Nil)

instance AsList (a, b, c, d, e, f, g) '[a, b, c, d, e, f, g] where
  asList (a, b, c, d, e, f, g)
    = (a :> b :> c :> d :> e :> f :> g :> Nil)

instance AsList (a, b, c, d, e, f, g, h) '[a, b, c, d, e, f, g, h] where
  asList (a, b, c, d, e, f, g, h)
    = (a :> b :> c :> d :> e :> f :> g :> h :> Nil)

data TestProd = Test Int String Char Int
              deriving (Show, Generic)

-- roundtrips
-- to (gto (gfrom (from $ Test 5 "asd" 'c' 4))) :: TestProd

type family ((xs :: [k]) ++ (ys :: [k])) :: [k] where
    '[] ++ ys = ys
    (x ': xs) ++ ys = x ': (xs ++ ys)

class GHasConstructor (con :: Symbol) (s :: Type -> Type) a | con s -> a where
  gconstruct :: Prism' (s x) a

instance GHasConstructor con s a => GHasConstructor con (M1 D c s) a where
  gconstruct = mIso . gconstruct @con

instance (GCollect s xs, AsList a xs, Product xs ~ a) => GHasConstructor con (M1 C ('MetaCons con f n) s) a where
  gconstruct = prism (M1 . gto . asList) (Right . tuples @xs . gfrom . unM1)

instance (GHasConstructor con s a) => GHasConstructor con (M1 S m s) a where
  gconstruct = mIso . gconstruct @con

class GHasConstructorSum (con :: Symbol) l r a (p :: Bool) | con l r p -> a where
  gconstructSum :: Prism' ((l :+: r) x) a

instance GHasConstructor con l a => GHasConstructorSum con l r a 'True where
  gconstructSum = left . gconstruct @con

instance GHasConstructor con r a => GHasConstructorSum con l r a 'False where
  gconstructSum = right . gconstruct @con

instance GHasConstructorSum con l r a (ContainsC con l) => GHasConstructor con (l :+: r) a where
  gconstruct = gconstructSum @con @l @r @a @(ContainsC con l)

data T2
  = T3 Int String
  | T2 Int String
  | T8 Int Char String Int Int
  deriving (Show, Generic)

-- to (gconstruct @"T2" # (5, "asd")) :: T2
-- Generics.to (gconstruct @"T8" # (5, 'c', "asd" ,4 ,4)) :: T2
-- T8 4 'c' "asd" 4 2 ^? construct @"T8" . _3

class Partition xs ys zs | xs ys -> zs, xs zs -> ys where
  partition :: HList zs -> (HList xs, HList ys)

instance Partition '[] xs xs where
  partition xs = (Nil, xs)

instance Partition xs ys zs => Partition (x ': xs) ys (x ': zs) where
  partition (x :> xs) = (x :> xs', ys')
    where (xs', ys') = partition xs

class GCollect (s :: Type -> Type) (xs :: [Type]) | s -> xs where
  --gcollect :: Iso' (s x) (HList xs)
  gfrom :: s x -> HList xs
  gto :: HList xs -> s x

instance (GCollect a as, GCollect b bs, xs ~ (as ++ bs), Partition as bs xs) => GCollect (a :*: b) xs where
  --gcollect (a :*: b) = gcollect a `append` gcollect b
  gfrom (a :*: b) = gfrom a `append` gfrom b
  gto xs = (gto l :*: gto r)
    where (l, r) = partition @as @bs xs

instance GCollect (K1 R a) '[a] where
  gfrom (K1 x) = x :> Nil
  gto (x :> Nil) = K1 x

instance GCollect s a => GCollect (M1 S c s) a where
  gfrom (M1 x) = gfrom x
  gto x = M1 $ gto x

instance GCollect s a => GCollect (M1 D c s) a where
  gfrom (M1 x) = gfrom x
  gto x = M1 $ gto x

instance GCollect s a => GCollect (M1 C c s) a where
  gfrom (M1 x) = gfrom x
  gto x = M1 $ gto x


--------------------------------------------------------------------------------

type family ContainsC (field :: Symbol) f :: Bool where
  ContainsC cname (C1 ('MetaCons cname _ _) _)
    = 'True
  ContainsC cname (f :*: g)
    = ContainsC cname f || ContainsC cname g
  ContainsC cname (f :+: g)
    = ContainsC cname f || ContainsC cname g
  ContainsC cname (S1 _ _)
    = 'False
  ContainsC cname (C1 m f)
    = ContainsC cname f
  ContainsC cname (D1 m f)
    = ContainsC cname f
  ContainsC cname (Rec0 _)
    = 'False
  ContainsC cname U1
    = 'False
  ContainsC cname V1
    = 'False

-- | Type-level alternative
type family (a :: Bool) || (b :: Bool) :: Bool where
  'True  || _  = 'True
  'False || b = b

