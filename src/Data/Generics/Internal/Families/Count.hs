{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Generics.Internal.Families.Count
  ( CountTotalType
  , CountPartialType
  , Count (..)
  ) where

import GHC.Generics
import GHC.TypeLits
import Data.Type.Bool (If)

import Data.Generics.Internal.HList

type family CountTotalType t f :: Count where
  CountTotalType t (S1 _ (Rec0 t))
    = 'One
  CountTotalType t (l :*: r)
    = CountTotalType t l <|> CountTotalType t r
  CountTotalType t (l :+: r)
    = CountTotalType t l <&> CountTotalType t r
  CountTotalType t (S1 _ _)
    = 'None
  CountTotalType t (C1 _ f)
    = CountTotalType t f
  CountTotalType t (D1 _ f)
    = CountTotalType t f
  CountTotalType t (Rec0 _)
    = 'None
  CountTotalType t U1
    = 'None
  CountTotalType t V1
    = 'None
  CountTotalType t f
    = TypeError
        (     'ShowType f
        ':<>: 'Text " is not a valid GHC.Generics representation type"
        )

type family CountPartialType t f :: Count where
  CountPartialType t (l :+: r)
    = CountPartialType t l <|> CountPartialType t r
  CountPartialType t (C1 m f)
    = If (Equals t (ListToTuple (GCollect f))) 'One 'None
  CountPartialType t (D1 _ f)
    = CountPartialType t f

type family Equals a b where
  Equals a a = 'True
  Equals _ _ = 'False

data Count
  = None
  | One
  | Multiple

type family (a :: Count) <|> (b :: Count) :: Count where
  'None <|> b     = b
  a     <|> 'None = a
  a     <|> b     = 'Multiple

type family (a :: Count) <&> (b :: Count) :: Count where
  a <&> a = a
  _ <&> _ = 'Multiple
