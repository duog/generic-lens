{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Generics.Sum.Subtype
  ( AsSubtype (..)

  , GAsSubtype (..)
  ) where

--import Data.Generics.Internal.HList
import Data.Generics.Internal.Lens
import Data.Generics.Sum.Typed

import Data.Kind
import GHC.Generics

class AsSubtype sub sup where
  _Sub :: Prism' sup sub
  _Sub = prism injectSub projectSub

  injectSub  :: sub -> sup
  projectSub :: sup -> Either sup sub

instance
  ( Generic sub
  , Generic sup
  , GAsSubtype (Rep sub) (Rep sup)
  ) => AsSubtype sub sup where

  injectSub  = to . ginjectSub . from
  projectSub = either (Left . to) (Right . to) . gprojectSub . from

class GAsSubtype (subf :: Type -> Type) (supf :: Type -> Type) where
  ginjectSub  :: subf x -> supf x
  gprojectSub :: supf x -> Either (supf x) (subf x)

instance
  ( GAsSubtype l supf
  , GAsSubtype r supf
  ) => GAsSubtype (l :+: r) supf where

  ginjectSub x = case x of
    L1 l -> ginjectSub l
    R1 r -> ginjectSub r
  gprojectSub x
    = case gprojectSub x of
        Left  _ -> fmap R1 (gprojectSub x)
        Right y -> Right (L1 y)

{-
instance
  ( GAsType supf a
  , GCollectible subf as
  , ListTuple x as
  ) => GAsSubtype (C1 meta subf) supf where

  ginjectSub
    =
    -}

instance GAsType supf a => GAsSubtype (S1 meta (Rec0 a)) supf where
  ginjectSub
    = ginjectTyped @supf . unK1 . unM1
  gprojectSub
    = fmap (M1 . K1) . gprojectTyped @supf

instance GAsSubtype subf supf => GAsSubtype (C1 meta subf) supf where
  ginjectSub
    = ginjectSub . unM1
  gprojectSub
    = fmap M1 . gprojectSub

instance GAsSubtype subf supf => GAsSubtype (D1 meta subf) supf where
  ginjectSub
    = ginjectSub . unM1
  gprojectSub
    = fmap M1 . gprojectSub
