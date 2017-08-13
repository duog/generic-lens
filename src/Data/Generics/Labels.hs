{-# LANGUAGE CPP, TypeFamilies, KindSignatures, MultiParamTypeClasses,
  FunctionalDependencies, TypeApplications, ScopedTypeVariables,
  DataKinds, FlexibleInstances, UndecidableInstances,
  UndecidableSuperClasses #-}
module Data.Generics.Labels where

import Data.Generics.Product
import GHC.OverloadedLabels
import GHC.TypeLits
import GHC.Exts
import Data.Proxy

{-
LabelsOptic is a guess at an encoding that will allow labeledOptic @ x to be
an Iso('), IndexePreservingLens('), IndexPreservingTraversal(') or Prism(').

Currently, If there's an instance (Data.Generics.Product.Internal.HasField x s a)
then labeledOptic (Proxy @x) is a Lens' s a

The dream is that the first satisfied case below applies:

If s has exactly one constructor with exactly one field named x, you get
an Iso', or Iso if the field can change type.

If all of s's constructors have a field named x, you get an
IndexPreservingLens' s a, or IndexPreservingLens s t a b
if the field can change type in all cases.

If one of s's constructros has a field named x, you get an
IndexPreservingTraversal' s a, or IndexPreservingTraversal s t a b
if the field can change type in all cases.

if x is of the form "_1", and s has exactly one constructor, pick
the numbered field, for a IndexPreservingLens(').

if x is of the form "_Con" then you get a Prism' or Prism.
If we solve https://ghc.haskell.org/trac/ghc/ticket/11671 then we
can drop the underscore.
-}

class LabelsOptic (x :: Symbol) s t a b
  | s x -> a, t x -> b where
  type Pc x s :: (* -> * -> *) -> Constraint
  type Qc x s :: (* -> * -> *) -> Constraint
  type Fc x s :: (* -> *) -> Constraint
  labeledOptic :: forall proxy p q f. (Pc x s p, Qc x s q, Fc x s f)
    => proxy x
    -> p a (f b) -> q s (f t)

instance (HasField x a s) =>
  LabelsOptic (x :: Symbol) s s a a where
  type Pc x s = ((~) (->))
  type Qc x s = ((~) (->))
  type Fc x s = Functor
  labeledOptic = const $ field @ x

-- I don't know if this is required? I needed it for an earlier iteration,
class (LabelsOptic x s t a b, Pc x s p, Qc x s q, Fc x s f) =>
  IsLabelOptic x p q f s t a b | x s -> a, x t -> b

instance (LabelsOptic x s t a b, Pc x s p, Qc x s q, Fc x s f) =>
  IsLabelOptic x p q f s t a b

instance (IsLabelOptic x p q f s t a b) =>
  IsLabel x (p a (f b) -> q s (f t)) where
-- haven't tested this CPP, but it's at least nearly right
#if __GLASGOW_HASKELL__ >= 802
  fromLabel = labeledOptic (Proxy @ x)
#else
  fromLabel _ = labeledOptic (Proxy @ x)
#endif
