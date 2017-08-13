{-# LANGUAGE OverloadedLabels, DeriveGeneric #-}
module FieldSpec where

import Data.Generics.Internal.Lens
import Data.Generics.Labels()
import GHC.Generics
import Test.Hspec
data G c = G
  { a :: Int
  , b :: c
  } deriving Generic


foo :: G c -> Int
foo = (^. #a)

bar :: Traversal' [G c] c
bar = traverse . #b

blens :: Lens' (G c) c
blens = #b

blens' :: Lens' (G Double) Double
blens' = #b

spec :: Spec
spec = return ()
