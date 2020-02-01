{-# LANGUAGE DataKinds, DefaultSignatures, DeriveGeneric, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, PolyKinds, TypeFamilies, TypeOperators  #-}
{-# LANGUAGE UndecidableInstances                                           #-}
module Main where
import Data.Type.Natural ((:*), (:+), Nat (..), One)
import Data.Type.Ordinal
import GHC.Generics

class (Enum a, Enum b) => Iso a b where
 toIso   :: a -> b
 toIso = toEnum . fromEnum
 fromIso :: b -> a
 fromIso = toEnum . fromEnum

data Xpto = Abc | Def | Ghi
          deriving (Read, Show, Eq, Ord, Enum, Generic)

type family SizeG (a :: k) :: Nat
type instance SizeG (M1 D y a) = SizeG a
type instance SizeG (M1 C y a) = SizeG a
type instance SizeG (M1 S y a) = Z
type instance SizeG V1         = Z
type instance SizeG U1         = One
type instance SizeG (a :+: b)  = SizeG a :+ SizeG b
type instance SizeG (a :*: b)  = SizeG a :* SizeG b

type Size a = SizeG (Rep a)

data TTTT = T | TT | TTT
          deriving (Read, Show, Eq, Ord, Enum)

instance (b ~ Size Xpto) => Iso Xpto (Ordinal b)
-- instance Iso Xpto TTTT
