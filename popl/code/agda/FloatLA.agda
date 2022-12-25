{-# OPTIONS --without-K --exact-split --safe #-}

-- Various definitions around Float that get re-used

module FloatLA where

open import Data.Float using (Float)

open import LinearAlgebraSig

FloatLA : LASig
FloatLA = record { vec = λ t → t → Float ; mat = λ t → t → t → Float }
