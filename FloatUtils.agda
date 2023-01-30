{-# OPTIONS --without-K --exact-split --safe #-}

-- Various definitions around Float that get re-used

module FloatUtils where

open import Data.Float using (Float; cos; sin; _÷_; _≤ᵇ_; _<ᵇ_)
open import Data.Bool using (Bool; _∧_; _∨_)

π : Float
π = 3.1415926535

cπ/8 : Float
cπ/8 = cos (π ÷ 8.0)
sπ/8 : Float
sπ/8 = sin (π ÷ 8.0)

tooSmall : Float → Bool
tooSmall a = ((0.0 ≤ᵇ a) ∧ (a <ᵇ 0.01)) ∨ ((a ≤ᵇ 0.0) ∧ (-0.01 <ᵇ a))
