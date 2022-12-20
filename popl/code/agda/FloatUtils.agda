{-# OPTIONS --without-K --exact-split --safe #-}

-- Various definitions around Float that get re-used

module FloatUtils where

open import Data.Float using (Float; cos; sin; _÷_; _*_; _+_; -_; _-_; _≤ᵇ_; _<ᵇ_)
open import Data.Sum as Sum using (inj₁; inj₂; _⊎_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; _∧_; _∨_)

π : Float
π = 3.1415926535

cπ/8 : Float
cπ/8 = cos (π ÷ 8.0)
sπ/8 : Float
sπ/8 = sin (π ÷ 8.0)

vec : Set → Set
vec t = t → Float

mat : Set → Set
mat t = vec t → vec t

Rω : mat (⊤ ⊎ ⊤)
Rω f = Sum.[ (λ _ → cπ/8 * f (inj₁ tt) - sπ/8 * f (inj₂ tt)) ,
             (λ _ → sπ/8 * f (inj₁ tt) + cπ/8 * f (inj₂ tt)) ]

Rω⁻¹ : mat (⊤ ⊎ ⊤)
Rω⁻¹ f = Sum.[ (λ _ →    cπ/8 * f (inj₁ tt)  + sπ/8 * f (inj₂ tt)) ,
               (λ _ → - (sπ/8 * f (inj₁ tt)) + cπ/8 * f (inj₂ tt)) ]

tooSmall : Float → Bool
tooSmall a = ((0.0 ≤ᵇ a) ∧ (a <ᵇ 0.01)) ∨ ((a ≤ᵇ 0.0) ∧ (-0.01 <ᵇ a))
