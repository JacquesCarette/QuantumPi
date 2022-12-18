{-# OPTIONS --without-K --exact-split --safe #-}

-- Various definitions around Float that get re-used

module FloatUtils where

open import Data.Float as F using (Float; cos; sin; _÷_; _*_; _+_; -_; _-_)
import Data.Sum as Sum
open Sum using (inj₁; inj₂; _⊎_)
open import Data.Unit using (⊤; tt)

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

