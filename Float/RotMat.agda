{-# OPTIONS --without-K --exact-split --safe #-}

-- Explicit Rotation Matrix to be used by the main unitary model

module Float.RotMat where

open import Data.Float using (Float; _*_; _+_; -_; _-_)
open import Data.Sum as Sum using (inj₁; inj₂; _⊎_)
open import Data.Unit using (⊤; tt)

open import LinearAlgebraSig using (LASig)
open import AbstractRotation using (RotMat)
open import Float.LASig
open import FloatUtils using (cπ/8; sπ/8)

open LASig FloatVec using (aut)

Rω : aut (⊤ ⊎ ⊤)
Rω f = Sum.[ (λ _ → cπ/8 * f (inj₁ tt) - sπ/8 * f (inj₂ tt)) ,
             (λ _ → sπ/8 * f (inj₁ tt) + cπ/8 * f (inj₂ tt)) ]

Rω⁻¹ : aut (⊤ ⊎ ⊤)
Rω⁻¹ f = Sum.[ (λ _ →    cπ/8 * f (inj₁ tt)  + sπ/8 * f (inj₂ tt)) ,
               (λ _ → - (sπ/8 * f (inj₁ tt)) + cπ/8 * f (inj₂ tt)) ]

Rot : RotMat FloatVec
Rot = record { Rω = Rω ; Rω⁻¹ = Rω⁻¹ }
