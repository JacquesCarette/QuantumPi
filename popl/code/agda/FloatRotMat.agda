{-# OPTIONS --without-K --exact-split --safe #-}

-- Explicit Rotation Matrix to be used by the main unitary model

module FloatRotMat where

open import Data.Float using (Float; _*_; _+_; -_; _-_)
open import Data.Sum as Sum using (inj₁; inj₂; _⊎_)
open import Data.Unit using (⊤; tt)

open import LinearAlgebraSig using (LASig)
open import FloatLA
open import FloatUtils using (cπ/8; sπ/8)

open LASig FloatLA using (linop)

Rω : linop (⊤ ⊎ ⊤)
Rω f = Sum.[ (λ _ → cπ/8 * f (inj₁ tt) - sπ/8 * f (inj₂ tt)) ,
             (λ _ → sπ/8 * f (inj₁ tt) + cπ/8 * f (inj₂ tt)) ]

Rω⁻¹ : linop (⊤ ⊎ ⊤)
Rω⁻¹ f = Sum.[ (λ _ →    cπ/8 * f (inj₁ tt)  + sπ/8 * f (inj₂ tt)) ,
               (λ _ → - (sπ/8 * f (inj₁ tt)) + cπ/8 * f (inj₂ tt)) ]
