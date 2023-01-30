{-# OPTIONS --without-K --exact-split --safe #-}

-- Signature of the rotation matrix we need

module AbstractRotation where

open import Data.Sum as Sum using (inj₁; inj₂; _⊎_)
open import Data.Unit using (⊤; tt)

open import LinearAlgebraSig using (LASig)

record RotMat (L : LASig) : Set where
  open LASig L using (aut)
  field
    Rω : aut (⊤ ⊎ ⊤)
    Rω⁻¹ : aut (⊤ ⊎ ⊤)
