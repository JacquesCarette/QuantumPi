{-# OPTIONS --without-K --exact-split --safe #-}

module PiZ where

open import Pi.Types using (U; 𝟚)
open import Pi.Language using (_⟷_)
open import Pi.SyntaxToTagless using (generalize)
open import GenericPi using (Fwd; GenericPi)
open import Unitary using (UVec)
open import LinearAlgebraSig using (LASig)

module MkPiZ (L : LASig) where
  open LASig L using (true; false)
  
-----------------------------------------------------------------------
-- Below we start the work that correspoints to the Z interpretation

  -- An evaluator for Z can re-use GenericPi directly:
  evalZ : {t₁ t₂ : U} → t₁ ⟷ t₂ → Fwd L t₁ t₂
  evalZ {t₁} {t₂} c = generalize (GenericPi L) c

  trueZ falseZ : UVec L 𝟚
  trueZ = true
  falseZ = false
