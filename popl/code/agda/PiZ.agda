{-# OPTIONS --without-K --exact-split --safe #-}

module PiZ where

open import Pi.Types using (U)
open import PiSyntax using (_⟷_; 𝟚)
open import PiTagless using (generalize)
open import GenericPi using (Fwd; GenericPi; true; false)
open import Unitary using (𝒰)

-----------------------------------------------------------------------
-- Below we start the work that correspoints to the Z interpretation

-- An evaluator for Z can re-use GenericPi directly:
evalZ : {t₁ t₂ : U} → t₁ ⟷ t₂ → Fwd t₁ t₂
evalZ {t₁} {t₂} c = generalize GenericPi c

trueZ falseZ : 𝒰 𝟚
trueZ = true
falseZ = false

