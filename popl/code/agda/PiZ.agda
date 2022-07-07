{-# OPTIONS --without-K --exact-split --safe #-}

module PiZ where

open import Function using (_∘_)

open import PiSyntax using (U; I; O; _+ᵤ_; _×ᵤ_; _⟷₁_; 𝟚; swap₊)
open import PiBij using (generalize)
open import GenericPi using (Fwd; GenericPi; true; false)
open import Unitary using (𝒰)

-----------------------------------------------------------------------
-- Below we start the work that correspoints to the Z interpretation

-- An evaluator for Z can re-use GenericPi directly:
evalZ : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → Fwd t₁ t₂
evalZ {t₁} {t₂} c = generalize GenericPi c

trueZ falseZ : 𝒰 𝟚
trueZ = true
falseZ = false

x : Fwd 𝟚 𝟚
x = evalZ swap₊
