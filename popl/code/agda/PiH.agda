{-# OPTIONS --without-K --exact-split --safe #-}

module PiH where

open import Function using (_∘_)

open import Pi.Types using (U; 𝟚)
open import Pi.Language using (_⟷_)
open import PiTagless using (generalize)
open import GenericPi using (Fwd; GenericPi; true; false)
open import Unitary using (UVec; R; R⁻¹)

-----------------------------------------------------------------------
-- An evaluator for H can re-use GenericPi and conjugate before/after:
evalH : {t₁ t₂ : U} → t₁ ⟷ t₂ → Fwd t₁ t₂
evalH {t₁} {t₂} c = R⁻¹ t₂ ∘ generalize GenericPi c ∘ R t₁

trueH falseH  : UVec 𝟚
trueH =  R⁻¹ 𝟚 true
falseH = R⁻¹ 𝟚 false

