{-# OPTIONS --without-K --exact-split --safe #-}

module PiH where

open import Function using (_∘_)

open import PiSyntax using (U; I; O; _+ᵤ_; _×ᵤ_; _⟷₁_; 𝟚; swap₊)
open import PiBij using (⟦_⟧; generalize)
open import PiZ using (PiZ; trueZ; falseZ)
open import Unitary using (𝒰; R; R⁻¹)

-----------------------------------------------------------------------
-- Below we start the work that correspoints to the H interpretation

H : (t : U) → Set
H = 𝒰

Fwd : U → U → Set
Fwd t₁ t₂ = H t₁ → H t₂

-- An evaluator for H can re-use PiZ and conjugate before/after:
evalH : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → Fwd t₁ t₂
evalH {t₁} {t₂} c = R⁻¹ t₂ ∘ generalize PiZ c ∘ R t₁

trueH falseH  : H 𝟚
trueH =  R⁻¹ 𝟚 trueZ
falseH = R⁻¹ 𝟚 falseZ

notH : H 𝟚 → H 𝟚
notH = evalH swap₊
