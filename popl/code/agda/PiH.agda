{-# OPTIONS --without-K --exact-split --safe #-}

module PiH where

open import Function using (_∘_)

open import Pi.Types using (U; 𝟚)
open import Pi.Language using (_⟷_)
open import PiTagless using (generalize)
open import GenericPi using (Fwd; GenericPi)
open import Unitary using (UVec; module Build)
open import LinearAlgebraSig using (LASig)
open import AbstractRotation using (RotMat)

module MkPiH (L : LASig) (RM : RotMat L) where
  open LASig L using (true; false)
  open Build L RM using (R; R⁻¹)
  
  -----------------------------------------------------------------------
  -- An evaluator for H can re-use GenericPi and conjugate before/after:
  evalH : {t₁ t₂ : U} → t₁ ⟷ t₂ → Fwd L t₁ t₂
  evalH {t₁} {t₂} c = R⁻¹ t₂ ∘ generalize (GenericPi L) c ∘ R t₁

  trueH falseH  : UVec L 𝟚
  trueH =  R⁻¹ 𝟚 true
  falseH = R⁻¹ 𝟚 false

