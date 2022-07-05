{-# OPTIONS --without-K --exact-split --safe #-}

-- Show that Unitary(?) has states and effects

module Instances where

open import PiSyntax using (U)
import PiZ
import PiH
open import PiBij using (generalize)
open import Unitary
open import ArrowsOverPair
open import GenericList
open import StatesAndEffects

-- This "Forward" interpreter is in 𝒰 space, which is common to PiZ and PiH
Fwd : U → U → Set
Fwd t₁ t₂ = 𝒰 t₁ → 𝒰 t₂

FC : Categorical Fwd
FC = record
  { idr = λ x → x
  ; comp = λ f g h x → g (f h) x
  }

evalTL₁ : ∀ {t₁ t₂ : U} → TList t₁ t₂ → Fwd t₁ t₂
evalTL₁ tl = evalTL FC (generalize PiZ.PiZ) (generalize PiH.PiH) tl

{-
Unitary-hasEffects : Interpreter Fwd
Unitary-hasEffects (lift nil) = Categorical.idr FC
Unitary-hasEffects (lift (cons₁ x x₁)) = {!evalTL₁ (cons₁ x x₁)!}
Unitary-hasEffects (lift (cons₂ x x₁)) = {!!}
-}
