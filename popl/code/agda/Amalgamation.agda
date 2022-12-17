{-# OPTIONS --without-K --exact-split --safe #-}

module Amalgamation where

-- Sequencing of 2 copies of Pi

open import PiSyntax using (U; _×ᵤ_; _⟷_; !⟷; _⊗_; id⟷)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U
    a b c d : U

data TList : U → U → Set where
  nil : TList a a
  cons₁ : t₁ ⟷ t₂ → TList t₂ t₃ → TList t₁ t₃
  cons₂ : t₁ ⟷ t₂ → TList t₂ t₃ → TList t₁ t₃

record Categorical (rep : U → U → Set) : Set where
  field
    idr : {t : U} → rep t t
    comp : {t₁ t₂ t₃ : U} → rep t₁ t₂ → rep t₂ t₃ → rep t₁ t₃

open Categorical

-- We have 2 different evaluators for the same interpretation, we can combine them
evalTL : {rep : U → U → Set} → Categorical rep → (∀ {t₁ t₂} → t₁ ⟷ t₂ → rep t₁ t₂) → (∀ {t₁ t₂} → t₁ ⟷ t₂ → rep t₁ t₂) → TList t₃ t₄ → rep t₃ t₄
evalTL c i₁ i₂ nil         = idr c
evalTL c i₁ i₂ (cons₁ x l) = comp c (i₁ x) (evalTL c i₁ i₂ l)
evalTL c i₁ i₂ (cons₂ x l) = comp c (i₂ x) (evalTL c i₁ i₂ l)
