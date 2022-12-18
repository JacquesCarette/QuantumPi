{-# OPTIONS --without-K --exact-split --safe #-}

module Amalgamation where

-- Sequencing of 2 copies of Pi

open import PiSyntax using (U; _⟷_)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ : U

data TList : U → U → Set where
  nil : TList t t
  cons₁ : t₁ ⟷ t₂ → TList t₂ t₃ → TList t₁ t₃
  cons₂ : t₁ ⟷ t₂ → TList t₂ t₃ → TList t₁ t₃

record Categorical (rep : U → U → Set) : Set where
  field
    id : {t : U} → rep t t
    _∘_ : {t₁ t₂ t₃ : U} → rep t₁ t₂ → rep t₂ t₃ → rep t₁ t₃

-- We have 2 different evaluators for the same interpretation, we can combine them
module _ {rep : U → U → Set} (c : Categorical rep) where
  open Categorical c
  
  evalTL : (i₁ i₂ : ∀ {t₁ t₂} → t₁ ⟷ t₂ → rep t₁ t₂) → TList t₃ t₄ → rep t₃ t₄
  evalTL i₁ i₂ nil         = id
  evalTL i₁ i₂ (cons₁ x l) = (i₁ x) ∘ (evalTL i₁ i₂ l)
  evalTL i₁ i₂ (cons₂ x l) = (i₂ x) ∘ (evalTL i₁ i₂ l)
