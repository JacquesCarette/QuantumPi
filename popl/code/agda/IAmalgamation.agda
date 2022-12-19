{-# OPTIONS --without-K --exact-split --safe #-}

module IAmalgamation where

-- Sequencing of I-many copies of Pi, where I is a type
open import Level using (Level)

open import Pi.Types using (U)
open import Pi.Language using (_⟷_)
open import Amalgamation using (Categorical)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ : U

data TList (I : Set) : U → U → Set where
  nil : TList I t t
  cons : (i : I) → t₁ ⟷ t₂ → TList I t₂ t₃ → TList I t₁ t₃

-- We have 2 different evaluators for the same interpretation, we can combine them
module _ {rep : U → U → Set} (c : Categorical rep) where
  open Categorical c
  
  evalTL : {I : Set} → (∀ {t₁ t₂} → I → t₁ ⟷ t₂ → rep t₁ t₂) → TList I t₃ t₄ → rep t₃ t₄
  evalTL inj nil           = id
  evalTL inj (cons i x l) = (inj i x) ∘ (evalTL inj l)

-------------------------------------------------------------------------------------
-- We can "reproduce" Amalgamation in the following way:
data Two : Set where one two : Two

TList′ : U → U → Set
TList′ = TList Two

pattern cons₁ = cons one
pattern cons₂ = cons two

evalTL′ : {rep : U → U → Set} (c : Categorical rep)
  (i₁ i₂ : ∀ {t₁ t₂} → t₁ ⟷ t₂ → rep t₁ t₂) → TList′ t₃ t₄ → rep t₃ t₄
evalTL′ {rep = rep} c i₁ i₂ = evalTL c inj
  where
    inj : Two → t₁ ⟷ t₂ → rep t₁ t₂
    inj one x = i₁ x
    inj two x = i₂ x

-------------------------------------------------------------------------------------
