{-# OPTIONS --without-K --exact-split --safe #-}

module Pairing where

open import PiSyntax using (U; _×ᵤ_)

-------------------------------------------------------------------------------------
-- Pairing

-- Pair any two things that are binary predicates over a type using alternation.
-- This is basically the 'm' line of section 3.2.

-- Maybe "Pairing" is a bad name, since this ends up being a list-of-eithers.

-- However, we put composition in the language itself instead of at the meta-level
-- since this is a polymorphic representation; if we'd used a inductive type, it
-- could have been defined.
record Pair {W : Set} (rep₁ rep₂ : W → W → Set) (p : W → W → Set) : Set where
  infixr 50 _⊚⊚_
  field
    nil : {t : W} → p t t
    cons₁ : {t₁ t₂ t₃ : W} → rep₁ t₁ t₂ → p t₂ t₃ → p t₁ t₃
    cons₂ : {t₁ t₂ t₃ : W} → rep₂ t₁ t₂ → p t₂ t₃ → p t₁ t₃
    _⊚⊚_ : {t₁ t₂ t₃ : W} → p t₁ t₂ → p t₂ t₃ → p t₁ t₃

-- Pair two things that depend on U types
-- Because we're generic over the representation, we have to ask that
-- they implement first and inv, as it depends on the implementation details
record PiPair (rep₁ rep₂ : U → U → Set) (p : U → U → Set) : Set where
  field
    pair : Pair rep₁ rep₂ p
    first : {t₁ t₂ t₃ : U} → p t₁ t₂ -> p (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)
    inv : {t₁ t₂ : U} → p t₁ t₂ → p t₂ t₁
