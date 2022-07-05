{-# OPTIONS --without-K --exact-split --safe #-}

-- Lifting an abstract list over a pair of representations.

module StatesAndEffects where

open import PiSyntax using (U; I; _×ᵤ_; _+ᵤ_; swap⋆)
-- open import PiTagless using (Pi)
open import GenericList
open import ArrowsOverPair

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-------------------------------------------------------------------------------------

-- This is the type of Ancillas
data N : Set where
  I′ : N
  Two : N
  _×ₙ_ : N → N → N

-- Inject N into U
N⇒U : N → U
N⇒U I′ = I
N⇒U Two = I +ᵤ I
N⇒U (x ×ₙ y) = N⇒U x ×ᵤ N⇒U y

-- Lifting an abstract pair
data StEffPi : U → U → Set where
  lift : {n₁ n₂ : N} → TList (t₁ ×ᵤ N⇒U n₁) (t₂ ×ᵤ N⇒U n₂) → StEffPi t₁ t₂

-- Some examples where we use all of the above
-- With annotations
zero : StEffPi I (I +ᵤ I)
zero = lift (arr₁ swap⋆)

assertZero : StEffPi (I +ᵤ I) I
assertZero = lift (arr₁ swap⋆)

-- A function is an Interpreter when:
Interpreter : (rep : U → U → Set) → Set
Interpreter rep = ∀ {t₁ t₂} → StEffPi t₁ t₂ → rep t₁ t₂
