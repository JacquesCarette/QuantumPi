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
-- Lifting an abstract pair
data StEffPi : U → U → Set where
  lift : TList (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄) → StEffPi t₁ t₃

-- Some examples where we use all of the above
-- Lifting too general a swap:
lswap : StEffPi t₁ t₃
lswap = lift (arr₁ swap⋆)

-- With annotations
zero : StEffPi I (I +ᵤ I)
zero = lift (arr₁ swap⋆)

assertZero : StEffPi (I +ᵤ I) I
assertZero = lift (arr₁ swap⋆)

-- A function is an Interpreter when:
Interpreter : (rep : U → U → Set) → Set
Interpreter rep = ∀ {t₁ t₂} → StEffPi t₁ t₂ → rep t₁ t₂
