{-# OPTIONS --without-K --exact-split --safe #-}

-- Lifting an abstract list over a pair of representations.

module StatesAndEffects where

open import PiSyntax using (U; I; _×ᵤ_; _+ᵤ_)
open import PiTagless using (Pi)
open import Pairing using (PiPair)
open import ArrowsOverPair using (module Arrows)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-------------------------------------------------------------------------------------
-- Lifting an abstract pair
record StEffPi {rep₁ rep₂ : U → U → Set}
         (p : U → U → Set)
         (pair : PiPair rep₁ rep₂ p)
         (rep : PiPair rep₁ rep₂ p → U → U → Set) : Set where
  field
    lift : p (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄) → rep pair t₁ t₃

-- Some examples where we use all of the above
module _ {rep₁ rep₂ : U → U → Set} (p₁ : Pi rep₁) (p₂ : Pi rep₂)
         {p : U → U → Set}
         {pair : PiPair rep₁ rep₂ p}
         {rep : PiPair rep₁ rep₂ p → U → U → Set}
         (eff : StEffPi p pair rep) where
  open StEffPi eff
  open Arrows p₁ p₂ p pair

  id₁ : rep₁ I I
  id₁ = Pi.idp p₁

  -- Lifting too general a swap:
  lswap : rep pair t₁ t₃
  lswap = lift (arr₁ (Pi.swap× p₁))

  -- With annotations
  zero : rep pair I (I +ᵤ I)
  zero = lift (arr₁ (Pi.swap× p₁))
