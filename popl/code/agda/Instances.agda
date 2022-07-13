{-# OPTIONS --without-K --exact-split --safe #-}

-- Show that Unitary(?) has states and effects

module Instances where

import Data.Float as F
open import Data.List using (map; length; head)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_; flip)

open import PiSyntax
open import PiZ using (evalZ)
open import PiH using (evalH)
open import PiBij using (⟦_⟧)
open import Unitary
import ArrowsOverAmalg as A
open import Amalgamation using (TList; Categorical; evalTL)
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
evalTL₁ tl = evalTL FC evalZ evalH tl

infixl 9 _○_

_○_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ○ g = λ a → g (f a)

private
  effect : {t₂ : U} (n : N) → 𝒰 (t₂ ×ᵤ (N⇒U n)) → 𝒰 (t₂ ×ᵤ I)
  effect n f z = effect′ (head (enumN n))
    where effect′ : Maybe ⟦ N⇒U n ⟧ → F.Float
          effect′ (just x) = f (proj₁ z , x)
          effect′ nothing = 0.0 -- if we had a vector, we could prove this cannot happen

  delta : (n : N) → (x : ⟦ N⇒U n ⟧) → F.Float
  delta (just Two)        (inj₁ x) = 1.0
  delta (just Two)        (inj₂ y) = 0.0
  delta (just (x₁ ×ₙ x₂)) x        = delta (just x₁) (proj₁ x) F.* delta (just x₂) (proj₂ x)
  delta nothing           _        = 1.0

  state : {t : U} (n : N) → 𝒰 (t ×ᵤ I) → 𝒰 (t ×ᵤ (N⇒U n))
  state n f (x , i) = delta n i F.* f ( x , tt )

-- re-expand out to test each part
evalSE : ∀ {t₁ t₂ : U} → StEffPi t₁ t₂ → Fwd t₁ t₂
evalSE (lift {n₁ = nothing} {nothing}   z) = evalTL₁ A.uniti* ○           evalTL₁ z ○            evalTL₁ A.unite*
evalSE (lift {n₁ = nothing} y@{just _}  z) = evalTL₁ A.uniti* ○           evalTL₁ z ○ effect y ○ evalTL₁ A.unite*
evalSE (lift x@{n₁ = just _} {nothing}  z) = evalTL₁ A.uniti* ○ state x ○ evalTL₁ z ○  evalTL₁ A.unite*
evalSE (lift x@{n₁ = just _} y@{just _} z) = evalTL₁ A.uniti* ○ state x ○ evalTL₁ z ○ effect y ○ evalTL₁ A.unite*
--- evalSE (lift {n₁ = n₁} {n₂} z) = evalTL₁ A.uniti* ○ state n₁ ○ evalTL₁ z ○ effect n₂ ○ evalTL₁ A.unite*
