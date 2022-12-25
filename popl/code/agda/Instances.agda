{-# OPTIONS --without-K --exact-split --safe #-}

-- Show that Unitary has states and effects

module Instances where

import Data.Float as F
open import Data.List using (head)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Pi.Types using (U; I; _×ᵤ_; ⟦_⟧)
open import Pi.Language using (_⟷_)
open import Amalgamation using (module Build; Categorical)
open Build (_⟷_) using (TList; evalTL)
import ArrowsOverAmalg as A
open import Ancillae using (N; N⇒U; enumN; Anc; Two; _×ₙ_)
open import StatesAndEffects using (_↭_; lift)

open import Unitary using (UVec)
open import PiZ using (evalZ)
open import PiH using (evalH)
open import GenericPi using (Fwd)

FC : Categorical Fwd
FC = record
  { id = λ x → x
  ; _∘_ = λ f g h x → g (f h) x
  }

evalTL₁ : ∀ {t₁ t₂ : U} → TList t₁ t₂ → Fwd t₁ t₂
evalTL₁ tl = evalTL FC evalZ evalH tl

infixl 9 _○_

_○_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ○ g = λ a → g (f a)

private
  effect : {t₂ : U} (n : N) → UVec (t₂ ×ᵤ (N⇒U n)) → UVec (t₂ ×ᵤ I)
  effect n f z = effect′ (head (enumN n))
    where effect′ : Maybe ⟦ N⇒U n ⟧ → F.Float
          effect′ (just x) = f (proj₁ z , x)
          effect′ nothing = 0.0 -- if we had a vector, we could prove this cannot happen

  delta : (n : N) → (x : ⟦ N⇒U n ⟧) → F.Float
  delta (just Two)        (inj₁ x) = 1.0
  delta (just Two)        (inj₂ y) = 0.0
  delta (just (x₁ ×ₙ x₂)) x        = delta (just x₁) (proj₁ x) F.* delta (just x₂) (proj₂ x)
  delta nothing           _        = 1.0

  state : {t : U} (n : N) → UVec (t ×ᵤ I) → UVec (t ×ᵤ (N⇒U n))
  state n f (x , i) = delta n i F.* f ( x , tt )

-- re-expand out to test each part
evalSE : ∀ {t₁ t₂ : U} → t₁ ↭ t₂ → Fwd t₁ t₂
evalSE (lift {n₁ = nothing} {nothing}   z) = evalTL₁ A.uniti* ○           evalTL₁ z ○            evalTL₁ A.unite*
evalSE (lift {n₁ = nothing} y@{just _}  z) = evalTL₁ A.uniti* ○           evalTL₁ z ○ effect y ○ evalTL₁ A.unite*
evalSE (lift x@{n₁ = just _} {nothing}  z) = evalTL₁ A.uniti* ○ state x ○ evalTL₁ z ○  evalTL₁ A.unite*
evalSE (lift x@{n₁ = just _} y@{just _} z) = evalTL₁ A.uniti* ○ state x ○ evalTL₁ z ○ effect y ○ evalTL₁ A.unite*
--- evalSE (lift {n₁ = n₁} {n₂} z) = evalTL₁ A.uniti* ○ state n₁ ○ evalTL₁ z ○ effect n₂ ○ evalTL₁ A.unite*
