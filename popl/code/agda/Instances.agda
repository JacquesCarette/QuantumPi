{-# OPTIONS --without-K --exact-split --safe #-}

-- Show that Unitary(?) has states and effects

module Instances where

import Data.Float as F
open import Data.List using (map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_; flip)

open import PiSyntax
import PiZ
import PiH
open import PiBij using (generalize; ⟦_⟧)
open import Unitary
import ArrowsOverPair as A
open import GenericList
open import StatesAndEffects
open Direct

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

infixl 9 _○_

_○_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ○ g = λ a → g (f a)

private
  effect : {t₂ : U} (n : N) → 𝒰 ((N⇒U n) ×ᵤ t₂) → 𝒰 (I ×ᵤ t₂)
  effect n f z = sumf (map (λ w → f (w , proj₂ z)) (enumN n))

  delta : (n : N) → (x : ⟦ N⇒U n ⟧) → F.Float
  delta (just Two)        (inj₁ x) = 1.0
  delta (just Two)        (inj₂ y) = 0.0
  delta (just (x₁ ×ₙ x₂)) x        = delta (just x₁) (proj₁ x) F.* delta (just x₂) (proj₂ x)
  delta nothing           _        = 1.0

  state : {t : U} (n : N) → 𝒰 (I ×ᵤ t) → 𝒰 ((N⇒U n) ×ᵤ t)
  state n f (i , x) = delta n i F.* f ( tt , x )

eval : ∀ {t₁ t₂ : U} → StEffPi t₁ t₂ → Fwd t₁ t₂
eval (lift {n₁ = n₁} {n₂} z) = evalTL₁ A.uniti*l ○ state n₁ ○ evalTL₁ z ○ effect n₂ ○ evalTL₁ A.unite*l
{-
eval (lift {t₁} {t₂} {just x} {just y} z)   = evalTL₁ A.uniti*l ○ state (just x) ○ evalTL₁ z ○ effect (just y) ○ evalTL₁ A.unite*l
eval (lift {t₁} {t₂} {just x} {nothing} z)  = evalTL₁ A.uniti*l ○ state (just x) ○ evalTL₁ z ○                   evalTL₁ A.unite*l
eval (lift {t₁} {t₂} {nothing} {just x} z)  = evalTL₁ A.uniti*l ○                  evalTL₁ z ○ effect (just x) ○ evalTL₁ A.unite*l
eval (lift {t₁} {t₂} {nothing} {nothing} z) = evalTL₁ A.uniti*l ○                  evalTL₁ z ○                   evalTL₁ A.unite*l
-}

Bool : U
Bool = I +ᵤ I

{--

1 -> unit intro
1 x 1 x 1 x 1 -> zero
2 x 2 x 2 x 2 -> simon1 ; simon2 ; simon1

--}

-- Simon using the Direct method
module SimonDirect where
  open Direct

  simon : StEffPi I (Bool ×ᵤ Bool ×ᵤ Bool ×ᵤ Bool)
  simon =
    uniti*l >>>>
    idst *** uniti*l >>>>
    idst *** (idst *** uniti*l) >>>>
    (zero *** (zero *** (zero *** zero))) >>>>
    arr (A.arr₂ simon₁) >>>>
    arr (A.arr₁ simon₂) >>>>
    arr (A.arr₂ simon₁)
