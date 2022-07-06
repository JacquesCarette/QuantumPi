{-# OPTIONS --without-K --exact-split --safe #-}

-- Show that Unitary(?) has states and effects

module Instances where

open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)

open import PiSyntax
import PiZ
import PiH
open import PiBij using (generalize)
open import Unitary
open import ArrowsOverPair hiding (_***_)
open import GenericList
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
evalTL₁ tl = evalTL FC (generalize PiZ.PiZ) (generalize PiH.PiH) tl
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
    arr (arr₁ uniti⋆l) >>>>
    arr (arr₁ (id⟷₁ ⊗ uniti⋆l)) >>>>
    arr (arr₁ (id⟷₁ ⊗ id⟷₁ ⊗ uniti⋆l)) >>>>
    (zero *** (zero *** (zero *** zero))) >>>>
    arr (arr₂ simon₁) >>>>
    arr (arr₁ simon₂) >>>>
    arr (arr₂ simon₁)
