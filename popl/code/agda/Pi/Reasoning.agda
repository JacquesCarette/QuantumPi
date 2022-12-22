{-# OPTIONS --without-K --exact-split --safe #-}

module Pi.Reasoning where

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Pi.Types using (U)
open import Pi.Language using (_⟷_; _◎_; id⟷; !⟷)

private
  variable
    t t₁ t₂ t₃ : U
    
-------------------------------------------------------------------------------------
-- Equational reasoning

PiSetoid : Setoid _ _
PiSetoid = record
  { Carrier = U
  ; _≈_ = _⟷_
  ; isEquivalence = record
    { refl = id⟷
    ; sym = !⟷
    ; trans = _◎_
    }
  }

private
  module Base = SetoidR PiSetoid
  
open Base public
  hiding (step-≈)

infixr 2 step-≈

step-≈ : ∀ (x : U) {y z} → y IsRelatedTo z → x ⟷ y → x IsRelatedTo z
step-≈ = Base.step-≈

syntax step-≈ x y⟷z x⟷y = x ⟨ x⟷y ⟩ y⟷z

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
