{-# OPTIONS --without-K --exact-split --safe #-}

-- Define syntax for presenting Pi using equational style

module Pi.Equational where

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Pi.Types using (U)
open import Pi.Language using (_⟷_; _◎_; id⟷; !⟷)

private
  variable
    t t₁ t₂ t₃ : U
    
-------------------------------------------------------------------------------------
-- Equational reasoning, from stdlib

private
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

  module Base = SetoidR PiSetoid
  
open Base public
  hiding (step-≈)

infixr 2 step-≈

step-≈ : ∀ (x : U) {y z} → y IsRelatedTo z → x ⟷ y → x IsRelatedTo z
step-≈ = Base.step-≈

syntax step-≈ x y⟷z x⟷y = x ⟨ x⟷y ⟩ y⟷z

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
