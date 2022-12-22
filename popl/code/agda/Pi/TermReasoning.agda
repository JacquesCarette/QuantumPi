{-# OPTIONS --without-K --exact-split --safe #-}

-- Define syntax for presenting Pi using equational style

module Pi.TermReasoning where

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Pi.Types using (U)
open import Pi.Language using (_⟷_)
open import Pi.Equivalences using (_⟷₂_; trans⟷₂; id⟷₂; !⟷₂)

-------------------------------------------------------------------------------------
-- Equational reasoning, from stdlib

private
  ⟷₂Setoid : {t₁ t₂ : U} → Setoid _ _
  ⟷₂Setoid {t₁} {t₂} = record
    { Carrier = t₁ ⟷ t₂
    ; _≈_ = _⟷₂_
    ; isEquivalence = record
      { refl = id⟷₂
      ; sym = !⟷₂
      ; trans = trans⟷₂
      }
    }

  module Base {t₁ t₂} = SetoidR (⟷₂Setoid {t₁} {t₂})
  
open Base public

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
