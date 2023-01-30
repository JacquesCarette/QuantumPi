{-# OPTIONS --without-K --exact-split --safe #-}

-- Define syntax for presenting Pi using equational style

module Pi.TermReasoning where

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Pi.Types using (U)
open import Pi.Language using (_⟷_; _◎_; _⊗_; _⊕_)
open import Pi.Equivalences using (_⟷₂_; trans⟷₂; id⟷₂; !⟷₂; _⊡_; resp⊗⟷₂; resp⊕⟷₂)

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

-- Extra combinators to make more things pretty
private
  variable
    t₁ t₂ t₃ : U
    c₁ c₂ c₃ c₄ : t₁ ⟷ t₂

infixr 4 _○_
infixr 4 _⟩◎⟨_ id⟩◎⟨_
infixl 5 _⟩◎⟨id
infixr 6 _⟩⊗⟨_ id⟩⊗⟨_
infixl 7 _⟩⊗⟨id

_○_ : (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
_○_ = trans⟷₂

_⟩◎⟨_ : (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
_⟩◎⟨_ = _⊡_

id⟩◎⟨_ : (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₁ ◎ c₄)
id⟩◎⟨_ = id⟷₂ ⊡_

_⟩◎⟨id : (c₁ ⟷₂ c₃) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₂)
_⟩◎⟨id = _⊡ id⟷₂

_⟩⊗⟨_ : (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊗ c₂) ⟷₂ (c₃ ⊗ c₄)
_⟩⊗⟨_ = resp⊗⟷₂

id⟩⊗⟨_ : (c₂ ⟷₂ c₄) → (c₁ ⊗ c₂) ⟷₂ (c₁ ⊗ c₄)
id⟩⊗⟨_ = resp⊗⟷₂ id⟷₂

_⟩⊗⟨id : (c₁ ⟷₂ c₃) → (c₁ ⊗ c₂) ⟷₂ (c₃ ⊗ c₂)
d ⟩⊗⟨id = resp⊗⟷₂ d id⟷₂

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
