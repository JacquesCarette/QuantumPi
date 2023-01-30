{-# OPTIONS --without-K --exact-split --safe #-}

module QPi.TermReasoning where

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Pi.Types using (U)
open import QPi.Syntax using (_⇔_; _>>>_; _***_)
open import QPi.Equivalences using (_≡_; id≡; trans≡; !≡; cong≡; cong***)

---------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ : U
    d d₁ d₂ d₃ d₄ : t₁ ⇔ t₂

-- Equational reasoning, from stdlib

private
  ≡Setoid : {t₁ t₂ : U} → Setoid _ _
  ≡Setoid {t₁} {t₂} = record
    { Carrier = t₁ ⇔ t₂
    ; _≈_ = _≡_
    ; isEquivalence = record
      { refl = id≡
      ; sym = !≡
      ; trans = trans≡
      }
    }

  module Base {t₁ t₂} = SetoidR (≡Setoid {t₁} {t₂})
  
open Base public hiding (step-≈; step-≡)

infixr 2 step-≡
step-≡ :  (x : t₁ ⇔ t₂) {y z : t₁ ⇔ t₂} →
  _IsRelatedTo_ y z → x ≡ y → x IsRelatedTo z
step-≡ = Base.step-≈

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

-- Cheat and use ◎ for >>> and ⊗ for ***, else we don't save enough
infixr 4 _⟩◎⟨_ id⟩◎⟨_
infixl 5 _⟩◎⟨id
infixr 6 _⟩⊗⟨_ id⟩⊗⟨_
infixl 7 _⟩⊗⟨id
infixr 3 _◯_

_◯_ : (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
_◯_ = trans≡

_⟩◎⟨_ : (d₁ ≡ d₃) → (d₂ ≡ d₄) → (d₁ >>> d₂) ≡ (d₃ >>> d₄)
_⟩◎⟨_ = cong≡

id⟩◎⟨_ : (d₂ ≡ d₄) → (d₁ >>> d₂) ≡ (d₁ >>> d₄)
id⟩◎⟨_ = cong≡ id≡

_⟩◎⟨id : (d₁ ≡ d₃) → (d₁ >>> d₂) ≡ (d₃ >>> d₂)
d ⟩◎⟨id = cong≡ d id≡

_⟩⊗⟨_ : (d₁ ≡ d₃) → (d₂ ≡ d₄) → (d₁ *** d₂) ≡ (d₃ *** d₄)
_⟩⊗⟨_ = cong***

id⟩⊗⟨_ : (d₂ ≡ d₄) → (d₁ *** d₂) ≡ (d₁ *** d₄)
id⟩⊗⟨_ = cong*** id≡

_⟩⊗⟨id : (d₁ ≡ d₃) → (d₁ *** d₂) ≡ (d₃ *** d₂)
e ⟩⊗⟨id = cong*** e id≡

---------------------------------------------------------------------------
---------------------------------------------------------------------------

