{-# OPTIONS --without-K #-}

module QPi.Syntax where

open import Pi.Types using (U; O; I; _+ᵤ_; _×ᵤ_; 𝟚)
open import PiSyntax using (_⟷_)

---------------------------------------------------------------------------
-- The surface Quantum Pi language

infix  10 _⇔_
infixr 30 _>>>_
infixr 40 _***_

private
  variable
    t t₁ t₂ t₃ t₄ : U

-- Arrow combinators

data _⇔_ : U → U → Set where
  arrZ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂) 
  arrϕ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂)
  -- multiplicative structure
  unite⋆   : t ×ᵤ I ⇔ t
  uniti⋆   : t ⇔ t ×ᵤ I
  swap⋆    : t₁ ×ᵤ t₂ ⇔  t₂ ×ᵤ t₁
  assocl⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⇔ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆  : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⇔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  -- composition (sequential and parallel)
  id⇔    : t ⇔ t
  _>>>_  : (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)
  _***_  : (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (t₁ ×ᵤ t₂ ⇔ t₃ ×ᵤ t₄)
  -- inverse
  inv    : (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
  -- states and effects
  zero        : I ⇔ 𝟚
  assertZero  : 𝟚 ⇔ I

---------------------------------------------------------------------------
