{-# OPTIONS --without-K --exact-split --safe #-}

module CommMonoid where

-- Generate a "commutative monoid" structure over a given language
-- It uses multiplicative notation, but doesn't assume that.

record CMStructure : Set₁ where
  constructor CMon
  infixr 40 _×ᵤ_
  field
    U : Set
    I : U
    _×ᵤ_ : U → U → U

module Build (CM : CMStructure) where
  open CMStructure CM

  private
    variable
      t t₁ t₂ t₃ : U

  -- left-handed version of combinators as primary
  data _⇔_ : U → U → Set where
    unite⋆   : I ×ᵤ t ⇔ t
    uniti⋆   : t ⇔ I ×ᵤ t
    swap⋆    : t₁ ×ᵤ t₂ ⇔  t₂ ×ᵤ t₁
    assocl⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⇔ (t₁ ×ᵤ t₂) ×ᵤ t₃
    assocr⋆  : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⇔ t₁ ×ᵤ (t₂ ×ᵤ t₃)

---------------------------------------------------------------------------
