{-# OPTIONS --without-K --exact-split --safe #-}

module Multiplicative where

-- Generate a "multiplicative" structure over a given language

record MultiplicativeStructure : Set₁ where
  constructor Mult
  infixr 40 _×ᵤ_
  field
    U : Set
    I : U
    _×ᵤ_ : U → U → U

module Build (M : MultiplicativeStructure) where
  open MultiplicativeStructure M

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
