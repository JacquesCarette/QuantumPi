{-# OPTIONS --without-K --exact-split --safe #-}

module PiTagless where

open import PiSyntax

-------------------------------------------------------------------------------------

private
  variable
    t t₁ t₂ t₃ t₄ : U

record Pi (rep : U → U → Set) : Set where
  field
    unite+l : rep (O +ᵤ t) t
    uniti+l : rep t (O +ᵤ t)
    unite*l : rep (I ×ᵤ t) t
    uniti*l : rep t (I ×ᵤ t)
    swap+ : rep (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
    swap× : rep (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
    idp : rep t t
    _⊚_ : rep t₁ t₂ → rep t₂ t₃ → rep t₁ t₃
    _⊛_ : rep t₁ t₃ → rep t₂ t₄ → rep (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄)
{-
  assocl₊ : t₁ +ᵤ (t₂ +ᵤ t₃) ⟷₁  (t₁ +ᵤ t₂) +ᵤ t₃
  assocr₊ : (t₁ +ᵤ t₂) +ᵤ t₃ ⟷₁  t₁ +ᵤ (t₂ +ᵤ t₃)
  assocl⋆ : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷₁  (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆ : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷₁  t₁ ×ᵤ (t₂ ×ᵤ t₃)
  absorbr : O ×ᵤ t ⟷₁  O
  absorbl : t ×ᵤ O ⟷₁  O
  factorzr : O ⟷₁  t ×ᵤ O
  factorzl : O ⟷₁  O ×ᵤ t
  dist : (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷₁  (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  distl : t₃ ×ᵤ (t₁ +ᵤ t₂)  ⟷₁ (t₃ ×ᵤ t₁) +ᵤ (t₃ ×ᵤ t₂)
  factor : {t₁ t₂ t₃ : U} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷₁ (t₁ +ᵤ t₂) ×ᵤ t₃
  factorl : {t₁ t₂ t₃ : U} → (t₃ ×ᵤ t₁) +ᵤ (t₃ ×ᵤ  t₂) ⟷₁ t₃ ×ᵤ (t₁ +ᵤ t₂)
  id⟷₁  : t ⟷₁  t
  _◎_     : (t₁ ⟷₁  t₂) → (t₂ ⟷₁  t₃) → (t₁ ⟷₁  t₃)
  _⊕_     : (t₁ ⟷₁  t₃) → (t₂ ⟷₁  t₄) → (t₁ +ᵤ t₂ ⟷₁  t₃ +ᵤ t₄)
  _⊗_     : (t₁ ⟷₁  t₃) → (t₂ ⟷₁  t₄) → (t₁ ×ᵤ t₂ ⟷₁  t₃ ×ᵤ t₄)
-}
