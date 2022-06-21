{-# OPTIONS --without-K --exact-split --safe #-}

module PiSyntax where

open import Data.Nat using (ℕ)

-------------------------------------------------------------------------------------
-- Nat

private
  variable
    m n o p q r : ℕ

-- Types

data U : Set where
  O : U
  I : U
  _+ᵤ_ : U → U → U
  _×ᵤ_ : U → U → U

infixr 40 _+ᵤ_ _×ᵤ_
infix 30 _⟷₁_
infixr 50 _◎_ _⊕_

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-- 1-combinators

data _⟷₁_  : U → U → Set where
  unite₊l : O +ᵤ t ⟷₁  t
  uniti₊l : t ⟷₁  O +ᵤ t
  unite⋆l : I ×ᵤ t ⟷₁  t
  uniti⋆l : t ⟷₁  I ×ᵤ t
  swap₊   : t₁ +ᵤ t₂ ⟷₁  t₂ +ᵤ t₁
  swap⋆   : t₁ ×ᵤ t₂ ⟷₁  t₂ ×ᵤ t₁
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

-- Equational reasoning

infixr 10 _⟷₁⟨_⟩_
infix  15 _⟷₁∎

_⟷₁⟨_⟩_ : (t₁ : U) → (t₁ ⟷₁  t₂) → (t₂ ⟷₁  t₃) → (t₁ ⟷₁  t₃)
_ ⟷₁⟨ c₁ ⟩ c₂ = c₁ ◎ c₂

_⟷₁∎ : (t : U) → t ⟷₁  t
_⟷₁∎ t = id⟷₁

-- Coherence

unite₊r : {t : U} → t +ᵤ O ⟷₁  t
unite₊r = swap₊ ◎ unite₊l

uniti₊r : t ⟷₁  t +ᵤ O
uniti₊r = uniti₊l ◎ swap₊

unite⋆r : {t : U} → t ×ᵤ I ⟷₁  t
unite⋆r = swap⋆ ◎ unite⋆l

uniti⋆r : t ⟷₁  t ×ᵤ I
uniti⋆r = uniti⋆l ◎ swap⋆

!⟷₁ : t₁ ⟷₁  t₂ → t₂ ⟷₁  t₁
!⟷₁ unite₊l = uniti₊l
!⟷₁ uniti₊l = unite₊l
!⟷₁ unite⋆l = uniti⋆l
!⟷₁ uniti⋆l = unite⋆l
!⟷₁ swap₊   = swap₊
!⟷₁ swap⋆   = swap⋆
!⟷₁ assocl₊ = assocr₊
!⟷₁ assocr₊ = assocl₊
!⟷₁ assocl⋆ = assocr⋆
!⟷₁ assocr⋆ = assocl⋆
!⟷₁ absorbr = factorzl
!⟷₁ absorbl = factorzr
!⟷₁ factorzr = absorbl
!⟷₁ factorzl = absorbr
!⟷₁ dist = factor
!⟷₁ distl = factorl
!⟷₁ factorl = distl
!⟷₁ factor = dist
!⟷₁ id⟷₁ = id⟷₁
!⟷₁ (c₁ ◎ c₂) = !⟷₁ c₂ ◎ !⟷₁ c₁
!⟷₁ (c₁ ⊕ c₂) = !⟷₁ c₁ ⊕ !⟷₁ c₂
!⟷₁ (c₁ ⊗ c₂) = !⟷₁ c₁ ⊗ !⟷₁ c₂

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
