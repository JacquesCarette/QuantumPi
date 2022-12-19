{-# OPTIONS --without-K --exact-split --safe #-}

module PiSyntax where

open import Data.Sum as Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Pi.Types using (U; O; I; _+ᵤ_; _×ᵤ_; 𝟚)

-------------------------------------------------------------------------------------
-- 1-combinators

private
  variable
    t t₁ t₂ t₃ t₄ : U

infix 30 _⟷_
infixr 10 _◎_
infixr 20 _⊕_
infixr 30 _⊗_

data _⟷_  : U → U → Set where
  id⟷  : t ⟷  t
  --
  swap₊   : t₁ +ᵤ t₂ ⟷  t₂ +ᵤ t₁
  assocr₊ : (t₁ +ᵤ t₂) +ᵤ t₃ ⟷ t₁ +ᵤ (t₂ +ᵤ t₃)
  assocl₊ : t₁ +ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ +ᵤ t₂) +ᵤ t₃
  unite₊l : O +ᵤ t ⟷  t
  uniti₊l : t ⟷  O +ᵤ t
  ---
  swap⋆   : t₁ ×ᵤ t₂ ⟷  t₂ ×ᵤ t₁
  assocr⋆ : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  assocl⋆ : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
  unite⋆l : I ×ᵤ t ⟷  t
  uniti⋆l : t ⟷  I ×ᵤ t
  --
  dist : (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor : {t₁ t₂ t₃ : U} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  absorbl : t ×ᵤ O ⟷ O
  factorzr : O ⟷  t ×ᵤ O
  --
  _◎_     : (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_     : (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)

-------------------------------------------------------------------------------------
-- Equational reasoning

infixr 10 _⟨_⟩_
infix  15 _∎

_⟨_⟩_ : (t₁ : U) → (t₁ ⟷  t₂) → (t₂ ⟷  t₃) → (t₁ ⟷  t₃)
_ ⟨ c₁ ⟩ c₂ = c₁ ◎ c₂

_∎ : (t : U) → t ⟷  t
_∎ t = id⟷

-------------------------------------------------------------------------------------
-- Inverse
!⟷ : t₁ ⟷  t₂ → t₂ ⟷  t₁
!⟷ unite₊l = uniti₊l
!⟷ uniti₊l = unite₊l
!⟷ unite⋆l = uniti⋆l
!⟷ uniti⋆l = unite⋆l
!⟷ swap₊   = swap₊
!⟷ swap⋆   = swap⋆
!⟷ assocl₊ = assocr₊
!⟷ assocr₊ = assocl₊
!⟷ assocl⋆ = assocr⋆
!⟷ assocr⋆ = assocl⋆
!⟷ absorbl = factorzr
!⟷ factorzr = absorbl
!⟷ dist = factor
!⟷ factor = dist
!⟷ id⟷ = id⟷
!⟷ (c₁ ◎ c₂) = !⟷ c₂ ◎ !⟷ c₁
!⟷ (c₁ ⊕ c₂) = !⟷ c₁ ⊕ !⟷ c₂
!⟷ (c₁ ⊗ c₂) = !⟷ c₁ ⊗ !⟷ c₂

-------------------------------------------------------------------------------------
-- Common terms

unite₊r : {t : U} → t +ᵤ O ⟷  t
unite₊r = swap₊ ◎ unite₊l

uniti₊r : {t : U} → t ⟷  t +ᵤ O
uniti₊r = uniti₊l ◎ swap₊

unite⋆r : {t : U} → t ×ᵤ I ⟷  t
unite⋆r = swap⋆ ◎ unite⋆l

uniti⋆r : {t : U} → t ⟷ t ×ᵤ I
uniti⋆r = uniti⋆l ◎ swap⋆

ctrl : t ⟷ t → (𝟚 ×ᵤ t) ⟷ (𝟚 ×ᵤ t)
ctrl c = dist ◎ (id⟷ ⊕ id⟷ ⊗ c) ◎ factor

cx : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
cx = ctrl swap₊

ccx : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ccx = ctrl cx

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
