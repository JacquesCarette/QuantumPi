{-# OPTIONS --without-K --exact-split --safe #-}

module Pi.Reasoning where

open import Pi.Types using (U)
open import Pi.Language using (_⟷_; _◎_; id⟷)

private
  variable
    t t₁ t₂ t₃ : U
    
-------------------------------------------------------------------------------------
-- Equational reasoning

infixr 10 _⟨_⟩_
infix  15 _∎

_⟨_⟩_ : (t₁ : U) → (t₁ ⟷  t₂) → (t₂ ⟷  t₃) → (t₁ ⟷  t₃)
_ ⟨ c₁ ⟩ c₂ = c₁ ◎ c₂

_∎ : (t : U) → t ⟷  t
_∎ t = id⟷

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
