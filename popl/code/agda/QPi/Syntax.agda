{-# OPTIONS --without-K --exact-split --safe #-}

module QPi.Syntax where

open import Pi.Types using (U; I; _×ᵤ_; 𝟚)
open import Pi.Language using (_⟷_)

open import Multiplicative using (MultiplicativeStructure; Mult; module Build)

---------------------------------------------------------------------------
-- The surface Quantum Pi language

infix  10 _⇔_
infixr 30 _>>>_
infixr 40 _***_

private
  variable
    t t₁ t₂ t₃ t₄ : U

-- Set things up
  MS : MultiplicativeStructure
  MS = Mult U I _×ᵤ_

  module M = Build MS
  
-- Arrow combinators

data _⇔_ : U → U → Set where
  arrZ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂) 
  arrϕ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂)
  -- multiplicative structure 
  mult     : t₁ M.⇔ t₂ → t₁ ⇔ t₂
  -- composition (sequential and parallel)
  id⇔    : t ⇔ t
  _>>>_  : (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)
  _***_  : (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (t₁ ×ᵤ t₂ ⇔ t₃ ×ᵤ t₄)
  -- inverse
  inv    : (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
  -- states and effects
  zero        : I ⇔ 𝟚
  assertZero  : 𝟚 ⇔ I

pattern unite⋆l = mult M.unite⋆
pattern uniti⋆l = mult M.uniti⋆
pattern swap⋆   = mult M.swap⋆
pattern assocl⋆ = mult M.assocl⋆
pattern assocr⋆ = mult M.assocr⋆

-- These are right-biased
unite⋆r : {t : U} → t ×ᵤ I ⇔  t
unite⋆r = swap⋆ >>> unite⋆l

uniti⋆r : {t : U} → t ⇔ t ×ᵤ I
uniti⋆r =  uniti⋆l >>> swap⋆ 
---------------------------------------------------------------------------
