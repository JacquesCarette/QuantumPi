{-# OPTIONS --without-K --exact-split --safe #-}

module QPi.Semantics where

open import Pi.Types using (U)
open import Pi.Language as Π using (_⟷_)
open import ArrowsOverAmalg using (arr₁; arr₂)
open import StatesAndEffects using (_↭_; arr; _>>>>_; invSE)
  renaming (_***_ to _****_; zero to kzero; assertZero to bzero)

open import QPi.Syntax

---------------------------------------------------------------------------
-- Semantics

private
  variable
    t t₁ t₂ : U

private
  pizA : (t₁ ⟷ t₂) → t₁ ↭ t₂
  pizA c = arr (arr₁ c)

embed : (t₁ ⇔ t₂) → t₁ ↭ t₂
embed (arrZ c)    = pizA c
embed (arrϕ c)    = arr (arr₂ c)
embed unite⋆l     = pizA Π.unite⋆l
embed uniti⋆l     = pizA Π.uniti⋆l
embed swap⋆       = pizA Π.swap⋆
embed assocl⋆     = pizA Π.assocl⋆
embed assocr⋆     = pizA Π.assocr⋆
embed id⇔         = pizA Π.id⟷
embed (d₁ >>> d₂) = embed d₁ >>>> embed d₂ 
embed (d₁ *** d₂) = embed d₁ **** embed d₂ 
embed zero        = kzero
embed assertZero  = bzero

---------------------------------------------------------------------------
---------------------------------------------------------------------------
