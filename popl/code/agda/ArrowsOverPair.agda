{-# OPTIONS --without-K --exact-split --safe #-}

module ArrowsOverPair where

open import PiSyntax using (U; I; _×ᵤ_; _⟷₁_; id⟷₁; swap⋆; assocl⋆; assocr⋆; unite⋆l; uniti⋆l)
open import PiBij hiding (Fwd)
open import PiTagless using (Pi)
open import GenericList using (TList; nil; cons₁; cons₂; _⊚⊚_; first; inv)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U
    a b c d : U

-------------------------------------------------------------------------------------
-- Form "Arrows" over a pairing of Pi languages. We need the following 3 items:
-- 1. idp, 2. swapp and 3. first.
infixr 50 _>>>_

arr₁ : t₁ ⟷₁ t₂ -> TList t₁ t₂
arr₁ c = cons₁ c nil
arr₂ : t₁ ⟷₁ t₂ -> TList t₁ t₂
arr₂ c = cons₂ c nil

idzh : TList t t
idzh = arr₁ id⟷₁
swap× : TList (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
swap× = arr₁ swap⋆
assocl× : TList  (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ((t₁ ×ᵤ t₂) ×ᵤ t₃)
assocl× = arr₁ assocl⋆
assocr× : TList  ((t₁ ×ᵤ t₂) ×ᵤ t₃) (t₁ ×ᵤ (t₂ ×ᵤ t₃))
assocr× = arr₁ assocr⋆
unite*l : TList (I ×ᵤ t) t
unite*l = arr₁ unite⋆l
uniti*l : TList t (I ×ᵤ t)
uniti*l = arr₁ uniti⋆l

second : TList t₁ t₂ → TList (t₃ ×ᵤ t₁) (t₃ ×ᵤ t₂)
second c = swap× ⊚⊚ first c ⊚⊚ swap×

_***_ : TList t₁ t₂ → TList t₃ t₄ → TList (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₄)
xs *** ys = first xs ⊚⊚ second ys

_>>>_ : TList t₁ t₂ → TList t₂ t₃ → TList t₁ t₃
c₀ >>> c₁ = c₀ ⊚⊚ c₁
