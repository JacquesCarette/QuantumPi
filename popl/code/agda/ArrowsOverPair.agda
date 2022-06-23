{-# OPTIONS --without-K --exact-split --safe #-}

module ArrowsOverPair where

open import Data.Float as F using (Float)
open import Data.List using (List; map; foldr)
open import Data.Product as Prod using (_,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)

open import PiSyntax
open import PiZ hiding (Fwd)
open import PiTagless
open import Pairing

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U
    a b c d : U

-------------------------------------------------------------------------------------
-- Form "Arrows" over a pairing of Pi languages. We need the following 3 items:
-- 1. idp, 2. swapp and 3. first.
module Arrows {rep₁ rep₂ : U → U → Set} (p₁ : Pi rep₁) (p₂ : Pi rep₂)
         (p : U → U → Set) (πpair : PiPair rep₁ rep₂ p) where
  open PiPair πpair
  open Pair pair

  arr₁ : rep₁ t₁ t₂ -> p t₁ t₂
  arr₁ c = cons₁ c nil
  arr₂ : rep₂ t₁ t₂ -> p t₁ t₂
  arr₂ c = cons₂ c nil

  idzh : p t t
  idzh = arr₁ (Pi.idp p₁)
  swap× : p (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
  swap× = arr₁ (Pi.swap× p₁)
  assocl× : p  (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ((t₁ ×ᵤ t₂) ×ᵤ t₃)
  assocl× = arr₁ (Pi.assocl* p₁)
  assocr× : p  ((t₁ ×ᵤ t₂) ×ᵤ t₃) (t₁ ×ᵤ (t₂ ×ᵤ t₃))
  assocr× = arr₁ (Pi.assocr* p₁)
  unite*l : p (I ×ᵤ t) t
  unite*l = arr₁ (Pi.unite*l p₁)
  uniti*l : p t (I ×ᵤ t)
  uniti*l = arr₁ (Pi.uniti*l p₁)

  second : p t₁ t₂ → p (t₃ ×ᵤ t₁) (t₃ ×ᵤ t₂)
  second c = swap× ⊚⊚ first c ⊚⊚ swap×

  _***_ : p t₁ t₂ → p t₃ t₄ → p (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₄)
  xs *** ys = first xs ⊚⊚ second ys
