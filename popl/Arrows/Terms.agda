
{-# OPTIONS --without-K --exact-split --safe #-}

module Arrows.Terms where

open import Pi.Types using (U; _+ᵤ_; _×ᵤ_; 𝟚)
open import Pi.Language using (_⟷_; swap₊)
open import Pi.Terms using (ctrl; cx; ccx)
open import Amalgamation using (module Build)
open Build (_⟷_) using (TList)
open import ArrowsOverAmalg using (arr₁; arr₂; _>>>_; id; _***_)

-------------------------------------------------------------------------------------
private
  variable
    t₁ t₂ : U

-------------------------------------------------------------------------------------
-- Examples of terms in this language, taken from section 5.1

X : TList (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
X = arr₁ swap₊

CX : TList (𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚)
CX = arr₁ cx

CCX : TList (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚)
CCX = arr₁ ccx

H : TList (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
H = arr₂ swap₊

Z : TList (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
Z = H >>> X >>> H

CZ : TList (𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚)
CZ = id *** H >>> CX >>> id *** H

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
