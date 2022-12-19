{-# OPTIONS --without-K --exact-split --safe #-}

-- Defining various terms over the StatesAndEffects version of Pi

module SPi.Terms where

open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Pi.Types using (U; I; _+ᵤ_; _×ᵤ_; 𝟚)
open import Pi.Language using (_⟷_; !⟷)
open import Ancillae
open import Amalgamation using (TList; cons₁)
import ArrowsOverAmalg as A
open A using (_>>>_)
import Arrows.Terms as AT
open import StatesAndEffects 

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ : U

-------------------------------------------------------------------------------------
-- Example terms

-- With annotations
zero : I ↭ (I +ᵤ I)
zero = lift A.swap×

assertZero : (I +ᵤ I) ↭ I
assertZero = lift A.swap×

-- Sanity check
inv0 : invSE zero ≡ assertZero
inv0 = refl

-- Additional combinators for complementarity

X : (t₁ +ᵤ t₂) ↭ (t₂ +ᵤ t₁)
X = arr AT.X

CX : (𝟚 ×ᵤ 𝟚) ↭ (𝟚 ×ᵤ 𝟚)
CX = arr AT.CX

CCX : (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚) ↭ (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚)
CCX = arr AT.CCX

H : (t₁ +ᵤ t₂) ↭ (t₂ +ᵤ t₁)
H = arr AT.H

Z : (t₁ +ᵤ t₂) ↭ (t₂ +ᵤ t₁)
Z = arr AT.Z

CZ : (𝟚 ×ᵤ 𝟚) ↭ (𝟚 ×ᵤ 𝟚)
CZ = arr AT.CZ

copyZ : 𝟚 ↭ (𝟚 ×ᵤ 𝟚)
copyZ = uniti* >>>> id *** zero >>>> CX

copyH : 𝟚 ↭ (𝟚 ×ᵤ 𝟚)
copyH = H >>>> copyZ >>>> H *** H

-- Special states and effects

one : I ↭ 𝟚
one = zero >>>> X
plus : I ↭ 𝟚
plus = zero >>>> H
minus : I ↭ 𝟚
minus = plus >>>> Z

assertOne : 𝟚 ↭ I
assertOne = X >>>> assertZero
assertPlus : 𝟚 ↭ I
assertPlus = H >>>> assertZero
assertMinus : 𝟚 ↭ I
assertMinus = Z >>>> assertZero

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
