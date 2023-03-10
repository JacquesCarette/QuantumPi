{-# OPTIONS --without-K --exact-split --safe #-}

-- Defining various terms over the StatesAndEffects version of Pi

module SPi.Terms where

open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_β‘_; refl)

open import Pi.Types using (U; I; _+α΅€_; _Γα΅€_; π)
open import Pi.Language using (_β·_; !β·)
open import Ancillae
open import Amalgamation using (module Build)
open Build (_β·_) using (TList; consβ)
import ArrowsOverAmalg as A
open A using (_>>>_)
import Arrows.Terms as AT
open import StatesAndEffects 

-------------------------------------------------------------------------------------
private
  variable
    t tβ tβ tβ tβ : U

-------------------------------------------------------------------------------------
-- Example terms

-- Sanity check
inv0 : invSE zero β‘ assertZero
inv0 = refl

-- Additional combinators for complementarity

X : (tβ +α΅€ tβ) β­ (tβ +α΅€ tβ)
X = arr AT.X

CX : (π Γα΅€ π) β­ (π Γα΅€ π)
CX = arr AT.CX

CCX : (π Γα΅€ π Γα΅€ π) β­ (π Γα΅€ π Γα΅€ π)
CCX = arr AT.CCX

H : (tβ +α΅€ tβ) β­ (tβ +α΅€ tβ)
H = arr AT.H

Z : (tβ +α΅€ tβ) β­ (tβ +α΅€ tβ)
Z = arr AT.Z

CZ : (π Γα΅€ π) β­ (π Γα΅€ π)
CZ = arr AT.CZ

copyZ : π β­ (π Γα΅€ π)
copyZ = uniti* >>>> id *** zero >>>> CX

copyH : π β­ (π Γα΅€ π)
copyH = H >>>> copyZ >>>> H *** H

-- Special states and effects

one : I β­ π
one = zero >>>> X
plus : I β­ π
plus = zero >>>> H
minus : I β­ π
minus = plus >>>> Z

assertOne : π β­ I
assertOne = X >>>> assertZero
assertPlus : π β­ I
assertPlus = H >>>> assertZero
assertMinus : π β­ I
assertMinus = Z >>>> assertZero

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
