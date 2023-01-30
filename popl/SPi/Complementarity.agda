{-# OPTIONS --without-K --exact-split --safe #-}

-- Complementarity equations

module SPi.Complementarity where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Pi.Types using (U)
open import StatesAndEffects using (_↭_; _>>>>_; id; assocr×; _***_; swap; invSE)
open import SPi.Terms using (copyZ; copyH)

private
  variable
    t₁ t₂ : U
    
-------------------------------------------------------------------------------------
-- complementarity equations

-- Define this equivalence for display purposes, and hack it to be ≡ for now,
-- until a proper equivalence can be defined.

infix 4 _≈_

_≈_ : t₁ ↭ t₂ → t₁ ↭ t₂ → Set
_≈_ x y = x ≡ y

-- Just typecheck them
eqZ₁ eqZ₂ eqZ₃ eqZ₄ : Set
eqZ₁ = copyZ >>>> (id *** copyZ) ≈ copyZ >>>> (copyZ *** id) >>>> assocr×
eqZ₂ = copyZ >>>> swap ≈ copyZ
eqZ₃ = copyZ >>>> invSE copyZ ≈ id
eqZ₄ = (copyZ *** id) >>>> (id *** copyZ) ≈ (id *** copyZ) >>>> (copyZ *** id)

eqH₁ eqH₂ eqH₃ eqH₄ : Set
eqH₁ = copyH >>>> (id *** copyH) ≈ copyH >>>> (copyH *** id) >>>> assocr×
eqH₂ = copyH >>>> swap ≈ copyH
eqH₃ = copyH >>>> invSE copyH ≈ id
eqH₄ = (copyH *** id) >>>> (id *** copyH) ≈ (id *** copyH) >>>> (copyH *** id)

eqZH : Set
eqZH = (copyZ *** id) >>>> (id *** (invSE copyH)) >>>> (id *** copyH) >>>> ((invSE copyZ) *** id) ≈ id

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
