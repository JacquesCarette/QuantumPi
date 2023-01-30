{-# OPTIONS --without-K --exact-split --safe #-}

module Pi.Types where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; cartesianProduct)
open import Data.Product as Prod using (_,_; _×_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

-------------------------------------------------------------------------------------
-- Types

data U : Set where
  O     : U
  I     : U
  _+ᵤ_  : U → U → U
  _×ᵤ_  : U → U → U

infixr 40 _+ᵤ_ _×ᵤ_

private
  variable
    t t₁ t₂ t₃ t₄ : U

-- Intended meaning
⟦_⟧ : (t : U) → Set
⟦ O ⟧ = ⊥
⟦ I ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

-- inhabitants of U have decidable equality
_≟_ : {t : U} → ⟦ t ⟧ → ⟦ t ⟧ → Bool
_≟_ {I} tt tt = true
_≟_ {t₁ +ᵤ t₂} (inj₁ v) (inj₁ w) = v ≟ w
_≟_ {t₁ +ᵤ t₂} (inj₁ v) (inj₂ w) = false
_≟_ {t₁ +ᵤ t₂} (inj₂ v) (inj₁ w) = false
_≟_ {t₁ +ᵤ t₂} (inj₂ v) (inj₂ w) = v ≟ w
_≟_ {t₁ ×ᵤ t₂} (v₁ , w₁) (v₂ , w₂) = v₁ ≟ v₂ ∧ w₁ ≟ w₂

-- we can enumerate our types
enum : (t : U) → List ⟦ t ⟧
enum O = []
enum I = tt ∷ []
enum (t₁ +ᵤ t₂) = map inj₁ (enum t₁) ++ map inj₂ (enum t₂)
enum (t₁ ×ᵤ t₂) = cartesianProduct (enum t₁) (enum t₂)

-------------------------------------------------------------------------------------
-- Common types that recur, give them abbreviations

𝟚 : U
𝟚 = I +ᵤ I

pattern 𝔽 = inj₁ tt
pattern 𝕋 = inj₂ tt
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
