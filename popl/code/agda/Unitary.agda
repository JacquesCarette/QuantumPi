{-# OPTIONS --without-K --exact-split --safe #-}

-- Define Unitary and a particular automorphism

module Unitary where

open import Data.Float as F using (Float; cos; sin; _÷_; _*_; _+_; -_)
open import Data.List using (List; foldr; map)
import Data.Product as Prod
open Prod using (_,_)
import Data.Sum as Sum
open Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_; id)

open import PiSyntax using (U; O; I; _+ᵤ_; _×ᵤ_; _⟷₁_)
open import PiBij using (⟦_⟧; enum)

π : Float
π = 3.1415926535

cπ/8 : Float
cπ/8 = cos (π ÷ 8.0)
sπ/8 : Float
sπ/8 = sin (π ÷ 8.0)

sumf : List Float → Float
sumf = foldr F._+_ (F.fromℕ 0)

𝒰 : (t : U) → Set
𝒰 t = ⟦ t ⟧ → Float

Aut : Set → Set
Aut X = X → X

_⊕_ : {t₁ t₂ : U} → Aut (𝒰 t₁) → Aut (𝒰 t₂) → Aut (𝒰 (t₁ +ᵤ t₂))
c₁ ⊕ c₂ = λ f → Sum.[ c₁ (f ∘ inj₁) , c₂ (f ∘ inj₂) ]

_⊗_ : {t₁ t₂ : U} → Aut (𝒰 t₁) → Aut (𝒰 t₂) → Aut (𝒰 (t₁ ×ᵤ t₂))
_⊗_ {t₁} {t₂} c₁ c₂ f (v₁ , v₂) =
  c₁ (λ a → sumf (map (λ z → f ( a , z)) (enum t₂))) v₁ F.*
  c₂ (λ c → sumf (map (λ z → f ( z , c)) (enum t₁))) v₂

-- Family R from Definition 6 in Section 4.3
-- It is more complicated here because inequations are not constructive.
R : (x : U) → Aut (𝒰 x)
R O = id
R I = id
R (O +ᵤ y) = R O ⊕ R y
R (I +ᵤ O) = R I ⊕ R O
R (I +ᵤ I) = λ f v → Sum.[ (λ _ →    cπ/8 * f (inj₁ tt)  + sπ/8 * f (inj₂ tt)) ,
                           (λ _ → - (sπ/8 * f (inj₁ tt)) + cπ/8 * f (inj₂ tt)) ] v
R (I +ᵤ z@(y +ᵤ y′)) = R I ⊕ R z
R (I +ᵤ z@(y ×ᵤ y′)) = R I ⊕ R z
R (z@(x +ᵤ x′) +ᵤ y) = R z ⊕ R y
R (z@(x ×ᵤ x′) +ᵤ y) = R z ⊕ R y
R (x ×ᵤ y) = R x ⊗ R y
