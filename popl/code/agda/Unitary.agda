{-# OPTIONS --without-K --exact-split --safe #-}

-- Define Unitary and a particular automorphism

module Unitary where

open import Data.Float as F using (Float; cos; sin; _÷_; _*_; _+_; -_; _-_)
open import Data.List using (List; foldr; map)
import Data.Nat as ℕ
open ℕ using (ℕ; _>_)
import Data.Product as Prod
open Prod using (_,_; Σ)
import Data.Sum as Sum
open Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_; id)

open import PiSyntax as Pi hiding (_⊕_; _⊗_)
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

private
  -- make it clearer that this is direct product.
  _⊕_ : {t₁ t₂ : U} → Aut (𝒰 t₁) → Aut (𝒰 t₂) → Aut (𝒰 (t₁ +ᵤ t₂))
  -- simple definition:
  -- c₁ ⊕ c₂ = λ f → Sum.[ c₁ (f ∘ inj₁) , c₂ (f ∘ inj₂) ]
  -- expanded:
  (c₁ ⊕ c₂) f (inj₁ x) = c₁ (f ∘ inj₁) x
  (c₁ ⊕ c₂) f (inj₂ y) = c₂ (f ∘ inj₂) y

  _⊗_ : {t₁ t₂ : U} → Aut (𝒰 t₁) → Aut (𝒰 t₂) → Aut (𝒰 (t₁ ×ᵤ t₂))
  _⊗_ {t₁} {t₂} c₁ c₂ f (v₁ , v₂) =
    c₁ (λ a → sumf (map (λ z → f ( a , z)) (enum t₂))) v₁ F.*
    c₂ (λ c → sumf (map (λ z → f ( z , c)) (enum t₁))) v₂

size : U → ℕ
size O = 0
size I = 1
size (u +ᵤ v) = size u ℕ.+ size v
size (u ×ᵤ v) = size u ℕ.* size v

fromSize : ℕ → U
fromSize ℕ.zero = O
fromSize (ℕ.suc n) = I +ᵤ fromSize n

canonicalU : U → U
canonicalU = fromSize ∘ size

size+ : (n₁ n₂ : ℕ) → (fromSize n₁) +ᵤ (fromSize n₂) ⟷₁ fromSize (n₁ ℕ.+ n₂)
size+ ℕ.zero n₂ = unite₊l
size+ (ℕ.suc n₁) n₂ = assocr₊ ◎ id⟷₁ Pi.⊕ size+ n₁ n₂

size* : (n₁ n₂ : ℕ) → (fromSize n₁) ×ᵤ (fromSize n₂) ⟷₁ fromSize (n₁ ℕ.* n₂)
size* ℕ.zero n₂ = absorbr
size* (ℕ.suc n₁) n₂ = dist ◎ (unite⋆l Pi.⊕ size* n₁ n₂) ◎ size+ n₂ (n₁ ℕ.* n₂)

normalizeC : (t : U) → t ⟷₁ canonicalU t
normalizeC O = id⟷₁
normalizeC I  = uniti₊l ◎ swap₊
normalizeC (t₀ +ᵤ t₁) =
  (normalizeC t₀ Pi.⊕ normalizeC t₁) ◎ size+ (size t₀) (size t₁)
normalizeC (t₀ ×ᵤ t₁) =
  (normalizeC t₀ Pi.⊗ normalizeC t₁) ◎ size* (size t₀) (size t₁)

-- Family R from Definition 6 in Section 4.3
-- It is more complicated here because inequations are not constructive.
-- Note that we use v below to choose which *row* we're in.
R : (x : U) → Aut (𝒰 x)
R O = id
R I = id
R (O +ᵤ y) = R O ⊕ R y
R (I +ᵤ O) = R I ⊕ R O
R (I +ᵤ I) = λ f v → Sum.[ (λ _ →  cπ/8 * f (inj₁ tt) - sπ/8 * f (inj₂ tt)) ,
                           (λ _ →  sπ/8 * f (inj₁ tt) + cπ/8 * f (inj₂ tt)) ] v
R (I +ᵤ z@(y +ᵤ y′)) = R I ⊕ R z
R (I +ᵤ z@(y ×ᵤ y′)) = R I ⊕ R z
R (z@(x +ᵤ x′) +ᵤ y) = R z ⊕ R y
R (z@(x ×ᵤ x′) +ᵤ y) = R z ⊕ R y
R (x ×ᵤ y) = R x ⊗ R y

-- Simpler to define R⁻¹ explicitly
R⁻¹ : (x : U) → Aut (𝒰 x)
R⁻¹ O = id
R⁻¹ I = id
R⁻¹ (O +ᵤ y) = R⁻¹ O ⊕ R⁻¹ y
R⁻¹ (I +ᵤ O) = R⁻¹ I ⊕ R⁻¹ O
R⁻¹ (I +ᵤ I) = λ f v → Sum.[ (λ _ →     cπ/8 * f (inj₁ tt)  + sπ/8 * f (inj₂ tt)) ,
                             (λ _ →  - (sπ/8 * f (inj₁ tt)) + cπ/8 * f (inj₂ tt)) ] v
R⁻¹ (I +ᵤ z@(y +ᵤ y′)) = R⁻¹ I ⊕ R⁻¹ z
R⁻¹ (I +ᵤ z@(y ×ᵤ y′)) = R⁻¹ I ⊕ R⁻¹ z
R⁻¹ (z@(x +ᵤ x′) +ᵤ y) = R⁻¹ z ⊕ R⁻¹ y
R⁻¹ (z@(x ×ᵤ x′) +ᵤ y) = R⁻¹ z ⊕ R⁻¹ y
R⁻¹ (x ×ᵤ y) = R⁻¹ x ⊗ R⁻¹ y
