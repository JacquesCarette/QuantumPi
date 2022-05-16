{-# OPTIONS --without-K --exact-split --rewriting #-}

module PiX where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Function using (_∘_)

open import PiSyntax
open import PiZ

-------------------------------------------------------------------------------------
-- Walsh functions as denotations

data PMOne : Set where
  One : PMOne
  MinusOne : PMOne

mul : PMOne → PMOne → PMOne
mul One One = One
mul One MinusOne = MinusOne
mul MinusOne One = MinusOne
mul MinusOne MinusOne = One

⟦_⟧x : (t : U) → Set
⟦ t ⟧x = ⟦ t ⟧z → PMOne

𝟚 : U
𝟚 = I +ᵤ I

walsh0 : ⟦ 𝟚 ⟧x
walsh0 _ = One

walsh1 : ⟦ 𝟚 ⟧x
walsh1 (inj₁ tt) = One
walsh1 (inj₂ tt) = MinusOne

_**_ : { t₁ t₂ : U } → ⟦ t₁ ⟧x → ⟦ t₂ ⟧x → ⟦ (t₁ ×ᵤ t₂ ) ⟧x
(w₁ ** w₂) (v₁ , v₂) = mul (w₁ v₁) (w₂ v₂)

lift : { t₁ t₂ : U } → (⟦ t₁ ⟧z → ⟦ t₂ ⟧z) → (⟦ t₂ ⟧x → ⟦ t₁ ⟧x)
lift bf w = w ∘ bf

-- Examples

xgate : ⟦ 𝟚 ⟧x → ⟦ 𝟚 ⟧x
xgate = lift (eval swap₊)

-- xgate walsh0 ==> λ x → One
-- xgate walsh1 (inj₁ tt) ==> MinusOne
-- xgate walsh1 (inj₂ tt) ==> One


-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
