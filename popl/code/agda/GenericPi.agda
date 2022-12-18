{-# OPTIONS --without-K --exact-split --safe #-}

module GenericPi where

open import Data.Float as F using (Float)
open import Data.Product as Prod using (_,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)

open import PiSyntax using (U; I; O; _+ᵤ_; _×ᵤ_; 𝟚)
open import PiTagless using (Pi)
open import Unitary using (𝒰)

-----------------------------------------------------------------------
-- This interpretation is "generic" in the sense that it works over an
-- arbitrary basis of 𝒰.

Fwd : U → U → Set
Fwd t₁ t₂ = 𝒰 t₁ → 𝒰 t₂

-- The interpretations pretty much follow the types. The only tricky one is for product,
-- which implements the Kronecker product.
GenericPi : Pi Fwd
GenericPi = record
  { unite+l = λ f → f ∘ inj₂
  ; uniti+l = λ {f (inj₂ x) → f x }
  ; unite*l = λ f x → f (tt , x)
  ; uniti*l = λ f x → f (Prod.proj₂ x)
  ; swap+ = λ f → f ∘ Sum.swap
  ; swap× = λ f → f ∘ Prod.swap
  ; assocl+ = λ f → f ∘ Sum.assocʳ
  ; assocr+ = λ f → f ∘ Sum.assocˡ
  ; assocl* = λ f → f ∘ Prod.assocʳ
  ; assocr* = λ f → f ∘ Prod.assocˡ
  ; absorbl′ = λ { _ () }
  ; factorzr′ = λ {_ ( _ , () )}
  ; dist′ = λ f → f ∘ Sum.[ Prod.map₁ inj₁ , Prod.map₁ inj₂ ]
  ; factor′ = λ f → f ∘ λ { (a , b) → Sum.map (_, b) (_, b) a }
  ; idp = λ x → x
  ; _⊚_ = λ f g → g ∘ f
  ; _⊕′_ = λ f g h → Sum.[ f (h ∘ inj₁) , g (h ∘ inj₂) ]
  ; _⊛_ = λ A₁₃ B₂₄ v (i , j) → A₁₃ (λ a → B₂₄ (λ b → v (a , b)) j) i
  }

-- Note that this definition has to be coherent with 𝕋 and 𝔽 in PiSyntax
true false : 𝒰 𝟚
true (inj₁ y) = 0.0
true (inj₂ x) = 1.0
false (inj₁ y) = 1.0
false (inj₂ x) = 0.0

