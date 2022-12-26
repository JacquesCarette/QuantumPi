{-# OPTIONS --without-K --exact-split --safe #-}

module Pi.SyntaxToTagless where

open import Pi.Types using (U)
open import Pi.Language -- all of it
open import Pi.Tagless

-------------------------------------------------------------------------------------

private
  variable
    t t₁ t₂ t₃ t₄ : U

-- Generalize the raw Pi Syntax

generalize : {t₁ t₂ : U} {_⇿_ : U → U → Set} → Pi _⇿_ → (t₁ ⟷ t₂) → t₁ ⇿ t₂
generalize p unite₊l = Pi.unite+l p
generalize p uniti₊l = Pi.uniti+l p
generalize p unite⋆l = Pi.unite*l p
generalize p uniti⋆l = Pi.uniti*l p
generalize p swap₊ = Pi.swap+ p
generalize p swap⋆ = Pi.swap× p
generalize p assocl₊ = Pi.assocl+ p
generalize p assocr₊ = Pi.assocr+ p
generalize p assocl⋆ = Pi.assocl* p
generalize p assocr⋆ = Pi.assocr* p
generalize p absorbl = Pi.absorbl′ p
generalize p factorzr = Pi.factorzr′ p
generalize p dist = Pi.dist′ p
generalize p factor = Pi.factor′ p
generalize p id⟷ = Pi.idp p
generalize p (c ◎ c₁) = Pi._⊚_ p (generalize p c) (generalize p c₁)
generalize p (c ⊕ c₁) = Pi._⊕′_ p (generalize p c) (generalize p c₁)
generalize p (c ⊗ c₁) = Pi._⊛_ p (generalize p c) (generalize p c₁)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
