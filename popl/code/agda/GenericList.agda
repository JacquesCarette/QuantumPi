{-# OPTIONS --without-K --exact-split --safe #-}

module GenericList where

open import PiSyntax using (U; _×ᵤ_; _⟷₁_; !⟷₁; _⊗_; id⟷₁)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U
    a b c d : U

infixr 10 _⊚⊚_

data TList : U → U → Set where
  nil : TList a a
  cons₁ : t₁ ⟷₁ t₂ → TList t₂ t₃ → TList t₁ t₃
  cons₂ : t₁ ⟷₁ t₂ → TList t₂ t₃ → TList t₁ t₃

_⊚⊚_ : {t₁ t₂ t₃ : U} → TList t₁ t₂ → TList t₂ t₃ → TList t₁ t₃
nil         ⊚⊚ z = z
(cons₁ x y) ⊚⊚ z = cons₁ x (y ⊚⊚ z)
(cons₂ x y) ⊚⊚ z = cons₂ x (y ⊚⊚ z)

first : {t₁ t₂ t₃ : U} → TList t₁ t₂ → TList (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)
first nil = nil
first (cons₁ x y) = cons₁ (x ⊗ id⟷₁) (first y)
first (cons₂ x y) = cons₂ (x ⊗ id⟷₁) (first y)

inv : {t₁ t₂ : U} → TList t₁ t₂ → TList t₂ t₁
inv nil          = nil
inv (cons₁ x xs) = inv xs ⊚⊚ (cons₁ (!⟷₁ x) nil)
inv (cons₂ x xs) = inv xs ⊚⊚ (cons₂ (!⟷₁ x) nil)

record Categorical (rep : U → U → Set) : Set where
  field
    idr : {t : U} → rep t t
    comp : {t₁ t₂ t₃ : U} → rep t₁ t₂ → rep t₂ t₃ → rep t₁ t₃

open Categorical

-- We have 2 different evaluators for the same interpretation, we can combine them
evalTL : {rep : U → U → Set} → Categorical rep → (∀ {t₁ t₂} → t₁ ⟷₁ t₂ → rep t₁ t₂) → (∀ {t₁ t₂} → t₁ ⟷₁ t₂ → rep t₁ t₂) → TList t₃ t₄ → rep t₃ t₄
evalTL c i₁ i₂ nil         = idr c
evalTL c i₁ i₂ (cons₁ x l) = comp c (i₁ x) (evalTL c i₁ i₂ l)
evalTL c i₁ i₂ (cons₂ x l) = comp c (i₂ x) (evalTL c i₁ i₂ l)
