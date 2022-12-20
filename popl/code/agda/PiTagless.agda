{-# OPTIONS --without-K --exact-split --safe #-}

module PiTagless where

open import Pi.Types using (U; O; I; _+ᵤ_; _×ᵤ_)
open import Pi.Language -- all of it

-------------------------------------------------------------------------------------

private
  variable
    t t₁ t₂ t₃ t₄ : U

-- The basic language itself

record Pi (_⇿_ : U → U → Set) : Set where
  infixr 50 _⊚_ _⊛_

  field
    unite+l : (O +ᵤ t) ⇿ t
    uniti+l :  t ⇿ (O +ᵤ t)
    unite*l :  (I ×ᵤ t) ⇿ t
    uniti*l :  t ⇿ (I ×ᵤ t)
    swap+ :  (t₁ +ᵤ t₂) ⇿ (t₂ +ᵤ t₁)
    swap× :  (t₁ ×ᵤ t₂) ⇿ (t₂ ×ᵤ t₁)
    assocl+ :   (t₁ +ᵤ (t₂ +ᵤ t₃)) ⇿ ((t₁ +ᵤ t₂) +ᵤ t₃)
    assocr+ :   ((t₁ +ᵤ t₂) +ᵤ t₃) ⇿ (t₁ +ᵤ (t₂ +ᵤ t₃))
    assocl* :   (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ⇿ ((t₁ ×ᵤ t₂) ×ᵤ t₃)
    assocr* :   ((t₁ ×ᵤ t₂) ×ᵤ t₃) ⇿ (t₁ ×ᵤ (t₂ ×ᵤ t₃))
    absorbl′ :  (t ×ᵤ O) ⇿ O
    factorzr′ :  O ⇿ (t ×ᵤ O)
    dist′ :  ((t₁ +ᵤ t₂) ×ᵤ t₃) ⇿ ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃))
    factor′ :  ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)) ⇿ ((t₁ +ᵤ t₂) ×ᵤ t₃)
    idp :  t ⇿ t
    _⊚_ :  t₁ ⇿ t₂ →  t₂ ⇿ t₃ →  t₁ ⇿ t₃
    _⊕′_ :  t₁ ⇿ t₃ →  t₂ ⇿ t₄ →  (t₁ +ᵤ t₂) ⇿ (t₃ +ᵤ t₄)
    _⊛_ :  t₁ ⇿ t₃ →  t₂ ⇿ t₄ →  (t₁ ×ᵤ t₂) ⇿ (t₃ ×ᵤ t₄)

-- And a witness that it's reversible

record PiR (_⇿_ : U → U → Set) : Set where
  field
    pi : Pi _⇿_
    !_ :  t₁ ⇿ t₂ →  t₂ ⇿ t₁
  open Pi pi public

-- It's reversible

reverse : {_⇿_ : U → U → Set} → Pi _⇿_ → Pi (λ x y →  y ⇿ x)
reverse p = record
  { unite+l = uniti+l
  ; uniti+l = unite+l
  ; unite*l = uniti*l
  ; uniti*l = unite*l
  ; swap+ = swap+
  ; swap× = swap×
  ; assocl+ = assocr+
  ; assocr+ = assocl+
  ; assocl* = assocr*
  ; assocr* = assocl*
  ; absorbl′ = factorzr′
  ; factorzr′ = absorbl′
  ; dist′ = factor′
  ; factor′ = dist′
  ; idp = idp
  ; _⊚_ = λ f g → g ⊚ f
  ; _⊕′_ = _⊕′_
  ; _⊛_ = _⊛_
  }
  where open Pi p

-- Generalize the raw PiSyntax

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
