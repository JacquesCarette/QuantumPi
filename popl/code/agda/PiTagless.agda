{-# OPTIONS --without-K --exact-split --safe #-}

module PiTagless where

open import PiSyntax 

-------------------------------------------------------------------------------------

private
  variable
    t t₁ t₂ t₃ t₄ : U

-- The basic language itself

record Pi (rep : U → U → Set) : Set where
  infixr 50 _⊚_ _⊛_

  field
    unite+l : rep (O +ᵤ t) t
    uniti+l : rep t (O +ᵤ t)
    unite*l : rep (I ×ᵤ t) t
    uniti*l : rep t (I ×ᵤ t)
    swap+ : rep (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
    swap× : rep (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
    assocl+ : rep  (t₁ +ᵤ (t₂ +ᵤ t₃)) ((t₁ +ᵤ t₂) +ᵤ t₃)
    assocr+ : rep  ((t₁ +ᵤ t₂) +ᵤ t₃) (t₁ +ᵤ (t₂ +ᵤ t₃))
    assocl* : rep  (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ((t₁ ×ᵤ t₂) ×ᵤ t₃)
    assocr* : rep  ((t₁ ×ᵤ t₂) ×ᵤ t₃) (t₁ ×ᵤ (t₂ ×ᵤ t₃))
    absorbl′ : rep (t ×ᵤ O) O
    factorzr′ : rep O (t ×ᵤ O)
    dist′ : rep ((t₁ +ᵤ t₂) ×ᵤ t₃) ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃))
    factor′ : rep ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)) ((t₁ +ᵤ t₂) ×ᵤ t₃)
    idp : rep t t
    _⊚_ : rep t₁ t₂ → rep t₂ t₃ → rep t₁ t₃
    _⊕′_ : rep t₁ t₃ → rep t₂ t₄ → rep (t₁ +ᵤ t₂) (t₃ +ᵤ t₄)
    _⊛_ : rep t₁ t₃ → rep t₂ t₄ → rep (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄)

-- And a witness that it's reversible

record PiR (rep : U → U → Set) : Set where
  field
    pi : Pi rep
    !_ : rep t₁ t₂ → rep t₂ t₁
  open Pi pi public

-- It's reversible

reverse : (rep : U → U → Set) → Pi rep → Pi (λ x y → rep y x)
reverse rep p = record
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

generalize : {t₁ t₂ : U} {rep : U → U → Set} → Pi rep → (t₁ ⟷₁ t₂) → rep t₁ t₂
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
generalize p id⟷₁ = Pi.idp p
generalize p (c ◎ c₁) = Pi._⊚_ p (generalize p c) (generalize p c₁)
generalize p (c ⊕ c₁) = Pi._⊕′_ p (generalize p c) (generalize p c₁)
generalize p (c ⊗ c₁) = Pi._⊛_ p (generalize p c) (generalize p c₁)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
