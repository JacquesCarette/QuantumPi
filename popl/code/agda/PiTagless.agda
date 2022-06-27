{-# OPTIONS --without-K --exact-split --safe #-}

module PiTagless where

open import PiSyntax using (U; I; O; _+ᵤ_; _×ᵤ_)

-------------------------------------------------------------------------------------

private
  variable
    t t₁ t₂ t₃ t₄ : U

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
    absorbr′ : rep (O ×ᵤ t) O
    absorbl′ : rep (t ×ᵤ O) O
    factorzr′ : rep O (t ×ᵤ O)
    factorzl′ : rep O (O ×ᵤ t)
    dist′ : rep ((t₁ +ᵤ t₂) ×ᵤ t₃) ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃))
    distl′ : rep (t₃ ×ᵤ (t₁ +ᵤ t₂)) ((t₃ ×ᵤ t₁) +ᵤ (t₃ ×ᵤ t₂))
    factor′ : rep ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)) ((t₁ +ᵤ t₂) ×ᵤ t₃)
    factorl′ : rep ((t₃ ×ᵤ t₁) +ᵤ (t₃ ×ᵤ  t₂)) (t₃ ×ᵤ (t₁ +ᵤ t₂))
    idp : rep t t
    _⊚_ : rep t₁ t₂ → rep t₂ t₃ → rep t₁ t₃
    _⊕′_ : rep t₁ t₃ → rep t₂ t₄ → rep (t₁ +ᵤ t₂) (t₃ +ᵤ t₄)
    _⊛_ : rep t₁ t₃ → rep t₂ t₄ → rep (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄)

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
  ; absorbr′ = factorzl′
  ; absorbl′ = factorzr′
  ; factorzr′ = absorbl′
  ; factorzl′ = absorbr′
  ; dist′ = factor′
  ; distl′ = factorl′
  ; factor′ = dist′
  ; factorl′ = distl′
  ; idp = idp
  ; _⊚_ = λ f g → g ⊚ f
  ; _⊕′_ = _⊕′_
  ; _⊛_ = _⊛_
  }
  where open Pi p
