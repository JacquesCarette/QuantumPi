{-# OPTIONS --without-K --exact-split --safe #-}

module PiExamples where

open import PiSyntax using (U; I;  _+ᵤ_; _×ᵤ_)
open import PiTagless using (Pi)

private
  variable
    t t₁ t₂ t₃ t₄ t₅ : U

-- These examples are completely generic, i.e. for any interpretation
module _ {rep : U → U → Set} (p : Pi rep) where
  open Pi p

  x : rep (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
  x = swap+

  -- cx is sometimes called cnot too
  cx : rep ((t₁ +ᵤ t₂) ×ᵤ (t₃ +ᵤ t₃) ) ((t₁ +ᵤ t₂) ×ᵤ (t₃ +ᵤ t₃))
  cx = dist′ ⊚ (idp ⊕′ (idp ⊛ x)) ⊚ factor′

  -- note how c has to be an automorphism
  ctrl : rep t₃ t₃ → rep ((t₁ +ᵤ t₄) ×ᵤ t₃) ((t₁ +ᵤ t₄) ×ᵤ t₃)
  ctrl c = dist′ ⊚ (idp ⊛ c ⊕′ idp) ⊚ factor′

  -- ccx is also known as the Toffoli gate
  ccx : rep ((t₁ +ᵤ t₂) ×ᵤ ((t₃ +ᵤ t₄) ×ᵤ (t₅ +ᵤ t₅)))
                ((t₁ +ᵤ t₂) ×ᵤ ((t₃ +ᵤ t₄) ×ᵤ (t₅ +ᵤ t₅)))
  ccx = ctrl cx
