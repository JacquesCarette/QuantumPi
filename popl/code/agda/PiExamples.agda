{-# OPTIONS --without-K --exact-split --safe #-}

module PiExamples where

open import PiSyntax
open import PiTagless

Bool : U
Bool = I +ᵤ I

private
  variable
    t t₁ t₂ t₃ t₄ t₅ : U

-- These examples are completely generic, i.e. for any interpretation
module _ {rep : U → U → Set} (p : Pi rep) where
  open Pi p

  not : rep (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
  not = swap+

  cnot : rep ((t₁ +ᵤ t₂) ×ᵤ (t₃ +ᵤ t₃) ) ((t₁ +ᵤ t₂) ×ᵤ (t₃ +ᵤ t₃))
  cnot = dist′ ⊚ (idp ⊕′ (idp ⊛ not)) ⊚ factor′

  -- note how c₂ has to be an automorphism
  cif : rep t₁ t₂ → rep t₃ t₃ → rep ((t₁ +ᵤ t₄) ×ᵤ t₃) ((t₂ +ᵤ t₄) ×ᵤ t₃)
  cif c₁ c₂ = dist′ ⊚ (c₁ ⊛ idp ⊕′ idp ⊛ c₂) ⊚ factor′

  toffoli : rep ((t₁ +ᵤ t₂) ×ᵤ ((t₃ +ᵤ t₄) ×ᵤ (t₅ +ᵤ t₅)))
                ((t₁ +ᵤ t₂) ×ᵤ ((t₃ +ᵤ t₄) ×ᵤ (t₅ +ᵤ t₅)))
  toffoli = cif idp cnot
            -- dist′ ⊚ ((idp ⊕′ (idp ⊛ cnot)) ⊚ factor′)
