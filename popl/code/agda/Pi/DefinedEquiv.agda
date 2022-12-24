{-# OPTIONS --without-K --exact-split --safe #-}

module Pi.DefinedEquiv where

open import Pi.Types using (U)
open import Pi.Language
open import Pi.Terms using (x; cx)
open import Pi.Equivalences -- take it all in, less trouble that way
open import Pi.TermReasoning -- make it prettier

private
  variable
    t₁ t₂ t₃ t₄ : U
    
-------------------------------------------------------------------------------------

-- Definable terms
comm-in-⊕ : {a a′ : t₁ ⟷ t₁} {b : t₂ ⟷ t₃} {c : t₃ ⟷ t₄} → a ◎ a′ ⟷₂ a′ ◎ a →
  (a ⊕ b) ◎ (a′ ⊕ c) ⟷₂ (a′ ⊕ b) ◎ (a ⊕ c)
comm-in-⊕ {a = a} {a′} {b} {c} sw = begin
  (a ⊕ b) ◎ (a′ ⊕ c) ≈⟨ hom◎⊕⟷₂ ⟩
  (a ◎ a′) ⊕ (b ◎ c) ≈⟨ resp⊕⟷₂ sw id⟷₂ ⟩
  (a′ ◎ a) ⊕ (b ◎ c) ≈⟨ hom⊕◎⟷₂ ⟩
  (a′ ⊕ b) ◎ (a ⊕ c) ∎

id-comm : {c : t₁ ⟷ t₂} → c ◎ id⟷ ⟷₂ id⟷ ◎ c
id-comm = idr◎l ○ idl◎r

xcx : id⟷ ⊗ x ◎ cx ⟷₂ cx ◎ id⟷ ⊗ x
xcx = begin
  (id⟷ ⊗ x) ◎ cx                                              ≈⟨ id⟷₂ ⟩
  (id⟷ ⊗ x) ◎ dist ◎ (id⟷ ⊕ id⟷ ⊗ x) ◎ factor                 ≈⟨ split⊕-id⟷ ⟩⊗⟨id ⟩◎⟨id ⟩
  ((id⟷ ⊕ id⟷) ⊗ x) ◎ dist ◎ (id⟷ ⊕ id⟷ ⊗ x) ◎ factor         ≈⟨ assoc◎l ⟩
  (((id⟷ ⊕ id⟷) ⊗ x) ◎ dist) ◎ (id⟷ ⊕ id⟷ ⊗ x) ◎ factor       ≈⟨ dist⟷₂l ⟩◎⟨id ⟩
  (dist ◎ (id⟷ ⊗ x) ⊕ (id⟷ ⊗ x)) ◎ (id⟷ ⊕ id⟷ ⊗ x) ◎ factor   ≈⟨ assoc◎r ○ id⟩◎⟨ assoc◎l ⟩
  dist ◎ ((id⟷ ⊗ x) ⊕ (id⟷ ⊗ x) ◎ (id⟷ ⊕ id⟷ ⊗ x)) ◎ factor   ≈⟨ id⟩◎⟨ comm-in-⊕ id-comm ⟩◎⟨id  ⟩
  dist ◎ ((id⟷ ⊕ id⟷ ⊗ x) ◎ (id⟷ ⊗ x ⊕ id⟷ ⊗ x)) ◎ factor     ≈⟨ assoc◎l ○ (assoc◎l ⟩◎⟨id) ○ assoc◎r ⟩
  (dist ◎ (id⟷ ⊕ id⟷ ⊗ x)) ◎ (id⟷ ⊗ x ⊕ id⟷ ⊗ x) ◎ factor     ≈⟨ id⟩◎⟨ factor⟷₂l ⟩
  (dist ◎ (id⟷ ⊕ id⟷ ⊗ x)) ◎ factor ◎ (id⟷ ⊕ id⟷) ⊗ x         ≈⟨ id⟩◎⟨ id⟩◎⟨ id⟷⊕id⟷⟷₂ ⟩⊗⟨id ⟩
  (dist ◎ (id⟷ ⊕ id⟷ ⊗ x)) ◎ factor ◎ id⟷ ⊗ x                 ≈⟨ assoc◎l ○ assoc◎r ⟩◎⟨id ⟩ 
  (dist ◎ (id⟷ ⊕ id⟷ ⊗ x) ◎ factor) ◎ id⟷ ⊗ x                 ≈⟨ id⟷₂ ⟩
  (cx ◎ (id⟷ ⊗ x)) ∎

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

