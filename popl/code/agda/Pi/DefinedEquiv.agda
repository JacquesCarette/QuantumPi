{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module Pi.DefinedEquiv where

open import Pi.Language
open import Pi.Terms using (cx)
open import Pi.Equivalences -- take it all in, less trouble that way

-------------------------------------------------------------------------------------

-- Definable term
xcx : ((id⟷ ⊗ swap₊) ◎ cx) ⟷₂ (cx ◎ (id⟷ ⊗ swap₊))
xcx = 
  ((id⟷ ⊗ swap₊) ◎ cx)                                            ⟨ id⟷₂ ⟩
  ((id⟷ ⊗ swap₊) ◎ dist ◎ (id⟷ ⊕ id⟷ ⊗ swap₊) ◎ factor)           ⟨ {!!} ⟩
  (((id⟷ ⊕ id⟷) ⊗ swap₊) ◎ dist ◎ (id⟷ ⊕ id⟷ ⊗ swap₊) ◎ factor)   ⟨ {!!} ⟩
  ((((id⟷ ⊕ id⟷) ⊗ swap₊) ◎ dist) ◎ (id⟷ ⊕ id⟷ ⊗ swap₊) ◎ factor)  ⟨ {!!} ⟩
  (((dist ◎ ((id⟷ ⊗ swap₊) ⊕ (id⟷ ⊗ swap₊)))) ◎ (id⟷ ⊕ id⟷ ⊗ swap₊) ◎ factor) ⟨ {!!} ⟩
  (dist ◎ (((id⟷ ⊗ swap₊) ⊕ (id⟷ ⊗ swap₊)) ◎ (id⟷ ⊕ id⟷ ⊗ swap₊)) ◎ factor)   ⟨ {!!} ⟩
  -- (dist ◎ (((id⟷ ⊗ swap₊) ◎ id⟷) ⊕ ((id⟷ ⊗ swap₊) ◎ (id⟷ ⊗ swap₊))) ◎ factor) ⟨ {!!} ⟩
  ((dist ◎ (id⟷ ⊕ id⟷ ⊗ swap₊) ◎ factor) ◎ (id⟷ ⊗ swap₊))         ⟨ id⟷₂ ⟩
  (cx ◎ (id⟷ ⊗ swap₊)) ▤   

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

