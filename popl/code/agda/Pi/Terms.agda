{-# OPTIONS --without-K --exact-split --safe #-}

module Pi.Terms where

open import Pi.Types using (U; _×ᵤ_; 𝟚)
open import Pi.Language using (_⟷_; id⟷; _◎_; _⊕_; _⊗_; dist; factor; swap₊)

private
  variable
    t : U
    
-------------------------------------------------------------------------------------
-- Common terms

ctrl : t ⟷ t → (𝟚 ×ᵤ t) ⟷ (𝟚 ×ᵤ t)
ctrl c = dist ◎ (id⟷ ⊕ id⟷ ⊗ c) ◎ factor

cx : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
cx = ctrl swap₊

ccx : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
ccx = ctrl cx

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
