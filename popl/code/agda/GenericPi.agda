{-# OPTIONS --without-K --exact-split --safe #-}

module GenericPi where

open import Pi.Types using (U; ⟦_⟧; 𝟚)
open import PiTagless using (Pi)
open import LinearAlgebraSig using (LASig)

-----------------------------------------------------------------------
-- This interpretation is "generic" in the sense that it works over an
-- arbitrary basis.

module _ (L : LASig) where

  private
    module LA = LASig L
    
  open LA using (linop; vec)
  
  Fwd : U → U → Set
  Fwd t₁ t₂ = linop ⟦ t₁ ⟧ ⟦ t₂ ⟧

  -- The interpretations pretty much follow the types. The only tricky one is for product,
  -- which implements the Kronecker product.
  GenericPi : Pi Fwd
  GenericPi = record { LA }


  true false : vec ⟦ 𝟚 ⟧
  true = LA.true
  false = LA.false
