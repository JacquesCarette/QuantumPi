{-# OPTIONS --without-K --exact-split --safe #-}

module GenericPi where

open import Pi.Types using (U; â¦_â§; ğ)
open import Pi.Tagless using (Pi)
open import LinearAlgebraSig using (LASig)

-----------------------------------------------------------------------
-- This interpretation is "generic" in the sense that it works over an
-- arbitrary basis.

module _ (L : LASig) where

  private
    module LA = LASig L
    
  open LA using (linop; vec)
  
  Fwd : U â U â Set
  Fwd tâ tâ = linop â¦ tâ â§ â¦ tâ â§

  -- The interpretations pretty much follow the types. The only tricky one is for product,
  -- which implements the Kronecker product.
  GenericPi : Pi Fwd
  GenericPi = record { LA }


  true false : vec â¦ ğ â§
  true = LA.true
  false = LA.false
