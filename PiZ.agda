{-# OPTIONS --without-K --exact-split --safe #-}

module PiZ where

open import Pi.Types using (U; ğ)
open import Pi.Language using (_â·_)
open import Pi.SyntaxToTagless using (generalize)
open import GenericPi using (Fwd; GenericPi)
open import Unitary using (UVec)
open import LinearAlgebraSig using (LASig)

module MkPiZ (L : LASig) where
  open LASig L using (true; false)
  
-----------------------------------------------------------------------
-- Below we start the work that correspoints to the Z interpretation

  -- An evaluator for Z can re-use GenericPi directly:
  evalZ : {tâ tâ : U} â tâ â· tâ â Fwd L tâ tâ
  evalZ {tâ} {tâ} c = generalize (GenericPi L) c

  trueZ falseZ : UVec L ğ
  trueZ = true
  falseZ = false
