{-# OPTIONS --without-K --exact-split --safe #-}

module PiH where

open import Function using (_â_)

open import Pi.Types using (U; ð)
open import Pi.Language using (_â·_)
open import Pi.SyntaxToTagless using (generalize)
open import GenericPi using (Fwd; GenericPi)
open import Unitary using (UVec; module Build)
open import LinearAlgebraSig using (LASig)
open import AbstractRotation using (RotMat)

module MkPiH (L : LASig) (RM : RotMat L) where
  open LASig L using (true; false)
  open Build L RM using (R; Râ»Â¹)
  
  -----------------------------------------------------------------------
  -- An evaluator for H can re-use GenericPi and conjugate before/after:
  evalH : {tâ tâ : U} â tâ â· tâ â Fwd L tâ tâ
  evalH {tâ} {tâ} c = Râ»Â¹ tâ â generalize (GenericPi L) c â R tâ

  trueH falseH  : UVec L ð
  trueH =  Râ»Â¹ ð true
  falseH = Râ»Â¹ ð false

