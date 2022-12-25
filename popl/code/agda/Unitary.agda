{-# OPTIONS --without-K --exact-split --safe #-}

-- Define Unitary and a particular automorphism

module Unitary where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; id)

open import LinearAlgebraSig using (LASig)
open import AbstractRotation using (RotMat)
open import Pi.Types using (U; O; I; _+ᵤ_; _×ᵤ_; ⟦_⟧)

UVec : (L : LASig) (t : U) → Set
UVec L t = LASig.vec L ⟦ t ⟧

module Build (L : LASig) (RM : RotMat L) where
  open LASig L using (vec; aut; _⊕_; _⊗_)
  open RotMat RM

  {-

  -}
  
  -- Family R from Definition 6 in Section 4.3
  -- It is more complicated here because inequations are not constructive.
  -- Note that we use v below to choose which *row* we're in.
  -- This definition also assumes 'x' is in normal form, i.e. contains no
  -- occurences of "O +ᵤ _", "I ×ᵤ _" (or its symmetric form).
  R : (x : U) → aut ⟦ x ⟧
  R O = id
  R I = id
  R (O +ᵤ y) = R O ⊕ R y
  R (I +ᵤ O) = R I ⊕ R O
  R (I +ᵤ I) = Rω
  R (I +ᵤ z@(y +ᵤ y′)) = R I ⊕ R z
  R (I +ᵤ z@(y ×ᵤ y′)) = R I ⊕ R z
  R (z@(x +ᵤ x′) +ᵤ y) = R z ⊕ R y
  R (z@(x ×ᵤ x′) +ᵤ y) = R z ⊕ R y
  R (x ×ᵤ y) = R x ⊗ R y

  -- Simpler to define R⁻¹ explicitly
  R⁻¹ : (x : U) → aut ⟦ x ⟧
  R⁻¹ O = id
  R⁻¹ I = id
  R⁻¹ (O +ᵤ y) = R⁻¹ O ⊕ R⁻¹ y
  R⁻¹ (I +ᵤ O) = R⁻¹ I ⊕ R⁻¹ O
  R⁻¹ (I +ᵤ I) = Rω⁻¹
  R⁻¹ (I +ᵤ z@(y +ᵤ y′)) = R⁻¹ I ⊕ R⁻¹ z
  R⁻¹ (I +ᵤ z@(y ×ᵤ y′)) = R⁻¹ I ⊕ R⁻¹ z
  R⁻¹ (z@(x +ᵤ x′) +ᵤ y) = R⁻¹ z ⊕ R⁻¹ y
  R⁻¹ (z@(x ×ᵤ x′) +ᵤ y) = R⁻¹ z ⊕ R⁻¹ y
  R⁻¹ (x ×ᵤ y) = R⁻¹ x ⊗ R⁻¹ y
