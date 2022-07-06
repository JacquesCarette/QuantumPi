{-# OPTIONS --without-K --exact-split --safe #-}

-- Lifting an abstract list over a pair of representations.

module StatesAndEffects where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)

open import PiSyntax
open import PiBij using (enum; ⟦_⟧)
open import GenericList as GL using (TList)
import ArrowsOverPair as A
open A using (_>>>_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-------------------------------------------------------------------------------------

-- This is the type of non-trivial Ancillas
data Anc : Set where
  Two : Anc
  _×ₙ_ : Anc → Anc → Anc

N : Set
N = Maybe Anc

-- Inject N into U
N⇒U : N → U
N⇒U nothing = I
N⇒U (just Two) = I +ᵤ I
N⇒U (just (x ×ₙ y)) = N⇒U (just x) ×ᵤ N⇒U (just y)

enumN : (n : N) → List ⟦ N⇒U n ⟧
enumN n = enum (N⇒U n)

-- Lifting an abstract pair
data StEffPi : U → U → Set where
  lift : {n₁ n₂ : N} → TList (N⇒U n₁ ×ᵤ t₁) (N⇒U n₂ ×ᵤ t₂) → StEffPi t₁ t₂

-- And now define the rest of the language
-- We actually do it 2 ways (and later show coherence)

-- First method: Direct, where it's done by translation to explicit TList
module Direct where
  -- First arr.
  arr : TList t₁ t₂ → StEffPi t₁ t₂
  arr c = lift {n₁ = nothing} {nothing} (A.unite*l >>> c >>> A.uniti*l)

  -- Then use that to lift id, swap, assoc and unit
  idst : StEffPi t t
  idst = arr A.idzh
  swap : StEffPi (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
  swap = arr A.swap×
  assocl× : StEffPi  (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ((t₁ ×ᵤ t₂) ×ᵤ t₃)
  assocl× = arr A.assocl×
  assocr× : StEffPi  ((t₁ ×ᵤ t₂) ×ᵤ t₃) (t₁ ×ᵤ (t₂ ×ᵤ t₃))
  assocr× = arr A.assocr×
  unite*l : StEffPi (I ×ᵤ t) t
  unite*l = arr A.unite*l
  uniti*l : StEffPi t (I ×ᵤ t)
  uniti*l = arr A.uniti*l

  a* : N → N → N
  a* (just x) (just y) = just (x ×ₙ y)
  a* (just x) nothing = just x
  a* nothing (just x) = just x
  a* nothing nothing = nothing

  unpack : (n₁ n₂ : N) → N⇒U (a* n₁ n₂) ⟷₁ N⇒U n₁ ×ᵤ N⇒U n₂
  unpack (just x) (just y) = id⟷₁
  unpack (just x) nothing = uniti⋆r
  unpack nothing (just x) = uniti⋆l
  unpack nothing nothing = uniti⋆l

  -- >>>< composition
  infixr 10 _>>>>_
  _>>>>_ : StEffPi t₁ t₂ → StEffPi t₂ t₃ → StEffPi t₁ t₃
  lift {n₁ = n₁} {n₂} m >>>> lift {n₁ = n₃} {n₄} p =
    lift {n₁ = a* n₃ n₁} {a* n₂ n₄} (GL.first (A.arr₁ (unpack n₃ n₁)) >>>
      A.assocr× >>> A.second m >>> A.assocl× >>> GL.first A.swap× >>> A.assocr× >>> A.second p >>> A.assocl×
      >>> GL.first (A.arr₁ (!⟷₁ (unpack n₂ n₄)))
      )

  -- first
  firstSE : StEffPi t₁ t₂ → StEffPi (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)
  firstSE (lift m) = lift (A.assocl× >>> GL.first m >>> A.assocr×)

  -- second and ***
  secondSE : StEffPi t₁ t₂ → StEffPi (t₃ ×ᵤ t₁) (t₃ ×ᵤ t₂)
  secondSE c = swap >>>> firstSE c >>>> swap

  _***_ : StEffPi t₁ t₂ → StEffPi t₃ t₄ → StEffPi (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₄)
  xs *** ys = firstSE xs >>>> secondSE ys

  -- inverse
  invSE : StEffPi t₁ t₂ → StEffPi t₂ t₁
  invSE (lift m) = lift (A.inv′ m)

  -- Some examples where we use all of the above
  -- With annotations
  zero : StEffPi I (I +ᵤ I)
  zero = lift (A.arr₁ swap⋆)

  assertZero : StEffPi (I +ᵤ I) I
  assertZero = lift (A.arr₁ swap⋆)

  -- Sanity check
  inv0 : invSE zero ≡ assertZero
  inv0 = refl
