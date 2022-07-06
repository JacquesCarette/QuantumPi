{-# OPTIONS --without-K --exact-split --safe #-}

-- Lifting an abstract list over a pair of representations.

module StatesAndEffects where

open import PiSyntax
open import GenericList
import ArrowsOverPair as A
open A using (_>>>_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-------------------------------------------------------------------------------------

-- This is the type of Ancillas
data N : Set where
  I′ : N
  Two : N
  _×ₙ_ : N → N → N

-- Inject N into U
N⇒U : N → U
N⇒U I′ = I
N⇒U Two = I +ᵤ I
N⇒U (x ×ₙ y) = N⇒U x ×ᵤ N⇒U y

-- Lifting an abstract pair
data StEffPi : U → U → Set where
  lift : {n₁ n₂ : N} → TList (N⇒U n₁ ×ᵤ t₁) (N⇒U n₂ ×ᵤ t₂) → StEffPi t₁ t₂

-- And now define the rest of the language
-- First arr.
arr : TList t₁ t₂ → StEffPi t₁ t₂
arr c = lift (A.unite*l >>> c >>> A.uniti*l)

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

-- >>>< composition
infixr 10 _>>>>_
_>>>>_ : StEffPi t₁ t₂ → StEffPi t₂ t₃ → StEffPi t₁ t₃
lift m >>>> lift p =
  lift (A.assocr× >>> A.second m >>> A.assocl× >>> first A.swap× >>> A.assocr× >>> A.second p >>> A.assocl×)

-- first
firstSE : StEffPi t₁ t₂ → StEffPi (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)
firstSE (lift m) = lift (A.assocl× >>> first m >>> A.assocr×)

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

-- A function is an Interpreter when:
Interpreter : (rep : U → U → Set) → Set
Interpreter rep = ∀ {t₁ t₂} → StEffPi t₁ t₂ → rep t₁ t₂
