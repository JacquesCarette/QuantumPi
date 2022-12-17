{-# OPTIONS --without-K --exact-split --safe #-}

-- Lifting an abstract list over a pair of representations.

module StatesAndEffects where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiSyntax
open import Amalgamation using (TList; cons₁)
import ArrowsOverAmalg as A
open A using (_>>>_)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-------------------------------------------------------------------------------------
-- Ancillae

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
  lift : {n₁ n₂ : N} → TList (t₁ ×ᵤ N⇒U n₁) (t₂ ×ᵤ N⇒U n₂) → StEffPi t₁ t₂

-- And now define the rest of the language
-- lifting:
arr : TList t₁ t₂ → StEffPi t₁ t₂
arr c = lift {n₁ = nothing} {nothing} (A.unite* >>> c >>> A.uniti*)

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
unite*  : StEffPi (t ×ᵤ I) t
unite*  = arr A.unite*
uniti*  : StEffPi t (t ×ᵤ I)
uniti*  = arr A.uniti*

-- Combining ancillas, i.e. product of ancillas
a* : N → N → N
a* (just x) (just y) = just (x ×ₙ y)
a* (just x) nothing = just x
a* nothing (just x) = just x
a* nothing nothing = nothing

-- "unpack" a product of ancillas (including none) into a proper product
unpack : (n₁ n₂ : N) → N⇒U (a* n₁ n₂) ⟷ N⇒U n₁ ×ᵤ N⇒U n₂
unpack (just x) (just y) = id⟷
unpack (just x) nothing = uniti⋆r
unpack nothing (just x) = uniti⋆l
unpack nothing nothing = uniti⋆l

-- >>>> composition.
-- Note how we have to unpack & pack up the ancillas
-- This is needed to move between the types (and elided in the paper version)
infixr 10 _>>>>_
_>>>>_ : StEffPi t₁ t₂ → StEffPi t₂ t₃ → StEffPi t₁ t₃
lift {n₁ = n₁} {n₂} m >>>> lift {n₁ = n₃} {n₄} p =
  lift {n₁ = a* n₁ n₃} {a* n₄ n₂} (A.second (A.arr₁ (unpack n₁ n₃)) >>>
    A.assocl× >>> A.first m >>> A.assocr× >>> A.second A.swap× >>> A.assocl× >>> A.first p >>> A.assocr×
    >>> A.second (A.arr₁ (!⟷ (unpack n₄ n₂)))
    )

-- first
-- Note how we don't use >>> twice, as that would do 2 full traversals
firstSE : StEffPi t₁ t₂ → StEffPi (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)
firstSE (lift m) = lift (cons₁ assocr⋆ (A.second A.swap× >>> A.assocl× >>> A.first m >>> A.assocr× >>> A.second A.swap× >>> A.assocl×))

-- second and ***
secondSE : StEffPi t₁ t₂ → StEffPi (t₃ ×ᵤ t₁) (t₃ ×ᵤ t₂)
-- it is inefficient to do 3 passes, but quite difficult to do otherwise
-- as the swaps are needed.
secondSE c = swap >>>> firstSE c >>>> swap

-- This is likewise inefficient
_***_ : StEffPi t₁ t₂ → StEffPi t₃ t₄ → StEffPi (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₄)
xs *** ys = firstSE xs >>>> secondSE ys

-- inverse
invSE : StEffPi t₁ t₂ → StEffPi t₂ t₁
invSE (lift m) = lift (A.inv m)

-------------------------------------------------------------------------------------
-- Some examples where we use all of the above

-- With annotations
zero : StEffPi I (I +ᵤ I)
zero = lift (A.arr₁ swap⋆)

assertZero : StEffPi (I +ᵤ I) I
assertZero = lift (A.arr₁ swap⋆)

-- Sanity check
inv0 : invSE zero ≡ assertZero
inv0 = refl

-- Additional combinators for complementarity

X : StEffPi (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
X = arr A.X

CX : StEffPi (𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚)
CX = arr A.CX

CCX : StEffPi (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚)
CCX = arr A.CCX

H : StEffPi (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
H = arr A.H

Z : StEffPi (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
Z = arr A.Z

CZ : StEffPi (𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚)
CZ = arr A.CZ

copyZ : StEffPi 𝟚 (𝟚 ×ᵤ 𝟚)
copyZ = uniti* >>>> idst *** zero >>>> arr A.CX

copyH : StEffPi 𝟚 (𝟚 ×ᵤ 𝟚)
copyH = H >>>> copyZ >>>> H *** H

--------------------------------------------
-- complementarity equations

-- Define this equivalence for display purposes, and hack it to be ≡ for now,
-- until a proper equivalence can be defined.

infix 4 _≈_

_≈_ : StEffPi t₁ t₂ → StEffPi t₁ t₂ → Set
_≈_ x y = x ≡ y

-- Just typecheck them
eqZ₁ eqZ₂ eqZ₃ eqZ₄ : Set
eqZ₁ = copyZ >>>> (idst *** copyZ) ≈ copyZ >>>> (copyZ *** idst) >>>> assocr×
eqZ₂ = copyZ >>>> swap ≈ copyZ
eqZ₃ = copyZ >>>> invSE copyZ ≈ idst
eqZ₄ = (copyZ *** idst) >>>> (idst *** copyZ) ≈ (idst *** copyZ) >>>> (copyZ *** idst)

eqH₁ eqH₂ eqH₃ eqH₄ : Set
eqH₁ = copyH >>>> (idst *** copyH) ≈ copyH >>>> (copyH *** idst) >>>> assocr×
eqH₂ = copyH >>>> swap ≈ copyH
eqH₃ = copyH >>>> invSE copyH ≈ idst
eqH₄ = (copyH *** idst) >>>> (idst *** copyH) ≈ (idst *** copyH) >>>> (copyH *** idst)

eqZH : Set
eqZH = (copyZ *** idst) >>>> (idst *** (invSE copyH)) >>>> (idst *** copyH) >>>> ((invSE copyZ) *** idst) ≈ idst

-- Special states and effects

one : StEffPi I 𝟚
one = zero >>>> X
plus : StEffPi I 𝟚
plus = zero >>>> H
minus : StEffPi I 𝟚
minus = plus >>>> Z

assertOne : StEffPi 𝟚 I
assertOne = X >>>> assertZero
assertPlus : StEffPi 𝟚 I
assertPlus = H >>>> assertZero
assertMinus : StEffPi 𝟚 I
assertMinus = Z >>>> assertZero

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
