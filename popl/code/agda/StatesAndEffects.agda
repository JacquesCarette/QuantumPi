{-# OPTIONS --without-K --exact-split --safe #-}

-- Lifting an abstract list over a pair of representations.

module StatesAndEffects where

open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Pi.Types using (U; I; _+ᵤ_; _×ᵤ_; 𝟚)
open import Pi.Language using (_⟷_; !⟷)
open import Ancillae
open import Amalgamation using (TList; cons₁)
import ArrowsOverAmalg as A
open A using (_>>>_)
import Arrows.Terms as AT

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ : U

infixr 30 _↭_

-- Lifting an abstract pair
data _↭_ : U → U → Set where
  lift : {n₁ n₂ : N} → TList (t₁ ×ᵤ N⇒U n₁) (t₂ ×ᵤ N⇒U n₂) → t₁ ↭ t₂

-- And now define the rest of the language
-- lifting:
arr : TList t₁ t₂ → t₁ ↭ t₂
arr c = lift {n₁ = nothing} {nothing} (A.unite* >>> c >>> A.uniti*)

-- Then use that to lift id, swap, assoc and unit
id : t ↭ t
id = arr A.id
swap : (t₁ ×ᵤ t₂) ↭ (t₂ ×ᵤ t₁)
swap = arr A.swap×
assocl× :  (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ↭ ((t₁ ×ᵤ t₂) ×ᵤ t₃)
assocl× = arr A.assocl×
assocr× :  ((t₁ ×ᵤ t₂) ×ᵤ t₃) ↭ (t₁ ×ᵤ (t₂ ×ᵤ t₃))
assocr× = arr A.assocr×
unite*l : (I ×ᵤ t) ↭ t
unite*l = arr A.unite*l
uniti*l : t ↭ (I ×ᵤ t)
uniti*l = arr A.uniti*l
unite*  : (t ×ᵤ I) ↭ t
unite*  = arr A.unite*
uniti*  : t ↭ (t ×ᵤ I)
uniti*  = arr A.uniti*

-- >>>> composition.
-- Note how we have to unpack & pack up the ancillas
-- This is needed to move between the types (and elided in the paper version)
infixr 10 _>>>>_
_>>>>_ : t₁ ↭ t₂ → t₂ ↭ t₃ → t₁ ↭ t₃
lift {n₁ = n₁} {n₂} m >>>> lift {n₁ = n₃} {n₄} p =
  lift {n₁ = a* n₁ n₃} {a* n₄ n₂}
   (A.second (A.arr₁ (unpack n₁ n₃)) >>>
    A.assocl× >>>
    A.first m >>>
    A.assocr× >>>
    A.second A.swap× >>>
    A.assocl× >>>
    A.first p >>>
    A.assocr× >>>
    A.second (A.arr₁ (!⟷ (unpack n₄ n₂)))
   )

-- first
-- Note how we don't use >>> twice, as that would do 2 full traversals
firstSE : t₁ ↭ t₂ → (t₁ ×ᵤ t₃) ↭ (t₂ ×ᵤ t₃)
firstSE (lift m) = lift
   (A.assocr× >>>
    A.second A.swap× >>>
    A.assocl× >>>
    A.first m >>>
    A.assocr× >>>
    A.second A.swap× >>>
    A.assocl×
   )

-- second and ***
secondSE : t₁ ↭ t₂ → (t₃ ×ᵤ t₁) ↭ (t₃ ×ᵤ t₂)
-- it is inefficient to do 3 passes, but quite difficult to do otherwise
-- as the swaps are needed.
secondSE c = swap >>>> firstSE c >>>> swap

-- This is likewise inefficient
_***_ : t₁ ↭ t₂ → t₃ ↭ t₄ → (t₁ ×ᵤ t₃) ↭ (t₂ ×ᵤ t₄)
xs *** ys = firstSE xs >>>> secondSE ys

-- inverse
invSE : t₁ ↭ t₂ → t₂ ↭ t₁
invSE (lift m) = lift (A.inv m)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
