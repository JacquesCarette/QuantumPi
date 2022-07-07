{-# OPTIONS --without-K --safe #-}

--Note: not exact-split here, that's too much of a pain
module Tests where

open import Data.Float using (Float)
open import Data.List using (List; _∷_; []; map)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiSyntax
open import PiBij using (⟦_⟧; enum; generalize)
import ArrowsOverPair as A
open import GenericList using (TList)
open import Instances using (evalTL₁)
import PiZ
import PiH
open import Simon using (simon₁; simon₂)
open import PiTagless using (Pi)
open import Unitary

-- Infrastructure for testing
show : {t : U} → (⟦ t ⟧ → Float) → List (⟦ t ⟧ × Float)
show {t} v = map (λ i → (i , v i)) (enum t)

-- Note: these tests are EVIL because they use the most brutal equality possible on the worst thing imaginable, i.e. Floats.

-- Test things in Amalgamated language
test-notH : show (evalTL₁ (A.arr₂ swap₊) PiH.trueH) ≡ (inj₁ tt , 0.3818376618201004) ∷ (inj₂ tt , 0.9192388155510836) ∷ []
test-notH = refl

test-id : show (evalTL₁ (A.idzh) PiH.trueH) ≡ (inj₁ tt , 0.92) ∷ (inj₂ tt , -0.38) ∷ []
test-id = refl

test-Had-true : show (evalTL₁ (A.arr₂ swap₊) PiZ.trueZ) ≡ (inj₁ tt , 0.7071067811706743) ∷ (inj₂ tt , 0.707106781202421) ∷ []
test-Had-true = refl

test-Had-false : show (evalTL₁ (A.arr₂ swap₊) PiZ.falseZ) ≡ (inj₁ tt , 0.707106781202421) ∷ (inj₂ tt , -0.7071067811706743) ∷ []
test-Had-false = refl

test-vec2 : ⟦ 𝟚 ×ᵤ 𝟚 ⟧ → Float
test-vec2 (inj₁ x , inj₁ x₁) = 1.0
test-vec2 (inj₁ x , inj₂ y) = 0.0
test-vec2 (inj₂ y , inj₁ x) = 0.0
test-vec2 (inj₂ y , inj₂ y₁) = 0.0


test-Had2-00 :  show ((R⁻¹ (𝟚 ×ᵤ 𝟚) ∘ generalize PiH.PiH₀ (id⟷₁ ⊗ swap₊) ∘ R (𝟚 ×ᵤ 𝟚))  test-vec2) ≡
  ((inj₁ tt , inj₁ tt) , 0.7071067811706743) ∷
      ((inj₁ tt , inj₂ tt) , 0.707106781202421) ∷
      ((inj₂ tt , inj₁ tt) , 0.0) ∷
      ((inj₂ tt , inj₂ tt) , 1.1102230246251565e-16) ∷ []
test-Had2-00 = refl

test-Had2-0 : show (PiH.evalH (id⟷₁ ⊗ swap₊) test-vec2) ≡
  ((inj₁ tt , inj₁ tt) , 0.7071067811706743) ∷
      ((inj₁ tt , inj₂ tt) , 0.707106781202421) ∷
      ((inj₂ tt , inj₁ tt) , 0.0) ∷
      ((inj₂ tt , inj₂ tt) , 1.1102230246251565e-16) ∷ []
test-Had2-0 = refl

test-Had2-1 : show (evalTL₁ (A.idzh A.*** A.arr₂ swap₊) test-vec2) ≡
  ((inj₁ tt , inj₁ tt) , 0.7071067811706743) ∷
      ((inj₁ tt , inj₂ tt) , 0.707106781202421) ∷
      ((inj₂ tt , inj₁ tt) , 0.0) ∷
      ((inj₂ tt , inj₂ tt) , 1.1102230246251565e-16) ∷ []
test-Had2-1 = refl

test-Had2-2 : show (evalTL₁ (A.arr₁ swap₊ A.*** A.idzh) test-vec2) ≡
  ((inj₁ tt , inj₁ tt) , 0.0) ∷ ((inj₁ tt , inj₂ tt) , 0.0) ∷
  ((inj₂ tt , inj₁ tt) , 1.0) ∷ ((inj₂ tt , inj₂ tt) , 0.0) ∷ []
test-Had2-2 = refl

-- very slow and supremely wrong
test-Had2-3 : show (evalTL₁ (A.arr₂ swap₊ A.*** A.idzh) test-vec2) ≡
  ((inj₁ tt , inj₁ tt) , 0.7071067811706744) ∷
      ((inj₁ tt , inj₂ tt) , 0.0) ∷
      ((inj₂ tt , inj₁ tt) , 0.7071067812024212) ∷
      ((inj₂ tt , inj₂ tt) , 0.0) ∷ []
test-Had2-3 = refl


inner-simon : TList (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚)
inner-simon = A.arr₂ simon₁ A.>>> A.arr₁ simon₂ A.>>> A.arr₂ simon₁

test-vec4 : ⟦ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟧ → Float
test-vec4 (inj₁ _ , inj₁ _ , inj₁ _ , inj₁ _) = 1.0
test-vec4 (_ , _ , _ , _) = 0.0

{-
test-s₁ : show (evalTL₁ (A.arr₂ simon₁) test-vec4) ≡ {!!}
test-s₁ = {!show (PiH.evalH simon₁ test-vec4)!}

test-is : show (evalTL₁ inner-simon test-vec4) ≡ {!!}
test-is = {!!}
-}
