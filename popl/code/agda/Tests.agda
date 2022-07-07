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
import ArrowsOverAmalg as A
open import Amalgamation using (TList)
open import Instances using (evalTL₁)
import PiZ
import PiH
open import Simon using (simon₁; simon₂)
open import Unitary

-- Infrastructure for testing
show : {t : U} → (⟦ t ⟧ → Float) → List (⟦ t ⟧ × Float)
show {t} v = map (λ i → (i , v i)) (enum t)

-- Note: these tests are EVIL because they use the most brutal equality possible on the worst thing imaginable, i.e. Floats.

-- Test things in Amalgamated language
test-notH : show (evalTL₁ (A.arr₂ swap₊) PiH.trueH) ≡ (inj₁ tt , 0.38268343235472) ∷ (inj₂ tt , 0.9238795325155821) ∷ []
test-notH = refl

test-id : show (evalTL₁ (A.idzh) PiH.trueH) ≡ (inj₁ tt , 0.9238795325155821) ∷ (inj₂ tt , -0.38268343235472) ∷ []
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


test-Had2-00 :  show ((R⁻¹ (𝟚 ×ᵤ 𝟚) ∘ generalize PiZ.PiZ (id⟷₁ ⊗ swap₊) ∘ R (𝟚 ×ᵤ 𝟚))  test-vec2) ≡
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

-- the first part of Simon "works" decently now
test-s₁ : show (evalTL₁ (A.arr₂ simon₁) test-vec4) ≡
  ((inj₁ tt , inj₁ tt , inj₁ tt , inj₁ tt) , 0.49999999997755185) ∷
  ((inj₁ tt , inj₁ tt , inj₁ tt , inj₂ tt) , 1.6348909148276115e-17) ∷
  ((inj₁ tt , inj₁ tt , inj₂ tt , inj₁ tt) , 2.7755575614747768e-17) ∷
  ((inj₁ tt , inj₁ tt , inj₂ tt , inj₂ tt) , -2.2893051763283195e-17) ∷
  ((inj₁ tt , inj₂ tt , inj₁ tt , inj₁ tt) , 0.5) ∷
  ((inj₁ tt , inj₂ tt , inj₁ tt , inj₂ tt) , 2.0237652028100054e-17) ∷
  ((inj₁ tt , inj₂ tt , inj₂ tt , inj₁ tt) , 3.925231146709438e-17) ∷
  ((inj₁ tt , inj₂ tt , inj₂ tt , inj₂ tt) , -2.1659708620061032e-17) ∷
  ((inj₂ tt , inj₁ tt , inj₁ tt , inj₁ tt) , 0.5) ∷
  ((inj₂ tt , inj₁ tt , inj₁ tt , inj₂ tt) , 2.0237652028100058e-17) ∷
  ((inj₂ tt , inj₁ tt , inj₂ tt , inj₁ tt) , 3.925231146709438e-17) ∷
  ((inj₂ tt , inj₁ tt , inj₂ tt , inj₂ tt) , -2.165970862006103e-17) ∷
  ((inj₂ tt , inj₂ tt , inj₁ tt , inj₁ tt) , 0.5000000000224483) ∷
  ((inj₂ tt , inj₂ tt , inj₁ tt , inj₂ tt) , 2.807041067731488e-17) ∷
  ((inj₂ tt , inj₂ tt , inj₂ tt , inj₁ tt) , 2.7755575616510065e-17) ∷
  ((inj₂ tt , inj₂ tt , inj₂ tt , inj₂ tt) , -3.3059056140334115e-17) ∷ []
test-s₁ = refl

-- takes ~22s on my MacBook Air
-- use columns to highly values from virtual 0s
test-is : show (evalTL₁ inner-simon test-vec4) ≡
  ((inj₁ tt , inj₁ tt , inj₁ tt , inj₁ tt) , 0.5000000000000001)  ∷
  ((inj₁ tt , inj₁ tt , inj₁ tt , inj₂ tt) ,        4.738173134873553e-17) ∷
  ((inj₁ tt , inj₁ tt , inj₂ tt , inj₁ tt) ,        4.5106981034918784e-17) ∷
  ((inj₁ tt , inj₁ tt , inj₂ tt , inj₂ tt) , 0.5000000000000001) ∷
  ((inj₁ tt , inj₂ tt , inj₁ tt , inj₁ tt) ,        -2.24482377131352e-11) ∷
  ((inj₁ tt , inj₂ tt , inj₁ tt , inj₂ tt) ,        3.350394354180222e-17) ∷
  ((inj₁ tt , inj₂ tt , inj₂ tt , inj₁ tt) ,        1.8013739550477034e-17) ∷
  ((inj₁ tt , inj₂ tt , inj₂ tt , inj₂ tt) ,        2.244829322428643e-11) ∷
  ((inj₂ tt , inj₁ tt , inj₁ tt , inj₁ tt) ,        -2.2448209957559584e-11) ∷
  ((inj₂ tt , inj₁ tt , inj₁ tt , inj₂ tt) ,        5.7483679261733055e-18) ∷
  ((inj₂ tt , inj₁ tt , inj₂ tt , inj₁ tt) ,        5.1923354385602495e-18) ∷
  ((inj₂ tt , inj₁ tt , inj₂ tt , inj₂ tt) ,        2.24482377131352e-11) ∷
  ((inj₂ tt , inj₂ tt , inj₁ tt , inj₁ tt) , 0.5000000000000002) ∷
  ((inj₂ tt , inj₂ tt , inj₁ tt , inj₂ tt) ,        8.129419882522301e-18) ∷
  ((inj₂ tt , inj₂ tt , inj₂ tt , inj₁ tt) ,        -1.7351405419289864e-17) ∷
  ((inj₂ tt , inj₂ tt , inj₂ tt , inj₂ tt) , -0.5000000000000001) ∷ []
test-is = refl
