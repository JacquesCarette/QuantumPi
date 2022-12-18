{-# OPTIONS --without-K --safe #-}

--Note: not exact-split here, that's too much of a pain
module Tests where

open import Data.Float as F using (Float)
open import Data.List using (List; _∷_; []; map)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiSyntax
open import Amalgamation using (TList)
import ArrowsOverAmalg as A
open import StatesAndEffects
open import Unitary
import PiZ
import PiH
open import Instances using (evalTL₁; evalSE)
open import Simon using (simon₁; simon₂)

---------------------------------------------------------------------------------------
-- Infrastructure for testing

show : {t : U} → (⟦ t ⟧ → Float) → List (⟦ t ⟧ × Float)
show {t} v = map (λ i → (i , v i)) (enum t)

-- Note: these tests are EVIL because they use the most brutal equality possible on the worst thing imaginable, i.e. Floats.

-- Test things in Amalgamated language
test-notH : show (evalTL₁ (A.arr₂ swap₊) PiH.trueH) ≡ (𝔽 , 0.9238795325155821) ∷ (𝕋 , -0.38268343235472) ∷ []
test-notH = refl

test-id : show (evalTL₁ (A.id) PiH.trueH) ≡ (𝔽 , 0.38268343235472) ∷ (𝕋 , 0.9238795325155821) ∷ []
test-id = refl

test-Had-true : show (evalTL₁ (A.arr₂ swap₊) PiZ.trueZ) ≡ (𝔽 , 0.707106781202421) ∷ (𝕋 , -0.7071067811706743) ∷ []
test-Had-true = refl

test-Had-false : show (evalTL₁ (A.arr₂ swap₊) PiZ.falseZ) ≡ (𝔽 , 0.7071067811706743) ∷ (𝕋 , 0.707106781202421) ∷ []
test-Had-false = refl

test-vec2 : ⟦ 𝟚 ×ᵤ 𝟚 ⟧ → Float
test-vec2 (𝕋 , 𝕋) = 1.0
test-vec2 (𝕋 , 𝔽) = 0.0
test-vec2 (𝔽 , 𝕋) = 0.0
test-vec2 (𝔽 , 𝔽) = 0.0

test-cxZ : show (evalTL₁ (A.arr₁ (ctrl swap₊)) test-vec2) ≡
   ((𝔽 , 𝔽) , 0.0) ∷
   ((𝔽 , 𝕋) , 0.0) ∷
   ((𝕋 , 𝔽) , 1.0) ∷
   ((𝕋 , 𝕋) , 0.0) ∷
   []
test-cxZ = refl

test-SE-cxZ =
  show (evalSE StatesAndEffects.CX test-vec2)

test-Had2-00 :  show ((R⁻¹ (𝟚 ×ᵤ 𝟚) ∘ PiZ.evalZ (id⟷ ⊗ swap₊) ∘ R (𝟚 ×ᵤ 𝟚))  test-vec2) ≡
  ((𝔽 , 𝔽) , -1.1102230246251565e-16) ∷
  ((𝔽 , 𝕋) , 0.0) ∷
  ((𝕋 , 𝔽) , 0.707106781202421) ∷
  ((𝕋 , 𝕋) , -0.7071067811706743) ∷ []
test-Had2-00 = refl

test-Had2-0 : show (PiH.evalH (id⟷ ⊗ swap₊) test-vec2) ≡
      ((𝔽 , 𝔽) , -1.1102230246251565e-16) ∷
      ((𝔽 , 𝕋) , 0.0) ∷
      ((𝕋 , 𝔽) , 0.707106781202421) ∷
      ((𝕋 , 𝕋) , -0.7071067811706743) ∷
      []
test-Had2-0 = refl

test-Had2-1 : show (evalTL₁ (A.id A.*** A.arr₂ swap₊) test-vec2) ≡
      ((𝔽 , 𝔽) , -1.1102230246251565e-16) ∷
      ((𝔽 , 𝕋) , 0.0) ∷
      ((𝕋 , 𝔽) , 0.707106781202421) ∷
      ((𝕋 , 𝕋) , -0.7071067811706743) ∷
      []
test-Had2-1 = refl

test-Had2-2 : show (evalTL₁ (A.arr₁ swap₊ A.*** A.id) test-vec2) ≡
  ((𝔽 , 𝔽) , 0.0) ∷   ((𝔽 , 𝕋) , 1.0) ∷
  ((𝕋 , 𝔽) , 0.0) ∷ ((𝕋 , 𝕋) , 0.0) ∷ []
test-Had2-2 = refl

test-Had2-3 : show (evalTL₁ (A.arr₂ swap₊ A.*** A.id) test-vec2) ≡
      ((𝔽 , 𝔽) , 0.0) ∷
      ((𝔽 , 𝕋) , 0.7071067812024212) ∷
      ((𝕋 , 𝔽) , 0.0) ∷
      ((𝕋 , 𝕋) , -0.7071067811706744) ∷
      []
test-Had2-3 = refl

inner-simon : TList (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚) (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚)
inner-simon = A.arr₂ simon₁ A.>>> A.arr₁ simon₂ A.>>> A.arr₂ simon₁

test-vec4 : ⟦ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟧ → Float
test-vec4 (inj₁ _ , inj₁ _ , inj₁ _ , inj₁ _) = 1.0
test-vec4 (_ , _ , _ , _) = 0.0

-- the first part of Simon "works" decently now
test-s₁ : show (evalTL₁ (A.arr₂ simon₁) test-vec4) ≡
  ((𝔽 , 𝔽 , 𝔽 , 𝔽) , 0.49999999997755185) ∷
  ((𝔽 , 𝔽 , 𝔽 , 𝕋) , 1.6348909148276115e-17) ∷
  ((𝔽 , 𝔽 , 𝕋 , 𝔽) , 2.7755575614747768e-17) ∷
  ((𝔽 , 𝔽 , 𝕋 , 𝕋) , -2.2893051763283195e-17) ∷
  ((𝔽 , 𝕋 , 𝔽 , 𝔽) , 0.5) ∷
  ((𝔽 , 𝕋 , 𝔽 , 𝕋) , 2.0237652028100054e-17) ∷
  ((𝔽 , 𝕋 , 𝕋 , 𝔽) , 3.925231146709438e-17) ∷
  ((𝔽 , 𝕋 , 𝕋 , 𝕋) , -2.1659708620061032e-17) ∷
  ((𝕋 , 𝔽 , 𝔽 , 𝔽) , 0.5) ∷
  ((𝕋 , 𝔽 , 𝔽 , 𝕋) , 2.0237652028100058e-17) ∷
  ((𝕋 , 𝔽 , 𝕋 , 𝔽) , 3.925231146709438e-17) ∷
  ((𝕋 , 𝔽 , 𝕋 , 𝕋) , -2.165970862006103e-17) ∷
  ((𝕋 , 𝕋 , 𝔽 , 𝔽) , 0.5000000000224483) ∷
  ((𝕋 , 𝕋 , 𝔽 , 𝕋) , 2.807041067731488e-17) ∷
  ((𝕋 , 𝕋 , 𝕋 , 𝔽) , 2.7755575616510065e-17) ∷
  ((𝕋 , 𝕋 , 𝕋 , 𝕋) , -3.3059056140334115e-17) ∷ []
test-s₁ = refl

---------------------------------------------------------------------
-- Tests of effectful language

<0|0> <0|+> <0|-> <0|1> : I ↭ I
<0|0> = zero >>>> assertZero
<0|+> = plus >>>> assertZero
<0|-> = minus >>>> assertZero
<0|1> = one >>>> assertZero

-- Simple tests
|0> : show (evalSE zero (λ tt → 1.0)) ≡
  (𝔽 , 1.0) ∷ (𝕋 , 0.0) ∷ []
|0> = refl

|1> : show (evalSE one (λ tt → 1.0)) ≡
  (𝔽 , 0.0) ∷ (𝕋 , 1.0) ∷ []
|1> = refl

<0| : show (evalSE assertZero λ {(inj₁ _) → 0.4; (inj₂ _) → 0.916}) ≡ (tt , 0.4) ∷ []
<0| = refl

-- This first one is good
<0|0>≡1 : show (evalSE <0|0> (λ tt → 1.0)) ≡ (tt , 1.0) ∷ []
<0|0>≡1 = refl

<0|+>≡1 : show (evalSE <0|+> (λ tt → 1.0)) ≡ (tt , 0.7071067811706743) ∷ []
<0|+>≡1 = refl

<0|->≡1 : show (evalSE <0|-> (λ tt → 1.0)) ≡ (tt , 0.7071067812024211) ∷ []
<0|->≡1 = refl

<0|1>≡1 : show (evalSE <0|1> (λ tt → 1.0)) ≡ (tt , 0.0) ∷ []
<0|1>≡1 = refl

---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------
