{-# OPTIONS --without-K --safe #-}

--Note: not exact-split here, that's too much of a pain
module TestsSlow where

open import Data.Float using (Float)
open import Data.List using (List; _∷_; []; map)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Amalgamation using (TList)
open import Instances using (evalTL₁)
open import Tests

-- takes ~22s on my MacBook Air
-- indentation used to highlight real values from virtual 0s
test-is : show (evalTL₁ inner-simon test-vec4) ≡
  ((inj₁ tt , inj₁ tt , inj₁ tt , inj₁ tt) , 0.5000000000000001)  ∷
  ((inj₁ tt , inj₁ tt , inj₁ tt , inj₂ tt) ,        -4.738173134873553e-17) ∷
  ((inj₁ tt , inj₁ tt , inj₂ tt , inj₁ tt) ,        -4.5106981034918784e-17) ∷
  ((inj₁ tt , inj₁ tt , inj₂ tt , inj₂ tt) , 0.5000000000000001) ∷
  ((inj₁ tt , inj₂ tt , inj₁ tt , inj₁ tt) ,         2.24482377131352e-11) ∷
  ((inj₁ tt , inj₂ tt , inj₁ tt , inj₂ tt) ,         3.350394354180222e-17) ∷
  ((inj₁ tt , inj₂ tt , inj₂ tt , inj₁ tt) ,         1.8013739550477034e-17) ∷
  ((inj₁ tt , inj₂ tt , inj₂ tt , inj₂ tt) ,        -2.244829322428643e-11) ∷
  ((inj₂ tt , inj₁ tt , inj₁ tt , inj₁ tt) ,         2.2448209957559584e-11) ∷
  ((inj₂ tt , inj₁ tt , inj₁ tt , inj₂ tt) ,         5.7483679261733055e-18) ∷
  ((inj₂ tt , inj₁ tt , inj₂ tt , inj₁ tt) ,         5.1923354385602495e-18) ∷
  ((inj₂ tt , inj₁ tt , inj₂ tt , inj₂ tt) ,        -2.24482377131352e-11) ∷
  ((inj₂ tt , inj₂ tt , inj₁ tt , inj₁ tt) , 0.5000000000000002) ∷
  ((inj₂ tt , inj₂ tt , inj₁ tt , inj₂ tt) ,        -8.129419882522301e-18) ∷
  ((inj₂ tt , inj₂ tt , inj₂ tt , inj₁ tt) ,         1.7351405419289864e-17) ∷
  ((inj₂ tt , inj₂ tt , inj₂ tt , inj₂ tt) , -0.5000000000000001) ∷ []
test-is = refl
