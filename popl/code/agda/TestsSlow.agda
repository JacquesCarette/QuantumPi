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
open import PiSyntax using (𝕋; 𝔽)

-- takes ~22s on my MacBook Air
-- indentation used to highlight real values from virtual 0s
test-is : show (evalTL₁ inner-simon test-vec4) ≡
  ((𝔽 , 𝔽 , 𝔽 , 𝔽) , 0.5000000000000001)  ∷
  ((𝔽 , 𝔽 , 𝔽 , 𝕋) ,        4.738173134873553e-17) ∷
  ((𝔽 , 𝔽 , 𝕋 , 𝔽) ,        4.5106981034918784e-17) ∷
  ((𝔽 , 𝔽 , 𝕋 , 𝕋) , 0.5000000000000001) ∷
  ((𝔽 , 𝕋 , 𝔽 , 𝔽) ,        -2.24482377131352e-11) ∷
  ((𝔽 , 𝕋 , 𝔽 , 𝕋) ,        3.350394354180222e-17) ∷
  ((𝔽 , 𝕋 , 𝕋 , 𝔽) ,        1.8013739550477034e-17) ∷
  ((𝔽 , 𝕋 , 𝕋 , 𝕋) ,        2.244829322428643e-11) ∷
  ((𝕋 , 𝔽 , 𝔽 , 𝔽) ,        -2.2448209957559584e-11) ∷
  ((𝕋 , 𝔽 , 𝔽 , 𝕋) ,        5.7483679261733055e-18) ∷
  ((𝕋 , 𝔽 , 𝕋 , 𝔽) ,        5.1923354385602495e-18) ∷
  ((𝕋 , 𝔽 , 𝕋 , 𝕋) ,        2.24482377131352e-11) ∷
  ((𝕋 , 𝕋 , 𝔽 , 𝔽) , 0.5000000000000002) ∷
  ((𝕋 , 𝕋 , 𝔽 , 𝕋) ,        8.129419882522301e-18) ∷
  ((𝕋 , 𝕋 , 𝕋 , 𝔽) ,        -1.7351405419289864e-17) ∷
  ((𝕋 , 𝕋 , 𝕋 , 𝕋) , -0.5000000000000001) ∷ []
test-is = refl
