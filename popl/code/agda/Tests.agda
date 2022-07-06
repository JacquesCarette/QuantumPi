{-# OPTIONS --without-K --exact-split --safe #-}

module Tests where

open import Data.Float using (Float)
open import Data.List using (List; _∷_; []; map)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiSyntax
open import PiBij using (⟦_⟧; enum)
import ArrowsOverPair as A
open import Instances using (evalTL₁)
import PiZ
import PiH

-- Infrastructure for testing
show : {t : U} → (⟦ t ⟧ → Float) → List (⟦ t ⟧ × Float)
show {t} v = map (λ i → (i , v i)) (enum t)

-- Test things in Amalgamated language
test-notH : show (evalTL₁ (A.arr₂ swap₊) PiH.trueH) ≡ (inj₁ tt , 0.3818376618201004) ∷ (inj₂ tt , 0.9192388155510836) ∷ []
test-notH = refl

test-id : show (evalTL₁ (A.idzh) PiH.trueH) ≡ (inj₁ tt , 0.92) ∷ (inj₂ tt , -0.38) ∷ []
test-id = refl

test-Had : show (evalTL₁ (A.arr₂ swap₊) PiZ.trueZ) ≡ (inj₁ tt , 0.7071067811706743) ∷ (inj₂ tt , 0.707106781202421) ∷ []
test-Had = refl
