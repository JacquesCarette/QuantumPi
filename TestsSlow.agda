{-# OPTIONS --without-K --safe #-}

--Note: not exact-split here, that's too much of a pain
module TestsSlow where

open import Data.Float using (Float)
open import Data.List using (_β·_; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_β‘_; refl)

open import Pi.Types using (π; π½)
open import Instances using (evalTLβ)
open import Tests using (inner-simon; test-vec4; show)

-- takes ~22s on my MacBook Air
-- indentation used to highlight real values from virtual 0s
test-is : show (evalTLβ inner-simon test-vec4) β‘
  ((π½ , π½ , π½ , π½) , 0.5000000000000001)  β·
  ((π½ , π½ , π½ , π) ,        4.738173134873553e-17) β·
  ((π½ , π½ , π , π½) ,        4.5106981034918784e-17) β·
  ((π½ , π½ , π , π) , 0.5000000000000001) β·
  ((π½ , π , π½ , π½) ,        -2.24482377131352e-11) β·
  ((π½ , π , π½ , π) ,        3.350394354180222e-17) β·
  ((π½ , π , π , π½) ,        1.8013739550477034e-17) β·
  ((π½ , π , π , π) ,        2.244829322428643e-11) β·
  ((π , π½ , π½ , π½) ,        -2.2448209957559584e-11) β·
  ((π , π½ , π½ , π) ,        5.7483679261733055e-18) β·
  ((π , π½ , π , π½) ,        5.1923354385602495e-18) β·
  ((π , π½ , π , π) ,        2.24482377131352e-11) β·
  ((π , π , π½ , π½) , 0.5000000000000002) β·
  ((π , π , π½ , π) ,        8.129419882522301e-18) β·
  ((π , π , π , π½) ,        -1.7351405419289864e-17) β·
  ((π , π , π , π) , -0.5000000000000001) β· []
test-is = refl
