{-# OPTIONS --without-K #-}

-- Infrastructure to "run" examples

module QPi.Execute where

open import Data.Float using (Float)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; _∷_; []; map; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Pi.Types using (U; O; ⟦_⟧; enum; _≟_)
open import FloatUtils using (vec; mat; tooSmall)
open import Instances using (evalSE)

open import QPi.Syntax using (_⇔_)
open import QPi.Semantics using (embed)

---------------------------------------------------------------------------

private
  variable
    t t₁ t₂ : U

---------------------------------------------------------------------------
-- Infrastructure for running things

K : U → Set
K t = vec ⟦ t ⟧

show : {t : U} → K t → List (⟦ t ⟧ × Float)
show {t} v =
  foldr (λ i r → let a = v i in if tooSmall a then r else (i , a) ∷ r)
        [] 
        (enum t)

ket : mat ⟦ t ⟧
ket v w = if v ≟ w then 1.0 else 0.0

run : (t₁ ⇔ t₂) → K t₁ → List (⟦ t₂ ⟧ × Float)
run c v = show (evalSE (embed c) v)

showAll : {t₁ t₂ : U} → (t₁ ⇔ t₂) → List (⟦ t₁ ⟧ × List (⟦ t₂ ⟧ × Float))
showAll {t₁} c = map (λ v → (v , run c (ket v))) (enum t₁)

---------------------------------------------------------------------------
---------------------------------------------------------------------------
