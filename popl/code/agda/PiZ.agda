{-# OPTIONS --without-K --exact-split --safe #-}

module PiZ where

open import Data.Float as F using (Float)
open import Data.Product as Prod using (_,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)

open import PiSyntax using (U; I; O; _+ᵤ_; _×ᵤ_; 𝟚)
open import PiTagless using (Pi)
open import Unitary using (𝒰)

-----------------------------------------------------------------------
-- Below we start the work that correspoints to the Z interpretation

-- The Z representation is as a vector with basis an enumeration of a type (t : U) with
-- real values (here represented as Floats). We use functions to represent such vectors.
-- So 'enum' from PiBij plays a crucial role here.
Z : (t : U) → Set
Z = 𝒰

Fwd : U → U → Set
Fwd t₁ t₂ = Z t₁ → Z t₂

-- Note how the interpretation is λ f → f ∘ g where g is the opposite of the Fwd interpretation for the
-- evaluator for PiBij
-- The interpretations pretty much follow the types. The only tricky one is for product, where a
-- convolution is used. Here again 'enum' is crucial, as we need to accumulate the action of 'h' over
-- all pairs, where we only have one of the two values in hand.
PiZ : Pi Fwd
PiZ = record
  { unite+l = λ f → f ∘ inj₂
  ; uniti+l = λ {f (inj₂ x) → f x }
  ; unite*l = λ f x → f (tt , x)
  ; uniti*l = λ f x → f (Prod.proj₂ x)
  ; unite+  = λ f → f ∘ inj₁
  ; uniti+  = λ {f (inj₁ x) → f x }
  ; unite*  = λ f x → f (x , tt)
  ; uniti*  = λ f x → f (Prod.proj₁ x)
  ; swap+ = λ f → f ∘ Sum.swap
  ; swap× = λ f → f ∘ Prod.swap
  ; assocl+ = λ f → f ∘ Sum.assocʳ
  ; assocr+ = λ f → f ∘ Sum.assocˡ
  ; assocl* = λ f → f ∘ Prod.assocʳ
  ; assocr* = λ f → f ∘ Prod.assocˡ
  ; absorbr′ = λ { f () }
  ; absorbl′ = λ { f () }
  ; factorzr′ = λ {f ( _ , () )}
  ; factorzl′ = λ {f ( () , _ ) }
  ; dist′ = λ f → f ∘ Sum.[ Prod.map₁ inj₁ , Prod.map₁ inj₂ ]
  ; distl′ = λ f → f ∘ Sum.[ Prod.map₂ inj₁ , Prod.map₂ inj₂ ]
  ; factor′ = λ f → f ∘ λ { (a , b) → Sum.map (_, b) (_, b) a }
  ; factorl′ = λ f → f ∘ λ (a , b) → Sum.map (a ,_) (a ,_) b
  ; idp = λ x → x
  ; _⊚_ = λ f g → g ∘ f
  ; _⊕′_ = λ f g h → Sum.[ f (h ∘ inj₁) , g (h ∘ inj₂) ]
  ; _⊛_ = λ A₁₃ B₂₄ v (i , j) → A₁₃ (λ a → B₂₄ (λ b → v (a , b)) j) i
  }

trueZ falseZ : Z 𝟚
trueZ (inj₁ x) = 1.0
trueZ (inj₂ y) = 0.0
falseZ (inj₁ x) = 0.0
falseZ (inj₂ y) = 1.0

x : Z 𝟚 → Z 𝟚
x = Pi.swap+ PiZ
