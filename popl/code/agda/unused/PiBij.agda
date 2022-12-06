{-# OPTIONS --without-K --exact-split --safe #-}

-- Interpretation as sets and isormorphisms (the categorification of Bij)
module PiBij where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; cartesianProduct)
open import Data.Product as Prod using (_,_; _×_; swap)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_; flip)

open import PiSyntax -- everything!
open import PiTagless using (Pi; PiR; reverse)

generalize : {t₁ t₂ : U} {rep : U → U → Set} → Pi rep → (t₁ ⟷₁ t₂) → rep t₁ t₂
generalize p unite₊l = Pi.unite+l p
generalize p uniti₊l = Pi.uniti+l p
generalize p unite⋆l = Pi.unite*l p
generalize p uniti⋆l = Pi.uniti*l p
generalize p swap₊ = Pi.swap+ p
generalize p swap⋆ = Pi.swap× p
generalize p assocl₊ = Pi.assocl+ p
generalize p assocr₊ = Pi.assocr+ p
generalize p assocl⋆ = Pi.assocl* p
generalize p assocr⋆ = Pi.assocr* p
generalize p absorbl = Pi.absorbl′ p
generalize p factorzr = Pi.factorzr′ p
generalize p dist = Pi.dist′ p
generalize p factor = Pi.factor′ p
generalize p id⟷₁ = Pi.idp p
generalize p (c ◎ c₁) = Pi._⊚_ p (generalize p c) (generalize p c₁)
generalize p (c ⊕ c₁) = Pi._⊕′_ p (generalize p c) (generalize p c₁)
generalize p (c ⊗ c₁) = Pi._⊛_ p (generalize p c) (generalize p c₁)

-------------------------------------------------------------------------------------
