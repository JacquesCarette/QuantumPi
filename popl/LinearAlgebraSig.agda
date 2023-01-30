{-# OPTIONS --without-K --exact-split --safe #-}

-- The signature of the types involved in Linear Algebra

module LinearAlgebraSig where

open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)

private
  variable
    t t₁ t₂ t₃ t₄ : Set
    
record LASig : Set₁ where
  field
    vec : Set → Set
    mat : Set → Set

  linop : Set → Set → Set
  linop s t = vec s → vec t

  aut : Set → Set
  aut t = linop t t
  
  field
    _⊕_ : {t₁ t₂ : Set} → aut t₁ → aut t₂ → aut (t₁ ⊎ t₂)
    _⊗_ : {t₁ t₂ : Set} → aut t₁ → aut t₂ → aut (t₁ × t₂)

  field
    unite+l   : linop (⊥ ⊎ t) t
    uniti+l   : linop t (⊥ ⊎ t)
    unite*l   : linop (⊤ × t) t
    uniti*l   : linop t (⊤ × t)
    swap+     : linop (t₁ ⊎ t₂) (t₂ ⊎ t₁)
    swap×     : linop (t₁ × t₂) (t₂ × t₁)
    assocl+   : linop (t₁ ⊎ (t₂ ⊎ t₃)) ((t₁ ⊎ t₂) ⊎ t₃)
    assocr+   : linop ((t₁ ⊎ t₂) ⊎ t₃) (t₁ ⊎ (t₂ ⊎ t₃))
    assocl*   : linop (t₁ × (t₂ × t₃)) ((t₁ × t₂) × t₃)
    assocr*   : linop ((t₁ × t₂) × t₃) (t₁ × (t₂ × t₃))
    absorbl′  : linop (t × ⊥) ⊥
    factorzr′ : linop ⊥ (t × ⊥)
    dist′     : linop ((t₁ ⊎ t₂) × t₃) ((t₁ × t₃) ⊎ (t₂ × t₃))
    factor′   : linop ((t₁ × t₃) ⊎ (t₂ × t₃)) ((t₁ ⊎ t₂) × t₃)
    idp       : linop t t
    _⊚_       : (linop t₁ t₂) → (linop t₂ t₃) → (linop t₁ t₃)
    _⊕′_      : (linop t₁ t₃) → (linop t₂ t₄) → (linop (t₁ ⊎ t₂) (t₃ ⊎ t₄))
    _⊛_       : (linop t₁ t₃) → (linop t₂ t₄) → (linop (t₁ × t₂) (t₃ × t₄))

    true      : vec (⊤ ⊎ ⊤)
    false     : vec (⊤ ⊎ ⊤)
