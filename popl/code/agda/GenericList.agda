{-# OPTIONS --without-K --exact-split --safe #-}

module GenericList where

open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)

open import PiSyntax using (U; _×ᵤ_; !⟷₁)
open import PiBij using (representable; transform)
open import PiTagless using (Pi)
open import Pairing using (Pair; PiPair)

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U
    a b c d : U

-- We can have a generic list of composables
data LST (p q : U → U → Set) : U → U → Set where
  NIL : LST p q a a
  CONS : (p a c) ⊎ (q a c) → LST p q c b → LST p q a b

-- which does give us a Pairing very generically
module _ {rep₁ rep₂ : U → U → Set} where
  comp : {t₁ t₂ t₃ : U} → LST rep₁ rep₂ t₁ t₂ → LST rep₁ rep₂ t₂ t₃ → LST rep₁ rep₂ t₁ t₃
  comp NIL y = y
  comp z@(CONS _ _) NIL = z
  comp (CONS x y) z@(CONS _ _) = CONS x (comp y z)

  LST-Pair : Pair rep₁ rep₂ (LST rep₁ rep₂)
  LST-Pair = record
    { nil = NIL
    ; cons₁ = λ a b → CONS (inj₁ a) b
    ; cons₂ = λ a b → CONS (inj₂ a) b
    ; _⊚⊚_ = comp
    }

-- if we want to pair up Pi representations, they need to be 'representable' to
-- get an inverse
module _ {rep₁ rep₂ : U → U → Set} (p₁ : Pi rep₁) (p₂ : Pi rep₂)
    (pres₁ : representable rep₁) (pres₂ : representable rep₂) where
  private
    module P = Pi p₁
    module Q = Pi p₂

  first′ : {t₁ t₂ t₃ : U} → LST rep₁ rep₂ t₁ t₂ → LST rep₁ rep₂ (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)
  first′ NIL = NIL
  first′ (CONS (inj₁ x) y) = CONS (inj₁ (x P.⊛ P.idp )) (first′ y)
  first′ (CONS (inj₂ x) y) = CONS (inj₂ (x Q.⊛ Q.idp)) (first′ y)

  inv′ : {t₁ t₂ : U} → LST rep₁ rep₂ t₁ t₂ → LST rep₁ rep₂ t₂ t₁
  inv′ NIL = NIL
  inv′ (CONS (inj₁ x) l) = comp (inv′ l) (CONS (inj₁ (transform p₁ pres₁ !⟷₁ x)) NIL)
  inv′ (CONS (inj₂ y) l) = comp (inv′ l) (CONS (inj₂ (transform p₂ pres₂ !⟷₁ y)) NIL)

  LST-PiPair : PiPair rep₁ rep₂ (LST rep₁ rep₂)
  LST-PiPair = record
    { pair = LST-Pair
    ; first = first′
    ; inv = inv′
    }
