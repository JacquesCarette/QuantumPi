{-# OPTIONS --without-K --exact-split --safe #-}

module Pi2 where

open import Data.Empty using (⊥)
open import Data.Float as F using (Float)
open import Data.List using (List; []; _∷_; _++_; map; cartesianProduct; foldr)
open import Data.Product using (_×_; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)

open import PiSyntax
open import PiZ

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U
    a b c d : U

-------------------------------------------------------------------------------------

record Pi (rep : U → U → Set) : Set where
  field
    idp : rep t t
    _⊚_ : rep t₁ t₂ → rep t₂ t₃ → rep t₁ t₃
    swapp : rep (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
    _⊛_ : rep t₁ t₃ → rep t₂ t₄ → rep (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄)

-- instances
Pi⟷ : Pi _⟷₁_
Pi⟷ = record
  { idp = id⟷₁
  ; _⊚_ = _◎_
  ; swapp = swap⋆
  ; _⊛_ = _⊗_
  }

-------------------------------------------------------------------------------------
-- Pairing

record Pair {W : Set} (rep₁ rep₂ : W → W → Set)
  (p : W → W → Set) : Set where
  infixr 50 _⊚⊚_
  field
    nil : {t : W} → p t t
    cons₁ : {t₁ t₂ t₃ : W} → rep₁ t₁ t₂ → p t₂ t₃ → p t₁ t₃
    cons₂ : {t₁ t₂ t₃ : W} → rep₂ t₁ t₂ → p t₂ t₃ → p t₁ t₃
    _⊚⊚_ : {t₁ t₂ t₃ : W} → p t₁ t₂ → p t₂ t₃ → p t₁ t₃

record PiPair (rep₁ rep₂ : U → U → Set)
  (p : U → U → Set) : Set where
  field
    pair : Pair rep₁ rep₂ p
    first : p t₁ t₂ -> p (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)

module Arrows {rep₁ rep₂ : U → U → Set} (p₁ : Pi rep₁) (p₂ : Pi rep₂)
         (p : U → U → Set)
         (πpair : PiPair rep₁ rep₂ p) where
  open PiPair πpair
  open Pair pair

  arr₁ : rep₁ t₁ t₂ -> p t₁ t₂
  arr₁ c = cons₁ c nil
  arr₂ : rep₂ t₁ t₂ -> p t₁ t₂
  arr₂ c = cons₂ c nil

  idzh : p t t
  idzh = arr₁ (Pi.idp p₁)
  swappzh : p (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
  swappzh = arr₁ (Pi.swapp p₁)

  second : p t₁ t₂ → p (t₃ ×ᵤ t₁) (t₃ ×ᵤ t₂)
  second c = swappzh ⊚⊚ first c ⊚⊚ swappzh

record StEffPi {rep₁ rep₂ : U → U → Set}
         (p : U → U → Set)
         (pair : PiPair rep₁ rep₂ p)
         (rep : PiPair rep₁ rep₂ p → U → U → Set) : Set where
  field
    lift : p (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄) → rep pair t₁ t₃


module _ {rep₁ rep₂ : U → U → Set} (p₁ : Pi rep₁) (p₂ : Pi rep₂)
         (p : U → U → Set)
         (pair : PiPair rep₁ rep₂ p)
         (rep : PiPair rep₁ rep₂ p → U → U → Set)
         (eff : StEffPi p pair rep) where
  open StEffPi eff
  open Arrows p₁ p₂ p pair
  -- open Pair pair

  id₁ : rep₁ I I
  id₁ = Pi.idp p₁

  -- Lifting too general a swap:
  lswap : rep pair t₁ t₃
  lswap = lift (arr₁ (Pi.swapp p₁))

  -- With annotations
  zero : rep pair I (I +ᵤ I)
  zero = lift (arr₁ (Pi.swapp p₁))

-- We can have a generic list of composables
data LST (p q : U → U → Set) : U → U → Set where
  NIL : LST p q a a
  CONS : (p a c) ⊎ (q a c) → LST p q c b → LST p q a b

-- which does give us a Pairing
module _ {rep₁ rep₂ : U → U → Set} (p₁ : Pi rep₁) (p₂ : Pi rep₂) where
  private
    module P = Pi p₁
    module Q = Pi p₂
  comp : {t₁ t₂ t₃ : U} → LST rep₁ rep₂ t₁ t₂ → LST rep₁ rep₂ t₂ t₃ → LST rep₁ rep₂ t₁ t₃
  comp NIL y = y
  comp z@(CONS _ _) NIL = z
  comp (CONS x y) z@(CONS _ _) = CONS x (comp y z)

  first′ : {t₁ t₂ t₃ : U} → LST rep₁ rep₂ t₁ t₂ → LST rep₁ rep₂ (t₁ ×ᵤ t₃) (t₂ ×ᵤ t₃)
  first′ NIL = NIL
  first′ (CONS (inj₁ x) y) = CONS (inj₁ (x P.⊛ P.idp )) (first′ y)
  first′ (CONS (inj₂ x) y) = CONS (inj₂ (x Q.⊛ Q.idp)) (first′ y)

  LST-Pair : Pair rep₁ rep₂ (LST rep₁ rep₂)
  LST-Pair = record
    { nil = NIL
    ; cons₁ = λ a b → CONS (inj₁ a) b
    ; cons₂ = λ a b → CONS (inj₂ a) b
    ; _⊚⊚_ = comp
    }
  LST-PiPair : PiPair rep₁ rep₂ (LST rep₁ rep₂)
  LST-PiPair = record
    { pair = LST-Pair
    ; first = first′
    }

-- we can enumerate our types
enum : (t : U) → List ⟦ t ⟧z
enum O = []
enum I = tt ∷ []
enum (t +ᵤ t₁) = map inj₁ (enum t) ++ map inj₂ (enum t₁)
enum (t ×ᵤ t₁) = cartesianProduct (enum t) (enum t₁)

H : (t : U) → Set
H t = ⟦ t ⟧z → Float

Fwd : U → U → Set
Fwd t₁ t₂ = H t₁ → H t₂

sumf : List Float → Float
sumf = foldr F._+_ (F.fromℕ 0)

PiH : Pi Fwd
PiH = record
  { idp = λ x → x
  ; _⊚_ = λ f g → g ∘ f
  ; swapp = λ {f (a , b) → f (b , a)} -- rewrite using swap?
  ; _⊛_ = λ { {t₁} {_} {t₃} f g h (c , d) →
            f (λ a → sumf (map (λ z → h (a , z)) (enum t₃))) c  F.*
            g (λ c → sumf (map (λ z → h (z , c)) (enum t₁))) d}
  }

Bool : U
Bool = I +ᵤ I

trueH falseH trueTH falseTH : H Bool
trueH (inj₁ x) = 0.92
trueH (inj₂ y) = -0.38
falseH (inj₁ x) = 0.38
falseH (inj₂ y) = 0.92
trueTH (inj₁ x) = 0.92
trueTH (inj₂ y) = 0.38
falseTH (inj₁ x) = -0.38
falseTH (inj₂ y) = 0.92

notH : H Bool → H Bool
notH f b = f (Sum.swap b)
