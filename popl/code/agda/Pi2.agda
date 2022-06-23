{-# OPTIONS --without-K --exact-split --safe #-}

module Pi2 where

open import Data.Float as F using (Float)
open import Data.List using (List; map; foldr)
open import Data.Product as Prod using (_,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)

open import PiSyntax
open import PiZ hiding (Fwd)
open import PiTagless
open import Pairing
open import ArrowsOverPair

-------------------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U
    a b c d : U

-------------------------------------------------------------------------------------
-- Lifting to States and Effects.
record StEffPi {rep₁ rep₂ : U → U → Set}
         (p : U → U → Set)
         (pair : PiPair rep₁ rep₂ p)
         (rep : PiPair rep₁ rep₂ p → U → U → Set) : Set where
  field
    lift : p (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄) → rep pair t₁ t₃

-- Some examples where we use all of the above
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
  lswap = lift (arr₁ (Pi.swap× p₁))

  -- With annotations
  zero : rep pair I (I +ᵤ I)
  zero = lift (arr₁ (Pi.swap× p₁))

-- We can have a generic list of composables
data LST (p q : U → U → Set) : U → U → Set where
  NIL : LST p q a a
  CONS : (p a c) ⊎ (q a c) → LST p q c b → LST p q a b

-- which does give us a Pairing
module _ {rep₁ rep₂ : U → U → Set} (p₁ : Pi rep₁) (p₂ : Pi rep₂)
    (pres₁ : representable rep₁) (pres₂ : representable rep₂) where
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

  inv′ : {t₁ t₂ : U} → LST rep₁ rep₂ t₁ t₂ → LST rep₁ rep₂ t₂ t₁
  inv′ NIL = NIL
  inv′ (CONS (inj₁ x) l) = comp (inv′ l) (CONS (inj₁ (transform p₁ pres₁ !⟷₁ x)) NIL)
  inv′ (CONS (inj₂ y) l) = comp (inv′ l) (CONS (inj₂ (transform p₂ pres₂ !⟷₁ y)) NIL)

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
    ; inv = inv′
    }

-----------------------------------------------------------------------
-- Below we start the work that correspoints to the H interpretation

H : (t : U) → Set
H t = ⟦ t ⟧z → Float

Fwd : U → U → Set
Fwd t₁ t₂ = H t₁ → H t₂

sumf : List Float → Float
sumf = foldr F._+_ (F.fromℕ 0)

-- Note how the interpretation is λ f → f ∘ g where g is the opposite of the Fwd interpretation for the
-- evaluator for PiZ
PiH : Pi Fwd
PiH = record
  { unite+l = λ f → f ∘ inj₂
  ; uniti+l = λ {f (inj₂ x) → f x }
  ; unite*l = λ f x → f (tt , x)
  ; uniti*l = λ f x → f (Prod.proj₂ x)
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
