{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Reasoning where

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Pi.Types using (U)
open import Pi.Language as Π using (_◎_; _⟷_; id⟷; !⟷)
import Pi.Terms as ΠT
open import Pi.Equivalences
open import Pi.DefinedEquiv using (xcx)
open import QPi.Syntax
open import QPi.Terms using (ctrlZ; one; copyZ; copyϕ; X; Z;
  H; minus; plus; cx; cz)
open import QPi.Equivalences
open import QPi.Measurement using (measureϕ; measureZ)

---------------------------------------------------------------------------
private
  variable
    t t₁ t₂ t₃ : U
    d d₁ d₂ d₃ d₄ : t₁ ⇔ t₂

infixr 10 _◯_
_◯_ : (d₁ ≡ d₂) → (d₂ ≡ d₃) → (d₁ ≡ d₃)
_◯_ = trans≡

-- Equational reasoning, from stdlib

private
  ≡Setoid : {t₁ t₂ : U} → Setoid _ _
  ≡Setoid {t₁} {t₂} = record
    { Carrier = t₁ ⇔ t₂
    ; _≈_ = _≡_
    ; isEquivalence = record
      { refl = id≡
      ; sym = !≡
      ; trans = trans≡
      }
    }

  module Base {t₁ t₂} = SetoidR (≡Setoid {t₁} {t₂})
  
open Base public hiding (step-≈; step-≡)

infixr 2 step-≡
step-≡ :  (x : t₁ ⇔ t₂) {y z : t₁ ⇔ t₂} →
  _IsRelatedTo_ y z → x ≡ y → x IsRelatedTo z
step-≡ = Base.step-≈

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

---------------------------------------------------------------------------
-- Example proofs

xInv : (X >>> X) ≡ id⇔
xInv = begin
  X >>> X                  ≡⟨ arrZR ⟩
  arrZ (Π.swap₊ ◎ Π.swap₊) ≡⟨ classicalZ linv◎l ⟩
  arrZ id⟷                 ≡⟨ arrZidL ⟩
  id⇔                      ∎

hadInv : (H >>> H) ≡ id⇔
hadInv = trans≡ arrϕR (trans≡ (classicalϕ linv◎l) arrϕidL)  

minusZ≡plus : (minus >>> Z) ≡ plus
minusZ≡plus = begin
  (minus >>> Z)
    ≡⟨ id≡ ⟩
  ((plus >>> H >>> X >>> H) >>> H >>> X >>> H)
    ≡⟨ ((cong≡ (assoc>>>l ◯ assoc>>>l) id≡) ◯ assoc>>>r) ◯ (cong≡ id≡ assoc>>>l) ⟩ 
  (((plus >>> H) >>> X) >>> (H >>> H) >>> X >>> H)
    ≡⟨ cong≡ id≡ (trans≡ (cong≡ hadInv id≡) idl>>>l) ⟩
  (((plus >>> H) >>> X) >>> X >>> H)
    ≡⟨ trans≡ assoc>>>r (cong≡ id≡ assoc>>>l) ⟩
  ((plus >>> H) >>> (X >>> X) >>> H)
    ≡⟨ cong≡ id≡ (trans≡ (cong≡ xInv id≡) idl>>>l) ⟩
  ((plus >>> H) >>> H)
    ≡⟨ trans≡ (trans≡ assoc>>>r (cong≡ id≡ hadInv)) idr>>>l ⟩ 
  plus ∎

oneMinusPlus : ((one *** minus) >>> cz) ≡ (one *** plus)
oneMinusPlus = begin
  (one *** minus) >>> (id⇔ *** H) >>> cx >>> (id⇔ *** H)
    ≡⟨ trans≡ assoc>>>l (cong≡ homL*** id≡) ⟩ 
  ((one >>> id⇔) *** (minus >>> H)) >>> cx >>> (id⇔ *** H)
    ≡⟨ cong≡ (cong*** idr>>>l id≡) id≡ ⟩ 
  (one *** (minus >>> H))>>> cx >>> (id⇔ *** H)
    ≡⟨ cong≡ (cong*** idl>>>r idr>>>r) id≡ ⟩ 
  ((id⇔ >>> one) *** ((minus >>> H) >>> id⇔)) >>> cx >>> (id⇔ *** H)
    ≡⟨ trans≡ (cong≡ homR*** id≡) assoc>>>r ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** id⇔) >>> cx >>> (id⇔ *** H)
    ≡⟨ cong≡ id≡ (trans≡ assoc>>>l (cong≡ e3L id≡)) ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** X) >>> (id⇔ *** H)
    ≡⟨ cong≡ id≡ (trans≡ homL*** (cong*** idr>>>l id≡)) ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** (X >>> H))
    ≡⟨ trans≡ homL*** (cong*** idl>>>l assoc>>>r ) ⟩ 
  one *** (minus >>> H >>> X >>> H)
    ≡⟨ cong*** id≡ minusZ≡plus  ⟩ 
  (one *** plus) ∎


xcxA : id⇔ *** X >>> cx ≡ cx >>> id⇔ *** X
xcxA = begin
  id⇔ *** X >>> cx
    ≡⟨ {!!} ⟩ 
  arrZ ((id⟷ Π.⊗ Π.swap₊) Π.◎ ΠT.cx)
    ≡⟨ classicalZ xcx ⟩
  arrZ (ΠT.cx Π.◎ (id⟷ Π.⊗ Π.swap₊))
    ≡⟨ {!!} ⟩
  cx >>> id⇔ *** X ∎


zhcx : ((id⇔ *** Z) >>> (id⇔ *** H) >>> cx) ≡
       (cz >>> (id⇔ *** H) >>> (id⇔ *** X))
zhcx = begin
  ((id⇔ *** Z) >>> (id⇔ *** H) >>> cx)
    ≡⟨ trans≡ assoc>>>l (cong≡ (trans≡ homL*** (cong*** idl>>>l id≡)) id≡) ⟩
  (id⇔ *** ((H >>> X >>> H) >>> H)) >>> cx
    ≡⟨ {!!} ⟩ 
  id⇔ *** (H >>> X) >>> cx
    ≡⟨ {!!} ⟩
  (cz >>> (id⇔ *** H) >>> (id⇔ *** X)) ∎


measure : measureϕ ≡ (H >>> measureZ >>> H)
measure = begin
  measureϕ
    ≡⟨ {!!} ⟩
  (H >>> measureZ >>> H) ∎

---------------------------------------------------------------------------

