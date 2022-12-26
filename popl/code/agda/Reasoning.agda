{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Reasoning where

open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Pi.Types using (U)
open import Pi.Language as Π using (_◎_; _⟷_; id⟷; !⟷; _⊗_)
import Pi.Terms as ΠT
open import Pi.Equivalences
open import Pi.DefinedEquiv using (xcx)
open import QPi.Syntax
open import QPi.Terms using (ctrlZ; one; copyZ; copyϕ; X; Z;
  H; minus; plus; cx; cz)
open import QPi.Equivalences
open import QPi.Measurement using (measureϕ; measureZ; fst; discard; discardL)
open import QPi.TermReasoning

---------------------------------------------------------------------------
-- Extra infrastructure, much of it inspired by agda-categories

private
  variable
    t t₁ t₂ t₃ : U
    c c₁ c₂ c₃ c₄ : t₁ ⟷ t₂
    d d₁ d₂ d₃ d₄ : t₁ ⇔ t₂

class*>R : arrZ c₁ *** arrZ c₂ >>> arrZ c₃ ≡ arrZ (c₁ Π.⊗ c₂ Π.◎ c₃)
class*>R = arrZR* ⟩◎⟨id ◯ arrZR

class*>L :  arrZ (c₁ Π.⊗ c₂ Π.◎ c₃) ≡ arrZ c₁ *** arrZ c₂ >>> arrZ c₃
class*>L = arrZL ◯ arrZL* ⟩◎⟨id

class>*R : arrZ c₁ >>> arrZ c₂ *** arrZ c₃ ≡ arrZ (c₁ Π.◎ c₂ Π.⊗ c₃)
class>*R = id⟩◎⟨ arrZR* ◯ arrZR

class>*L :  arrZ (c₁ Π.◎ c₂ Π.⊗ c₃) ≡ arrZ c₁ >>> arrZ c₂ *** arrZ c₃
class>*L = arrZL ◯ id⟩◎⟨ arrZL*

pullʳ : (d₁ >>> d₂ ≡ d₃) → (d >>> d₁) >>> d₂ ≡ d >>> d₃
pullʳ eq = assoc>>>r ◯ id⟩◎⟨ eq

pullˡ : (d₁ >>> d₂ ≡ d₃) → d₁ >>> d₂ >>> d ≡ d₃ >>> d
pullˡ eq = assoc>>>l ◯ eq ⟩◎⟨id

cancelʳ : (d₁ >>> d₂ ≡ id⇔) → (d >>> d₁) >>> d₂ ≡ d
cancelʳ inverse = pullʳ inverse ◯ idr>>>l

cancelˡ : (d₁ >>> d₂ ≡ id⇔) → d₁ >>> (d₂ >>> d) ≡ d
cancelˡ inverse = pullˡ inverse ◯ idl>>>l

insertˡ : (d₁ >>> d₂ ≡ id⇔) → d ≡ d₁ >>> (d₂ >>> d)
insertˡ inverse = !≡ (cancelˡ inverse)

-- bifunctoriality of *** lets one sequence
seq₂₁*** : d₁ *** d₂ ≡ (id⇔ *** d₂) >>> (d₁ *** id⇔)
seq₂₁*** = idl>>>r ⟩⊗⟨ idr>>>r ◯ homR***

---------------------------------------------------------------------------
-- Example proofs

xInv : (X >>> X) ≡ id⇔
xInv = begin
  X >>> X                   ≡⟨ arrZR ⟩
  arrZ (Π.swap₊ ◎ Π.swap₊)  ≡⟨ classicalZ linv◎l ⟩
  arrZ id⟷                 ≡⟨ arrZidL ⟩
  id⇔                       ∎

hadInv : (H >>> H) ≡ id⇔
hadInv = arrϕR ◯ classicalϕ linv◎l ◯ arrϕidL

1*HInv : (id⇔ {t₁} *** H) >>> (id⇔ *** H) ≡ id⇔
1*HInv = homL*** ◯ idl>>>l ⟩⊗⟨ hadInv ◯ id***id

minusZ≡plus : (minus >>> Z) ≡ plus
minusZ≡plus = begin
  (minus >>> Z)                                    ≡⟨ id≡ ⟩
  ((plus >>> H >>> X >>> H) >>> H >>> X >>> H)     ≡⟨ ((assoc>>>l ◯ assoc>>>l) ⟩◎⟨id ) ◯ pullʳ assoc>>>l ⟩
  (((plus >>> H) >>> X) >>> (H >>> H) >>> X >>> H) ≡⟨ id⟩◎⟨ ((hadInv ⟩◎⟨id) ◯ idl>>>l) ⟩
  (((plus >>> H) >>> X) >>> X >>> H)               ≡⟨ pullʳ assoc>>>l ⟩
  ((plus >>> H) >>> (X >>> X) >>> H)               ≡⟨ id⟩◎⟨ (xInv ⟩◎⟨id ◯ idl>>>l) ⟩
  ((plus >>> H) >>> H)                             ≡⟨ cancelʳ hadInv ⟩
  plus ∎

oneMinusPlus : ((one *** minus) >>> cz) ≡ (one *** plus)
oneMinusPlus = begin
  (one *** minus) >>> (id⇔ *** H) >>> cx >>> (id⇔ *** H)              ≡⟨ assoc>>>l ◯ (homL*** ⟩◎⟨id) ⟩ 
  ((one >>> id⇔) *** (minus >>> H)) >>> cx >>> (id⇔ *** H)            ≡⟨ idr>>>l ⟩⊗⟨id ⟩◎⟨id ⟩ 
  (one *** (minus >>> H))>>> cx >>> (id⇔ *** H)                       ≡⟨ idl>>>r ⟩⊗⟨ idr>>>r ⟩◎⟨id ⟩ 
  ((id⇔ >>> one) *** ((minus >>> H) >>> id⇔)) >>> cx >>> (id⇔ *** H)  ≡⟨ homR*** ⟩◎⟨id ◯ assoc>>>r ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** id⇔) >>> cx >>> (id⇔ *** H)    ≡⟨ id⟩◎⟨ (assoc>>>l ◯ e3L ⟩◎⟨id) ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** X) >>> (id⇔ *** H)             ≡⟨ id⟩◎⟨ (homL*** ◯ (idr>>>l ⟩⊗⟨id)) ⟩ 
  (id⇔ *** (minus >>> H)) >>> (one *** (X >>> H))                     ≡⟨ homL*** ◯ (idl>>>l ⟩⊗⟨ assoc>>>r ) ⟩ 
  one *** (minus >>> H >>> X >>> H)                                   ≡⟨ id⟩⊗⟨ minusZ≡plus  ⟩ 
  (one *** plus) ∎


xcxA : id⇔ *** X >>> cx ≡ cx >>> id⇔ *** X
xcxA = begin
  id⇔ *** X >>> cx                   ≡⟨ arrZidR ⟩⊗⟨id ⟩◎⟨id ◯ class*>R ⟩ 
  arrZ ((id⟷ Π.⊗ Π.swap₊) Π.◎ ΠT.cx) ≡⟨ classicalZ xcx ⟩
  arrZ (ΠT.cx Π.◎ (id⟷ Π.⊗ Π.swap₊)) ≡⟨ class>*L ◯ id⟩◎⟨ arrZidL ⟩⊗⟨id ⟩
  cx >>> id⇔ *** X                   ∎


zhcx : (id⇔ *** Z) >>> (id⇔ *** H) >>> cx ≡ cz >>> (id⇔ *** H) >>> (id⇔ *** X)
zhcx = begin
  (id⇔ *** Z) >>> (id⇔ *** H) >>> cx                                ≡⟨ id≡ ⟩
  (id⇔ *** (H >>> X >>> H)) >>> (id⇔ *** H) >>> cx                  ≡⟨ assoc>>>l ◯ (homL*** ◯ (idl>>>l ⟩⊗⟨id)) ⟩◎⟨id ⟩
  (id⇔ *** ((H >>> X >>> H) >>> H)) >>> cx                          ≡⟨ id⟩⊗⟨ pullʳ (cancelʳ hadInv) ⟩◎⟨id ⟩ 
  id⇔ *** (H >>> X) >>> cx                                          ≡⟨ (idl>>>r ⟩⊗⟨id ◯ homR***) ⟩◎⟨id ◯ assoc>>>r ⟩ 
  (id⇔ *** H) >>> (id⇔ *** X) >>> cx                                ≡⟨ id⟩◎⟨ xcxA ⟩
  (id⇔ *** H) >>> cx >>> (id⇔ *** X)                                ≡⟨ id⟩◎⟨ id⟩◎⟨ insertˡ 1*HInv ⟩
  (id⇔ *** H) >>> cx >>> (id⇔ *** H) >>> (id⇔ *** H) >>> (id⇔ *** X) ≡⟨ assoc>>>l ◯ assoc>>>l ◯ assoc>>>r ⟩◎⟨id ⟩
  (id⇔ *** H >>> cx >>> id⇔ *** H) >>> (id⇔ *** H) >>> (id⇔ *** X)  ≡⟨ id≡ ⟩
  cz >>> (id⇔ *** H) >>> (id⇔ *** X)      ∎

measure : measureϕ ≡ (H >>> measureZ >>> H)
measure = begin
  measureϕ               ≡⟨ id≡ ⟩ -- definition
  copyϕ >>> fst          ≡⟨ id≡ ⟩ -- definitions
  (H >>> copyZ >>> (H *** H)) >>> (id⇔ *** discard) >>> unite⋆r   ≡⟨ assoc>>>l ⟩◎⟨id ◯ assoc>>>r ◯ id⟩◎⟨ assoc>>>l ⟩
  (H >>> copyZ) >>> ((H *** H) >>> (id⇔ *** discard)) >>> unite⋆r ≡⟨ id⟩◎⟨ homL*** ⟩◎⟨id ⟩
  (H >>> copyZ) >>> ((H >>> id⇔) *** (H >>> discard)) >>> unite⋆r ≡⟨ id⟩◎⟨ idr>>>l ⟩⊗⟨ discardL H ⟩◎⟨id ⟩
  (H >>> copyZ) >>> H *** discard >>> unite⋆r                     ≡⟨ id⟩◎⟨ seq₂₁*** ⟩◎⟨id ⟩
  (H >>> copyZ) >>> (id⇔ *** discard >>> H *** id⇔) >>> unite⋆r   ≡⟨ assoc>>>r ◯ id⟩◎⟨ (assoc>>>l ◯ assoc>>>l ⟩◎⟨id ◯ assoc>>>r) ⟩  
  H >>> (copyZ >>> id⇔ *** discard) >>> (H *** id⇔) >>> unite⋆r   ≡⟨ id⟩◎⟨ id⟩◎⟨ uniter⋆≡r ⟩ 
  H >>> (copyZ >>> id⇔ *** discard) >>> (unite⋆r >>> H)           ≡⟨ id⟩◎⟨ (assoc>>>l ◯ assoc>>>r ⟩◎⟨id) ⟩
  H >>> (copyZ >>> id⇔ *** discard >>> unite⋆r) >>> H             ≡⟨ id≡ ⟩
  (H >>> measureZ >>> H) ∎

---------------------------------------------------------------------------

