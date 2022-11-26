module QPi where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Float using (Float) renaming (_+_ to _+f_; _*_ to _*f_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Data.Vec using (Vec; []; _∷_; _++_; map; concat; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiSyntax using (U; O; I; _+ᵤ_; _×ᵤ_; _⟷₁_)
open import PiTagless using (Pi)
open import GenericPi using (GenericPi)
open import Amalgamation using (TList; cons₁; cons₂; nil)
open import StatesAndEffects using (StEffPi; arr)  
open import Instances using (Fwd)
  renaming (evalTL₁ to evalPi; evalSE to evalArr)

---------------------------------------------------------------------------
-- The surface Quantum Pi language

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

𝟚 : U
𝟚 = I +ᵤ I

record QPI (_⟷_ _⇔_ : U → U → Set) : Set where
  field
    -- (+,0) monoid
    unite₊   : t +ᵤ O ⟷  t
    uniti₊   : t ⟷  t +ᵤ O
    swap₊    : t₁ +ᵤ t₂ ⟷  t₂ +ᵤ t₁
    assocl₊  : t₁ +ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ +ᵤ t₂) +ᵤ t₃
    assocr₊  : (t₁ +ᵤ t₂) +ᵤ t₃ ⟷ t₁ +ᵤ (t₂ +ᵤ t₃)
    -- (*,1) monoid
    unite⋆   : t ×ᵤ I ⟷  t
    uniti⋆   : t ⟷ t ×ᵤ I
    swap⋆    : t₁ ×ᵤ t₂ ⟷  t₂ ×ᵤ t₁
    assocl⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
    assocr⋆  : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
    -- distributivity
    absorbr   : O ×ᵤ t ⟷ O
    factorzl  : O ⟷  O ×ᵤ t
    dist      : (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
    factor    : {t₁ t₂ t₃ : U} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
    -- composition
    id⟷  : t ⟷  t
    _◎_   : (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_   : (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
    _⊗_   : (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)
    inv   : (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    -- arrow layer
    arrZ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂) 
    arrϕ  : (t₁ ⟷ t₂) → (t₁ ⇔ t₂)
    -- multiplicative structure
    uniteA⋆   : t ×ᵤ I ⇔ t
    unitiA⋆   : t ⇔ t ×ᵤ I
    swapA⋆    : t₁ ×ᵤ t₂ ⇔  t₂ ×ᵤ t₁
    assoclA⋆  : t₁ ×ᵤ (t₂ ×ᵤ t₃) ⇔ (t₁ ×ᵤ t₂) ×ᵤ t₃
    assocrA⋆  : (t₁ ×ᵤ t₂) ×ᵤ t₃ ⇔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
    -- composition
    idA⇔    : t ⇔ t
    _>>>_   : (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)
    _***_   : (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (t₁ ×ᵤ t₂ ⇔ t₃ ×ᵤ t₄)
    invA    : (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
    -- states and effects
    zeroA        : I ⇔ 𝟚
    assertZeroA  : 𝟚 ⇔ I

piz : (t₁ ⟷₁ t₂) → StEffPi t₁ t₂
piz c = arr (cons₁ c nil)

Qpi : QPI Fwd Fwd
Qpi = record
  {
  -- pi layer
    unite₊   = Pi.unite+ GenericPi
  ; uniti₊   = Pi.uniti+ GenericPi
  ; swap₊    = Pi.swap+ GenericPi
  ; assocl₊  = Pi.assocl+ GenericPi
  ; assocr₊  = Pi.assocr+ GenericPi
  ; unite⋆  = Pi.unite* GenericPi
  ; uniti⋆   = Pi.uniti* GenericPi 
  ; swap⋆    = Pi.swap× GenericPi 
  ; assocl⋆  = Pi.assocl* GenericPi 
  ; assocr⋆  = Pi.assocr* GenericPi 
  ; absorbr   = Pi.absorbr′ GenericPi 
  ; factorzl  = Pi.factorzl′ GenericPi 
  ; dist      = Pi.dist′ GenericPi 
  ; factor   = Pi.factor′ GenericPi 
  ; id⟷  = Pi.idp GenericPi
  ; _◎_  = Pi._⊚_ GenericPi 
  ; _⊕_   = Pi._⊕′_  GenericPi 
  ; _⊗_  = Pi._⊛_ GenericPi 
  ; inv   = {!!}
  -- arrow layer
  ; arrZ  = λ c → evalArr {!!}
  ; arrϕ  = {!!}
  ; uniteA⋆  = {!!} 
  ; unitiA⋆  = {!!}
  ; swapA⋆    = {!!}
  ; assoclA⋆  = {!!} 
  ; assocrA⋆  = {!!} 
  ; idA⇔    = {!!} 
  ; _>>>_   = {!!} 
  ; _***_  = {!!} 
  ; invA    = {!!} 
  ; zeroA        = {!!} 
  ; assertZeroA = {!!}
  }
