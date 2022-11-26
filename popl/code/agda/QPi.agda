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
  renaming (zero to kzero; assertZero to bzero)
open import Instances using (Fwd)
  renaming (evalTL₁ to evalPi; evalSE to evalArr)

---------------------------------------------------------------------------
-- The surface Quantum Pi language

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

𝟚 : U
𝟚 = I +ᵤ I

record QPI : Set where
  field
    -- (+,0) monoid
    unite₊   : Fwd (t +ᵤ O) t
    uniti₊   : Fwd t (t +ᵤ O)
    swap₊    : Fwd (t₁ +ᵤ t₂) (t₂ +ᵤ t₁)
    assocl₊  : Fwd (t₁ +ᵤ (t₂ +ᵤ t₃)) ((t₁ +ᵤ t₂) +ᵤ t₃)
    assocr₊  : Fwd ((t₁ +ᵤ t₂) +ᵤ t₃) (t₁ +ᵤ (t₂ +ᵤ t₃))
    -- (*,1) monoid
    unite⋆   : Fwd (t ×ᵤ I) t
    uniti⋆   : Fwd t (t ×ᵤ I)
    swap⋆    : Fwd (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
    assocl⋆  : Fwd (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ((t₁ ×ᵤ t₂) ×ᵤ t₃)
    assocr⋆  : Fwd ((t₁ ×ᵤ t₂) ×ᵤ t₃) (t₁ ×ᵤ (t₂ ×ᵤ t₃))
    -- distributivity
    absorbr   : Fwd (O ×ᵤ t) O
    factorzl  : Fwd O (O ×ᵤ t)
    dist      : Fwd ((t₁ +ᵤ t₂) ×ᵤ t₃) ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃))
    factor    : Fwd ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)) ((t₁ +ᵤ t₂) ×ᵤ t₃)
    -- composition
    id⟷  : Fwd t t
--    _◎_   : (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
--    _⊕_   : (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
--    _⊗_   : (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)
--    inv   : (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    -- arrow layer
    arrZ  : (t₁ ⟷₁ t₂) → Fwd t₁ t₂
    arrϕ  : (t₁ ⟷₁ t₂) → Fwd t₁ t₂
    -- multiplicative structure
    uniteA⋆   : Fwd (t ×ᵤ I) t
    unitiA⋆   : Fwd t (t ×ᵤ I)
    swapA⋆    : Fwd (t₁ ×ᵤ t₂) (t₂ ×ᵤ t₁)
    assoclA⋆  : Fwd (t₁ ×ᵤ (t₂ ×ᵤ t₃)) ((t₁ ×ᵤ t₂) ×ᵤ t₃)
    assocrA⋆  : Fwd ((t₁ ×ᵤ t₂) ×ᵤ t₃) (t₁ ×ᵤ (t₂ ×ᵤ t₃))
    -- composition
    idA⇔    : Fwd t t
--    _>>>_   : (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)
--    _***_   : (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (t₁ ×ᵤ t₂ ⇔ t₃ ×ᵤ t₄)
--    invA    : (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
    -- states and effects
    zeroA        : Fwd I 𝟚
    assertZeroA  : Fwd 𝟚 I

piz pih : (t₁ ⟷₁ t₂) → TList t₁ t₂
piz c = cons₁ c nil
pih c = cons₂ c nil

pizA pihA : (t₁ ⟷₁ t₂) → StEffPi t₁ t₂
pizA = arr ∘ piz
pihA = arr ∘ pih


QPi : QPI
QPi = record
  {
  -- pi layer
    unite₊ = Pi.unite+ GenericPi
  ; uniti₊   = Pi.uniti+ GenericPi
  ; swap₊    = Pi.swap+ GenericPi
  ; assocl₊  = Pi.assocl+ GenericPi
  ; assocr₊  = Pi.assocr+ GenericPi
  ; unite⋆  = Pi.unite* GenericPi
  ; uniti⋆   =  Pi.uniti* GenericPi
  ; swap⋆    =  Pi.swap× GenericPi
  ; assocl⋆  =  Pi.assocl* GenericPi
  ; assocr⋆  =  Pi.assocr* GenericPi
  ; absorbr   =  Pi.absorbr′ GenericPi
  ; factorzl  =  Pi.factorzl′ GenericPi
  ; dist      =  Pi.dist′ GenericPi
  ; factor   =  Pi.factor′ GenericPi
  ; id⟷  =  Pi.idp GenericPi
--  ; _◎_  =  ?
--  ; _⊕_   = ?
--  ; _⊗_  = ?
--  ; inv   = ?
  -- arrow layer
  ; arrZ  = evalArr ∘ pizA
  ; arrϕ  = evalArr ∘ pihA
  ; uniteA⋆  = evalArr (pizA _⟷₁_.unite⋆)
  ; unitiA⋆  = evalArr (pizA _⟷₁_.uniti⋆)
  ; swapA⋆    = evalArr (pizA _⟷₁_.swap⋆)
  ; assoclA⋆  = evalArr (pizA _⟷₁_.assocl⋆) 
  ; assocrA⋆  = evalArr (pizA _⟷₁_.assocr⋆) 
  ; idA⇔    = evalArr (pizA _⟷₁_.id⟷₁) 
--  ; _>>>_   = ?
--  ; _***_  = ?
--  ; invA    = ?
  ; zeroA        = evalArr kzero 
  ; assertZeroA = evalArr bzero
  }
