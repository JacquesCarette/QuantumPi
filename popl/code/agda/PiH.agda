{-# OPTIONS --without-K --exact-split --safe #-}

module PiH where

open import Data.Float as F using (Float)
open import Data.List using (List; map; foldr)
open import Data.Product as Prod using (_,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)

open import PiSyntax using (U; I; O; _+ᵤ_; _×ᵤ_)
open import PiBij using (⟦_⟧; enum)
open import PiTagless using (Pi)
open import Unitary using (𝒰; R; R⁻¹)

-----------------------------------------------------------------------
-- Below we start the work that correspoints to the H interpretation

H : (t : U) → Set
H = 𝒰

Fwd : U → U → Set
Fwd t₁ t₂ = H t₁ → H t₂

sumf : List Float → Float
sumf = foldr F._+_ (F.fromℕ 0)

-- We can show that, in the H basis, we can make Fwd an interpretation of Pi.
-- But this is not the one we really want, as it is not conjugated.
-- Note how the interpretation is λ f → f ∘ g where g is the opposite of the Fwd interpretation for the
-- evaluator for PiZ
PiH₀ : Pi Fwd
PiH₀ = record
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

-- Here is the one we want. We pre-conjugate with R⁻¹ and post-apply R, to the version above.
PiH : Pi Fwd
PiH = record
  { unite+l = λ {t} → R⁻¹ t ∘ unite+l ∘ R (O +ᵤ t)
  ; uniti+l = λ {t} → R⁻¹ (O +ᵤ t) ∘ uniti+l ∘ R t
  ; unite*l = λ {t} → R⁻¹ t ∘ unite*l ∘ R (I ×ᵤ t)
  ; uniti*l = λ {t} → R⁻¹ (I ×ᵤ t) ∘ uniti*l ∘ R t
  ; swap+ = λ {t₀} {t₁} → R⁻¹ (t₁ +ᵤ t₀) ∘ swap+ ∘ R (t₀ +ᵤ t₁)
  ; swap× = λ {t₀} {t₁} → R⁻¹ (t₁ ×ᵤ t₀) ∘ swap× ∘ R (t₀ ×ᵤ t₁)
  ; assocl+ = λ {t₀} {t₁} {t₂} → R⁻¹ ((t₀ +ᵤ t₁) +ᵤ t₂) ∘ assocl+ ∘ R (t₀ +ᵤ (t₁ +ᵤ t₂))
  ; assocr+ = λ {t₀} {t₁} {t₂} →  R⁻¹ (t₀ +ᵤ (t₁ +ᵤ t₂)) ∘ assocr+ ∘ R ((t₀ +ᵤ t₁) +ᵤ t₂)
  ; assocl* = λ {t₀} {t₁} {t₂} → R⁻¹ ((t₀ ×ᵤ t₁) ×ᵤ t₂) ∘ assocl* ∘ R (t₀ ×ᵤ (t₁ ×ᵤ t₂))
  ; assocr* = λ {t₀} {t₁} {t₂} → R⁻¹ (t₀ ×ᵤ (t₁ ×ᵤ t₂)) ∘ assocr* ∘ R ((t₀ ×ᵤ t₁) ×ᵤ t₂)
  ; absorbr′ = λ {t} → R⁻¹ O ∘ absorbr′ ∘ R (O ×ᵤ t)
  ; absorbl′ = λ {t} → R⁻¹ O ∘ absorbl′ ∘ R (t ×ᵤ O)
  ; factorzr′ = λ {t} → R⁻¹ (t ×ᵤ O) ∘ factorzr′ ∘ R O
  ; factorzl′ = λ {t} → R⁻¹ (O ×ᵤ t) ∘ factorzl′ ∘ R O
  ; dist′ = λ {t₀} {t₁} {t₂} → R⁻¹ ((t₀ ×ᵤ t₂) +ᵤ t₁ ×ᵤ t₂) ∘ dist′ ∘ R ((t₀ +ᵤ t₁) ×ᵤ t₂)
  ; distl′ = λ {t₀} {t₁} {t₂} → R⁻¹ ((t₀ ×ᵤ t₁) +ᵤ t₀ ×ᵤ t₂) ∘ distl′ ∘ R (t₀ ×ᵤ t₁ +ᵤ t₂)
  ; factor′ = λ {t₀} {t₁} {t₂} → R⁻¹ ((t₀ +ᵤ t₂) ×ᵤ t₁) ∘ factor′ ∘ R ((t₀ ×ᵤ t₁) +ᵤ t₂ ×ᵤ t₁)
  ; factorl′ = λ {t₀} {t₁} {t₂} → R⁻¹ (t₀ ×ᵤ t₁ +ᵤ t₂) ∘ factorl′ ∘ R ((t₀ ×ᵤ t₁) +ᵤ t₀ ×ᵤ t₂)
  ; idp = λ {t} → R⁻¹ t ∘ idp ∘ R t
  ; _⊚_ = λ {t₀} {t₁} {t₂} c₀ c₁ → R⁻¹ t₂ ∘ (c₀ ⊚ c₁) ∘ R t₀
  ; _⊕′_ = λ {t₀} {t₁} {t₂} {t₃} c₀ c₁ → R⁻¹ (t₁ +ᵤ t₃) ∘ (c₀ ⊕′ c₁) ∘ R (t₀ +ᵤ t₂)
  ; _⊛_ = λ {t₀} {t₁} {t₂} {t₃} c₀ c₁ → R⁻¹ (t₁ ×ᵤ t₃) ∘ (c₀ ⊛ c₁) ∘ R (t₀ ×ᵤ t₂)
  }
  where open Pi PiH₀

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
