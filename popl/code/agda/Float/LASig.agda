{-# OPTIONS --without-K --exact-split --safe #-}

-- Float Vectors, implemented as functions, as one representation of LASig

module Float.LASig where

open import Data.Float using (Float)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function.Base using (_∘_)

open import LinearAlgebraSig using (LASig)

private
  vec mat : Set → Set
  vec t = t → Float
  mat t = t → t → Float

  aut : Set → Set
  aut t = vec t → vec t

  -- make it clearer that this is direct product.
  _⊕_ : {t₁ t₂ : Set} → aut t₁ → aut t₂ → aut (t₁ ⊎ t₂)
  -- simple definition:
  -- c₁ ⊕ c₂ = λ f → Sum.[ c₁ (f ∘ inj₁) , c₂ (f ∘ inj₂) ]
  -- expanded:
  (c₁ ⊕ c₂) f (inj₁ x) = c₁ (f ∘ inj₁) x
  (c₁ ⊕ c₂) f (inj₂ y) = c₂ (f ∘ inj₂) y

  _⊗_ : {t₁ t₂ : Set} → aut t₁ → aut t₂ → aut (t₁ × t₂)
  _⊗_ {t₁} {t₂} c₁ c₂ f (v₁ , v₂) = c₁ (λ a → c₂ (λ b → f (a , b)) v₂) v₁

FloatVec : LASig
FloatVec = record
  { vec = vec
  ; mat = mat
  ; _⊕_ = _⊕_
  ; _⊗_ = _⊗_
  ; unite+l = λ f → f ∘ inj₂
  ; uniti+l = λ {f (inj₂ x) → f x }
  ; unite*l = λ f x → f (tt , x)
  ; uniti*l = λ f x → f (Prod.proj₂ x)
  ; swap+ = λ f → f ∘ Sum.swap
  ; swap× = λ f → f ∘ Prod.swap
  ; assocl+ = λ f → f ∘ Sum.assocʳ
  ; assocr+ = λ f → f ∘ Sum.assocˡ
  ; assocl* = λ f → f ∘ Prod.assocʳ
  ; assocr* = λ f → f ∘ Prod.assocˡ
  ; absorbl′ = λ { _ () }
  ; factorzr′ = λ {_ ( _ , () )}
  ; dist′ = λ f → f ∘ Sum.[ Prod.map₁ inj₁ , Prod.map₁ inj₂ ]
  ; factor′ = λ f → f ∘ λ { (a , b) → Sum.map (_, b) (_, b) a }
  ; idp = λ x → x
  ; _⊚_ = λ f g → g ∘ f
  ; _⊕′_ = λ f g h → Sum.[ f (h ∘ inj₁) , g (h ∘ inj₂) ]
  ; _⊛_ = λ A₁₃ B₂₄ v (i , j) → A₁₃ (λ a → B₂₄ (λ b → v (a , b)) j) i
  ; true = λ { (inj₁ x) → 0.0 ; (inj₂ y) → 1.0}
  ; false = λ { (inj₁ x) → 1.0 ; (inj₂ y) → 0.0}
  }
