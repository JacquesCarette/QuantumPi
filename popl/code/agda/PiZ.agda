{-# OPTIONS --without-K --exact-split --safe #-}

module PiZ where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; cartesianProduct)
open import Data.Product as Prod using (_,_; _×_; swap)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_; flip)

open import PiSyntax
open import PiTagless

-------------------------------------------------------------------------------------
-- Conventional denotations

⟦_⟧z : (t : U) → Set
⟦ O ⟧z = ⊥
⟦ I ⟧z = ⊤
⟦ t₁ +ᵤ t₂ ⟧z = ⟦ t₁ ⟧z ⊎ ⟦ t₂ ⟧z
⟦ t₁ ×ᵤ t₂ ⟧z = ⟦ t₁ ⟧z × ⟦ t₂ ⟧z

-- Interpreter

eval : {t₁ t₂ : U} → (t₁ ⟷₁ t₂) → ⟦ t₁ ⟧z → ⟦ t₂ ⟧z
eval unite₊l (inj₂ v) = v
eval uniti₊l v = inj₂ v
eval unite⋆l (tt , v)= v
eval uniti⋆l v = (tt , v)
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval dist (inj₁ v , w) = inj₁ (v , w)
eval dist (inj₂ v , w) = inj₂ (v , w)
eval distl (v , inj₁ w) = inj₁ (v , w)
eval distl (v , inj₂ w) = inj₂ (v , w)
eval factor (inj₁ (v , w)) = (inj₁ v , w)
eval factor (inj₂ (v , w)) = (inj₂ v , w)
eval factorl (inj₁ (v , w)) = (v , inj₁ w)
eval factorl (inj₂ (v , w)) = (v , inj₂ w)
eval id⟷₁ v = v
eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

-- we can enumerate our types
enum : (t : U) → List ⟦ t ⟧z
enum O = []
enum I = tt ∷ []
enum (t +ᵤ t₁) = map inj₁ (enum t) ++ map inj₂ (enum t₁)
enum (t ×ᵤ t₁) = cartesianProduct (enum t) (enum t₁)

-- The language is an instance of the record
Pi⟷ : Pi _⟷₁_
Pi⟷ = record
  { unite+l = unite₊l
  ; uniti+l = uniti₊l
  ; unite*l = unite⋆l
  ; uniti*l = uniti⋆l
  ; swap+ = swap₊
  ; swap× = swap⋆
  ; assocl+ = assocl₊
  ; assocr+ = assocr₊
  ; assocl* = assocl⋆
  ; assocr* = assocr⋆
  ; absorbr′ = absorbr
  ; absorbl′ = absorbl
  ; factorzr′ = factorzr
  ; factorzl′ = factorzl
  ; dist′ = dist
  ; distl′ = distl
  ; factor′ = factor
  ; factorl′ = factorl
  ; idp = id⟷₁
  ; _⊚_ = _◎_
  ; _⊕′_ = _⊕_
  ; _⊛_ = _⊗_
  }

Fwd : (t₁ t₂ : U) → Set
Fwd t₁ t₂ = ⟦ t₁ ⟧z → ⟦ t₂ ⟧z

-- So is the interpreter!
-- note how the action induced by each combinator is much clearer here than in `eval`
PiFwd : Pi Fwd
PiFwd = record
  { unite+l = λ { (inj₂ x) → x }
  ; uniti+l = inj₂
  ; unite*l = Prod.proj₂
  ; uniti*l = tt ,_
  ; swap+ = Sum.swap
  ; swap× = swap
  ; assocl+ = Sum.assocˡ
  ; assocr+ = Sum.assocʳ
  ; assocl* = Prod.assocˡ
  ; assocr* = Prod.assocʳ
  ; absorbr′ = Prod.proj₁
  ; absorbl′ = Prod.proj₂
  ; factorzr′ = λ ()
  ; factorzl′ = λ ()
  ; dist′ = λ { (a , b) → Sum.map (_, b) (_, b) a }
  ; distl′ = λ (a , b) → Sum.map (a ,_) (a ,_) b
  ; factor′ = Sum.[ Prod.map₁ inj₁ , Prod.map₁ inj₂ ]
  ; factorl′ = Sum.[ Prod.map₂ inj₁ , Prod.map₂ inj₂ ]
  ; idp = id
  ; _⊚_ = λ f g → g ∘ f
  ; _⊕′_ = λ c₁ c₂ → Sum.map c₁ c₂
  ; _⊛_ = λ c₁ c₂ → Prod.map c₁ c₂
  }

-- And it's all reversible
Bwd : (t₁ t₂ : U) → Set
Bwd t₁ t₂ = ⟦ t₂ ⟧z → ⟦ t₁ ⟧z

-- The generic reverse will do it, no need to rewrite
PiBwd : Pi Bwd
PiBwd = reverse Fwd PiFwd
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
