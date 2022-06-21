{-# OPTIONS --without-K --exact-split --safe #-}

module PiZ where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_)

open import PiSyntax

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

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
