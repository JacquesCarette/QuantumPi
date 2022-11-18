{-# OPTIONS --without-K --exact-split --safe #-}

module S where



data U : Set where
  O : U
  I : U
  _+ᵤ_ : U → U → U
  _×ᵤ_ : U → U → U

evalZ : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → Vec t₁ → Vec t₂
evalZ {t₁} {t₂} c = eval c

evalH : {t₁ t₂ : U} → t₁ ⟷₁ t₂ → Vec t₁ → Vec t₂
evalH {t₁} {t₂} c = R⁻¹ t₂ ∘ eval c ∘ R t₁

