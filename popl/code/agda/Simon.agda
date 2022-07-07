{-# OPTIONS --without-K --exact-split --safe #-}

module Simon where

open import PiSyntax
import ArrowsOverAmalg as A
open import StatesAndEffects
-- open import Instances using (eval)

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : U

-- Simon fragments

A[B[CD]]→[AC][BD]  : t₁ ×ᵤ (t₂ ×ᵤ (t₃ ×ᵤ t₄)) ⟷₁ (t₁ ×ᵤ t₃) ×ᵤ (t₂ ×ᵤ t₄)
A[B[CD]]→[AC][BD] {t₁} {t₂} {t₃} {t₄} =
 t₁ ×ᵤ (t₂ ×ᵤ (t₃ ×ᵤ t₄))   ⟨ id⟷₁ ⊗ assocl⋆ ⟩
 t₁ ×ᵤ (t₂ ×ᵤ t₃) ×ᵤ t₄     ⟨ id⟷₁ ⊗ swap⋆ ⊗ id⟷₁ ⟩
 t₁ ×ᵤ (t₃ ×ᵤ t₂) ×ᵤ t₄     ⟨ id⟷₁ ⊗ assocr⋆ ⟩
 t₁ ×ᵤ t₃ ×ᵤ (t₂ ×ᵤ t₄)     ⟨ assocl⋆ ⟩
 (t₁ ×ᵤ t₃) ×ᵤ (t₂ ×ᵤ t₄)   ∎

A[B[CD]]→[AD][BC]  : t₁ ×ᵤ (t₂ ×ᵤ (t₃ ×ᵤ t₄)) ⟷₁ (t₁ ×ᵤ t₄) ×ᵤ (t₂ ×ᵤ t₃)
A[B[CD]]→[AD][BC] {t₁} {t₂} {t₃} {t₄} =
 t₁ ×ᵤ (t₂ ×ᵤ (t₃ ×ᵤ t₄))   ⟨ id⟷₁ ⊗ assocl⋆ ⟩
 t₁ ×ᵤ (t₂ ×ᵤ t₃) ×ᵤ t₄     ⟨ id⟷₁ ⊗ swap⋆ ⟩
 t₁ ×ᵤ t₄ ×ᵤ (t₂ ×ᵤ t₃)     ⟨ assocl⋆ ⟩
 (t₁ ×ᵤ t₄) ×ᵤ (t₂ ×ᵤ t₃)   ∎

A[B[CD]]→[BC][AD]  : t₁ ×ᵤ (t₂ ×ᵤ (t₃ ×ᵤ t₄)) ⟷₁ (t₂ ×ᵤ t₃) ×ᵤ (t₁ ×ᵤ t₄)
A[B[CD]]→[BC][AD] {t₁} {t₂} {t₃} {t₄} =
  t₁ ×ᵤ (t₂ ×ᵤ (t₃ ×ᵤ t₄))  ⟨ id⟷₁ ⊗ assocl⋆ ⟩
  t₁ ×ᵤ (t₂ ×ᵤ t₃) ×ᵤ t₄    ⟨ id⟷₁ ⊗ swap⋆ ⟩
  t₁ ×ᵤ t₄ ×ᵤ (t₂ ×ᵤ t₃)    ⟨ assocl⋆ ⟩
  (t₁ ×ᵤ t₄) ×ᵤ (t₂ ×ᵤ t₃)  ⟨ swap⋆ ⟩
  (t₂ ×ᵤ t₃) ×ᵤ (t₁ ×ᵤ t₄)  ∎

A[B[CD]]→[BD][AC]  : t₁ ×ᵤ (t₂ ×ᵤ (t₃ ×ᵤ t₄)) ⟷₁ (t₂ ×ᵤ t₄) ×ᵤ (t₁ ×ᵤ t₃)
A[B[CD]]→[BD][AC] {t₁} {t₂} {t₃} {t₄} = A[B[CD]]→[AC][BD] ◎ swap⋆

[AC][BD]→[AD][BC] : {t₁ t₂ t₃ t₄ : U} → (t₁ ×ᵤ t₃) ×ᵤ (t₂ ×ᵤ t₄) ⟷₁ (t₁ ×ᵤ t₄) ×ᵤ (t₂ ×ᵤ t₃)
[AC][BD]→[AD][BC] {t₁} {t₂} {t₃} {t₄} =
  (t₁ ×ᵤ t₃) ×ᵤ (t₂ ×ᵤ t₄)   ⟨ assocr⋆ ⟩
   t₁ ×ᵤ (t₃ ×ᵤ (t₂ ×ᵤ t₄))  ⟨ id⟷₁ ⊗ assocl⋆ ⟩
   t₁ ×ᵤ ((t₃ ×ᵤ t₂) ×ᵤ t₄)  ⟨ id⟷₁ ⊗ swap⋆ ⟩
   t₁ ×ᵤ (t₄ ×ᵤ (t₃ ×ᵤ t₂))  ⟨ assocl⋆ ⟩
   (t₁ ×ᵤ t₄) ×ᵤ (t₃ ×ᵤ t₂)  ⟨ id⟷₁ ⊗ swap⋆ ⟩
  (t₁ ×ᵤ t₄) ×ᵤ (t₂ ×ᵤ t₃)   ∎

-- The 2 Hadamard gates
simon₁ : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷₁ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
simon₁ = swap₊ ⊗ swap₊ ⊗ id⟷₁ ⊗ id⟷₁

-- The core of the circuit
simon₂ : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ⟷₁ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
simon₂ =
     A[B[CD]]→[AC][BD]  ◎ (cnot ⊗ id⟷₁) ◎
     [AC][BD]→[AD][BC]  ◎ (cnot ⊗ id⟷₁) ◎ -- swap⋆ to do [AD][BC]→[BC][AD]
     swap⋆              ◎ (cnot ⊗ id⟷₁) ◎
     -- up to renaming, [AC][BD]→[AD][BC] does the same as [BC][AD]→[BD][AC]
     [AC][BD]→[AD][BC]  ◎ (cnot ⊗ id⟷₁) ◎ !⟷₁ A[B[CD]]→[BD][AC]

{--

1 -> unit intro
1 x 1 x 1 x 1 -> zero
2 x 2 x 2 x 2 -> simon1 ; simon2 ; simon1

--}

simon : StEffPi I (𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚)
simon =
  arr (A.uniti*l              A.>>>
       A.idzh A.*** A.uniti*l A.>>>
       A.idzh A.*** (A.idzh A.*** A.uniti*l)) >>>>
  (zero *** (zero *** (zero *** zero)))       >>>>
  arr (A.arr₂ simon₁ A.>>>
       A.arr₁ simon₂ A.>>>
       A.arr₂ simon₁)
