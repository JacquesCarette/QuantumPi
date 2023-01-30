{-# OPTIONS --without-K --exact-split --safe #-}

module Pi.Equivalences where

open import Pi.Types
open import Pi.Language

infix 5 _⟷₂_

data _⟷₂_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          c₁ ◎ (c₂ ◎ c₃) ⟷₂ (c₁ ◎ c₂) ◎ c₃
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          ((c₁ ◎ c₂) ◎ c₃) ⟷₂ (c₁ ◎ (c₂ ◎ c₃))
  assocl⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⟷₂ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocl⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆) ⟷₂ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃))
  assocl⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)) ⟷₂ ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆)
  assocr⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⟷₂ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
           (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃))) ⟷₂ (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assocr⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⟷₂ (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃)))
  assocr⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  dist⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
          ((((a ⊕ b) ⊗ c) ◎ dist)) ⟷₂ ((dist ◎ ((a ⊗ c) ⊕ (b ⊗ c))))
  dist⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
          (dist ◎ ((a ⊗ c) ⊕ (b ⊗ c))) ⟷₂ (((a ⊕ b) ⊗ c) ◎ dist)
  factor⟷₂l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
          (((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor) ⟷₂ (factor ◎ ((a ⊕ b) ⊗ c))
  factor⟷₂r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
          (factor ◎ ((a ⊕ b) ⊗ c)) ⟷₂ (((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor)
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⟷₂ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⟷₂ (id⟷ ◎ c)
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⟷₂ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⟷₂ (c ◎ id⟷)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ !⟷ c) ⟷₂ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⟷₂ (c ◎ !⟷ c)
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (!⟷ c ◎ c) ⟷₂ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⟷₂ (!⟷ c ◎ c)
  unite₊l⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (unite₊l ◎ c₂) ⟷₂ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          ((c₁ ⊕ c₂) ◎ unite₊l) ⟷₂ (unite₊l ◎ c₂)
  uniti₊l⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⟷₂ (c₂ ◎ uniti₊l)
  uniti₊l⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti₊l) ⟷₂ (uniti₊l ◎ (c₁ ⊕ c₂))
  unite₊r⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (unite₊r ◎ c₂) ⟷₂ ((c₂ ⊕ c₁) ◎ unite₊r)
  unite₊r⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          ((c₂ ⊕ c₁) ◎ unite₊r) ⟷₂ (unite₊r ◎ c₂)
  uniti₊r⟷₂l : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (uniti₊r ◎ (c₂ ⊕ c₁)) ⟷₂ (c₂ ◎ uniti₊r)
  uniti₊r⟷₂r : {t₁ t₂ : U} {c₁ : O ⟷ O} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti₊r) ⟷₂ (uniti₊r ◎ (c₂ ⊕ c₁))
  swapl₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          ((c₂ ⊕ c₁) ◎ swap₊) ⟷₂ (swap₊ ◎ (c₁ ⊕ c₂))
  unitel⋆⟷₂l : {t₁ t₂ : U} {c₁ : I ⟷ I} {c₂ : t₁ ⟷ t₂} →
          (unite⋆l ◎ c₂) ⟷₂ ((c₁ ⊗ c₂) ◎ unite⋆l)
  uniter⋆⟷₂l : {t₁ t₂ : U} {c₁ : I ⟷ I} {c₂ : t₁ ⟷ t₂} →
          ((c₁ ⊗ c₂) ◎ unite⋆l) ⟷₂ (unite⋆l ◎ c₂)
  unitil⋆⟷₂l : {t₁ t₂ : U} {c₁ : I ⟷ I} {c₂ : t₁ ⟷ t₂} →
          (uniti⋆l ◎ (c₁ ⊗ c₂)) ⟷₂ (c₂ ◎ uniti⋆l)
  unitir⋆⟷₂l : {t₁ t₂ : U} {c₁ : I ⟷ I} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti⋆l) ⟷₂ (uniti⋆l ◎ (c₁ ⊗ c₂))
  unitel⋆⟷₂r : {t₁ t₂ : U} {c₁ : I ⟷ I} {c₂ : t₁ ⟷ t₂} →
          (unite⋆r ◎ c₂) ⟷₂ ((c₂ ⊗ c₁) ◎ unite⋆r)
  uniter⋆⟷₂r : {t₁ t₂ : U} {c₁ : I ⟷ I} {c₂ : t₁ ⟷ t₂} →
          ((c₂ ⊗ c₁) ◎ unite⋆r) ⟷₂ (unite⋆r ◎ c₂)
  unitil⋆⟷₂r : {t₁ t₂ : U} {c₁ : I ⟷ I} {c₂ : t₁ ⟷ t₂} →
          (uniti⋆r ◎ (c₂ ⊗ c₁)) ⟷₂ (c₂ ◎ uniti⋆r)
  unitir⋆⟷₂r : {t₁ t₂ : U} {c₁ : I ⟷ I} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti⋆r) ⟷₂ (uniti⋆r ◎ (c₂ ⊗ c₁))
  swapl⋆⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          (swap⋆ ◎ (c₁ ⊗ c₂)) ⟷₂ ((c₂ ⊗ c₁) ◎ swap⋆)
  swapr⋆⟷₂ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          ((c₂ ⊗ c₁) ◎ swap⋆) ⟷₂ (swap⋆ ◎ (c₁ ⊗ c₂))
  id⟷₂     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⟷₂ c
  trans⟷₂  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} →
         (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
  _⊡_  : {t₁ t₂ t₃ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
  resp⊕⟷₂  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊕ c₂) ⟷₂ (c₃ ⊕ c₄)
  resp⊗⟷₂  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊗ c₂) ⟷₂ (c₃ ⊗ c₄)
--   -- below are the combinators added for the RigCategory structure
  id⟷⊕id⟷⟷₂ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⟷₂ id⟷
  split⊕-id⟷ : {t₁ t₂ : U} → (id⟷ {_+ᵤ_ t₁ t₂}) ⟷₂ (id⟷ ⊕ id⟷)
  hom⊕◎⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  id⟷⊗id⟷⟷₂ : {t₁ t₂ : U} → (id⟷ {t₁} ⊗ id⟷ {t₂}) ⟷₂ id⟷
  split⊗-id⟷ : {t₁ t₂ : U} → (id⟷ {_×ᵤ_ t₁ t₂}) ⟷₂ (id⟷ ⊗ id⟷)
  hom⊗◎⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄))
  hom◎⊗⟷₂ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄))
--   -- associativity triangle
  triangle⊕l : {t₁ t₂ : U} →
    (unite₊r {t₁} ⊕ id⟷ {t₂}) ⟷₂ (assocr₊ ◎ (id⟷ ⊕ unite₊l))
  triangle⊕r : {t₁ t₂ : U} →
    (assocr₊ ◎ (id⟷ {t₁} ⊕ unite₊l)) ⟷₂ (unite₊r ⊕ id⟷ {t₂})
  triangle⊗l : {t₁ t₂ : U} →
    ((unite⋆r {t₁}) ⊗ id⟷ {t₂}) ⟷₂ (assocr⋆ ◎ (id⟷ ⊗ unite⋆l))
  triangle⊗r : {t₁ t₂ : U} →
    (assocr⋆ ◎ (id⟷ {t₁} ⊗ unite⋆l)) ⟷₂ (unite⋆r ⊗ id⟷ {t₂})
  pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
   _⟷₂_ {((t₁ +ᵤ t₂) +ᵤ t₃) +ᵤ t₄}
    (assocr₊ ◎ assocr₊)
    (((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊))
  pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
   _⟷₂_ {((t₁ +ᵤ t₂) +ᵤ t₃) +ᵤ t₄}
    (((assocr₊ ⊕ id⟷ {t₄}) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊))
    (assocr₊ ◎ assocr₊)    
  pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
    _⟷₂_ {((t₁ ×ᵤ t₂) ×ᵤ t₃) ×ᵤ t₄} (assocr⋆ ◎ assocr⋆)
    (((assocr⋆ ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆))
  pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
    _⟷₂_ {((t₁ ×ᵤ t₂) ×ᵤ t₃) ×ᵤ t₄}
    (((assocr⋆ ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆))
    (assocr⋆ ◎ assocr⋆)
--   -- from the braiding
--   -- unit coherence
  unite₊l-coh-l : {t₁ : U} → _⟷₂_ {O +ᵤ t₁} unite₊l (swap₊ ◎ unite₊r)
  unite₊l-coh-r : {t₁ : U} → _⟷₂_ {O +ᵤ t₁} (swap₊ ◎ unite₊r) unite₊l
  unite⋆l-coh-l : {t₁ : U} → _⟷₂_ {I ×ᵤ t₁} unite⋆l (swap⋆ ◎ unite⋆r)
  unite⋆l-coh-r : {t₁ : U} → _⟷₂_ {I ×ᵤ t₁} (swap⋆ ◎ unite⋆r) unite⋆l
  hexagonr⊕l : {t₁ t₂ t₃ : U} →
    _⟷₂_ {(t₁ +ᵤ t₂) +ᵤ t₃}
    ((assocr₊ ◎ swap₊) ◎ assocr₊)
    (((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊))
  hexagonr⊕r : {t₁ t₂ t₃ : U} →
    _⟷₂_ {(t₁ +ᵤ t₂) +ᵤ t₃}
    (((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊))
    ((assocr₊ ◎ swap₊) ◎ assocr₊)
  hexagonl⊕l : {t₁ t₂ t₃ : U} →
    _⟷₂_ {t₁ +ᵤ (t₂ +ᵤ t₃)}
    ((assocl₊ ◎ swap₊) ◎ assocl₊)
    (((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷))
  hexagonl⊕r : {t₁ t₂ t₃ : U} →
    _⟷₂_ {t₁ +ᵤ (t₂ +ᵤ t₃)}
    (((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷))
    ((assocl₊ ◎ swap₊) ◎ assocl₊)
  hexagonr⊗l : {t₁ t₂ t₃ : U} →
    _⟷₂_ {(t₁ ×ᵤ t₂) ×ᵤ t₃}
    ((assocr⋆ ◎ swap⋆) ◎ assocr⋆)
    (((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆))
  hexagonr⊗r : {t₁ t₂ t₃ : U} →
    _⟷₂_ {(t₁ ×ᵤ t₂) ×ᵤ t₃}
    (((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆))
    ((assocr⋆ ◎ swap⋆) ◎ assocr⋆)
  hexagonl⊗l : {t₁ t₂ t₃ : U} →
    _⟷₂_ {t₁ ×ᵤ (t₂ ×ᵤ t₃)}
    ((assocl⋆ ◎ swap⋆) ◎ assocl⋆)
    (((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷))
  hexagonl⊗r : {t₁ t₂ t₃ : U} →
    _⟷₂_ {t₁ ×ᵤ (t₂ ×ᵤ t₃)}
    (((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷))
    ((assocl⋆ ◎ swap⋆) ◎ assocl⋆)
  absorbl⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    ((c₁ ⊗ id⟷ {O}) ◎ absorbl) ⟷₂ (absorbl ◎ id⟷ {O})
  absorbl⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (absorbl ◎ id⟷ {O}) ⟷₂ ((c₁ ⊗ id⟷ {O}) ◎ absorbl)
  factorzr⟷₂l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (id⟷ ◎ factorzr) ⟷₂ (factorzr ◎ (c₁ ⊗ id⟷))
  factorzr⟷₂r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (factorzr ◎ (c₁ ⊗ id⟷)) ⟷₂ (id⟷ ◎ factorzr)
  -- from the coherence conditions of RigCategory
  assocl₊-dist-dist⟷₂l : {t₁ t₂ t₃ t₄ : U} →
   _⟷₂_ {(t₁ +ᵤ t₂ +ᵤ t₃) ×ᵤ t₄}
    (((assocl₊ ⊗ id⟷ {t₄}) ◎ dist) ◎ (dist ⊕ id⟷))
    ((dist ◎ (id⟷ ⊕ dist)) ◎ assocl₊)
  assocl₊-dist-dist⟷₂r : {t₁ t₂ t₃ t₄ : U} →
    ((dist {t₁} ◎ (id⟷ ⊕ dist {t₂} {t₃} {t₄})) ◎ assocl₊) ⟷₂
    (((assocl₊ ⊗ id⟷) ◎ dist) ◎ (dist ⊕ id⟷))

-------------------------------------------------------------------------------------
-- This is invertible too
!⟷₂ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → c₁ ⟷₂ c₂ → c₂ ⟷₂ c₁
!⟷₂ assoc◎l = assoc◎r
!⟷₂ assoc◎r = assoc◎l
!⟷₂ assocl⊕l = assocl⊕r
!⟷₂ assocl⊕r = assocl⊕l
!⟷₂ assocl⊗l = assocl⊗r
!⟷₂ assocl⊗r = assocl⊗l
!⟷₂ assocr⊕r = assocr⊕l
!⟷₂ assocr⊗l = assocr⊗r
!⟷₂ assocr⊗r = assocr⊗l
!⟷₂ assocr⊕l = assocr⊕r
!⟷₂ dist⟷₂l = dist⟷₂r
!⟷₂ dist⟷₂r = dist⟷₂l
!⟷₂ factor⟷₂l = factor⟷₂r
!⟷₂ factor⟷₂r = factor⟷₂l
!⟷₂ idl◎l = idl◎r
!⟷₂ idl◎r = idl◎l
!⟷₂ idr◎l = idr◎r
!⟷₂ idr◎r = idr◎l
!⟷₂ linv◎l = linv◎r
!⟷₂ linv◎r = linv◎l
!⟷₂ rinv◎l = rinv◎r
!⟷₂ rinv◎r = rinv◎l
!⟷₂ unite₊l⟷₂l = unite₊l⟷₂r
!⟷₂ unite₊l⟷₂r = unite₊l⟷₂l
!⟷₂ uniti₊l⟷₂l = uniti₊l⟷₂r
!⟷₂ uniti₊l⟷₂r = uniti₊l⟷₂l
!⟷₂ unite₊r⟷₂l = unite₊r⟷₂r
!⟷₂ unite₊r⟷₂r = unite₊r⟷₂l
!⟷₂ uniti₊r⟷₂l = uniti₊r⟷₂r
!⟷₂ uniti₊r⟷₂r = uniti₊r⟷₂l
!⟷₂ swapl₊⟷₂ = swapr₊⟷₂
!⟷₂ swapr₊⟷₂ = swapl₊⟷₂
!⟷₂ unitel⋆⟷₂l = uniter⋆⟷₂l
!⟷₂ uniter⋆⟷₂l = unitel⋆⟷₂l
!⟷₂ unitil⋆⟷₂l = unitir⋆⟷₂l
!⟷₂ unitir⋆⟷₂l = unitil⋆⟷₂l
!⟷₂ unitel⋆⟷₂r = uniter⋆⟷₂r
!⟷₂ uniter⋆⟷₂r = unitel⋆⟷₂r
!⟷₂ unitil⋆⟷₂r = unitir⋆⟷₂r
!⟷₂ unitir⋆⟷₂r = unitil⋆⟷₂r
!⟷₂ swapl⋆⟷₂ = swapr⋆⟷₂
!⟷₂ swapr⋆⟷₂ = swapl⋆⟷₂
!⟷₂ id⟷₂ = id⟷₂
!⟷₂ (trans⟷₂ x x₁) = trans⟷₂ (!⟷₂ x₁) (!⟷₂ x)
!⟷₂ (x ⊡ x₁) = !⟷₂ x ⊡ !⟷₂ x₁
!⟷₂ (resp⊕⟷₂ x x₁) = resp⊕⟷₂ (!⟷₂ x) (!⟷₂ x₁)
!⟷₂ (resp⊗⟷₂ x x₁) = resp⊗⟷₂ (!⟷₂ x) (!⟷₂ x₁)
!⟷₂ id⟷⊕id⟷⟷₂ = split⊕-id⟷
!⟷₂ split⊕-id⟷ = id⟷⊕id⟷⟷₂
!⟷₂ hom⊕◎⟷₂ = hom◎⊕⟷₂
!⟷₂ hom◎⊕⟷₂ = hom⊕◎⟷₂
!⟷₂ id⟷⊗id⟷⟷₂ = split⊗-id⟷
!⟷₂ split⊗-id⟷ = id⟷⊗id⟷⟷₂
!⟷₂ hom⊗◎⟷₂ = hom◎⊗⟷₂
!⟷₂ hom◎⊗⟷₂ = hom⊗◎⟷₂
!⟷₂ triangle⊕l = triangle⊕r
!⟷₂ triangle⊕r = triangle⊕l
!⟷₂ triangle⊗l = triangle⊗r
!⟷₂ triangle⊗r = triangle⊗l
!⟷₂ pentagon⊕l = pentagon⊕r
!⟷₂ pentagon⊕r = pentagon⊕l
!⟷₂ pentagon⊗l = pentagon⊗r
!⟷₂ pentagon⊗r = pentagon⊗l
!⟷₂ unite₊l-coh-l = unite₊l-coh-r
!⟷₂ unite₊l-coh-r = unite₊l-coh-l
!⟷₂ unite⋆l-coh-l = unite⋆l-coh-r
!⟷₂ unite⋆l-coh-r = unite⋆l-coh-l
!⟷₂ hexagonr⊕l = hexagonr⊕r
!⟷₂ hexagonr⊕r = hexagonr⊕l
!⟷₂ hexagonl⊕l = hexagonl⊕r
!⟷₂ hexagonl⊕r = hexagonl⊕l
!⟷₂ hexagonr⊗l = hexagonr⊗r
!⟷₂ hexagonr⊗r = hexagonr⊗l
!⟷₂ hexagonl⊗l = hexagonl⊗r
!⟷₂ hexagonl⊗r = hexagonl⊗l
!⟷₂ absorbl⟷₂l = absorbl⟷₂r
!⟷₂ absorbl⟷₂r = absorbl⟷₂l
!⟷₂ factorzr⟷₂l = factorzr⟷₂r
!⟷₂ factorzr⟷₂r = factorzr⟷₂l
!⟷₂ assocl₊-dist-dist⟷₂l = assocl₊-dist-dist⟷₂r
!⟷₂ assocl₊-dist-dist⟷₂r = assocl₊-dist-dist⟷₂l

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

