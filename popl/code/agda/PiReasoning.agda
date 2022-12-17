{-# OPTIONS --without-K --allow-unsolved-metas #-}

module PiReasoning where

open import PiSyntax

infix  30 _⟷₂_

data _⟷₂_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⟷₂ ((c₁ ◎ c₂) ◎ c₃)
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
    (assocr₊ ◎ (id⟷ {t₁} ⊕ unite₊l {t₂})) ⟷₂ (unite₊r ⊕ id⟷)
  triangle⊗l : {t₁ t₂ : U} →
    ((unite⋆r {t₁}) ⊗ id⟷ {t₂}) ⟷₂ (assocr⋆ ◎ (id⟷ ⊗ unite⋆l))
  triangle⊗r : {t₁ t₂ : U} →
    (assocr⋆ ◎ (id⟷ {t₁} ⊗ unite⋆l {t₂})) ⟷₂ (unite⋆r ⊗ id⟷)
  pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
    (assocr₊ ◎ (assocr₊ {t₁} {t₂} {_+ᵤ_ t₃ t₄})) ⟷₂
    (((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊))
  pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
    (((assocr₊ {t₁} {t₂} {t₃} ⊕ id⟷ {t₄}) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊))
     ⟷₂ (assocr₊ ◎ assocr₊)    
  pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
    (assocr⋆ ◎ (assocr⋆ {t₁} {t₂} {_×ᵤ_ t₃ t₄})) ⟷₂
    (((assocr⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆))
  pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
    (((assocr⋆ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆))
     ⟷₂ (assocr⋆ ◎ assocr⋆)
--   -- from the braiding
--   -- unit coherence
  unite₊l-coh-l : {t₁ : U} → (unite₊l {t₁}) ⟷₂ (swap₊ ◎ unite₊r)
  unite₊l-coh-r : {t₁ : U} → (swap₊ ◎ unite₊r) ⟷₂ (unite₊l {t₁})
  unite⋆l-coh-l : {t₁ : U} → (unite⋆l {t₁}) ⟷₂ (swap⋆ ◎ unite⋆r)
  unite⋆l-coh-r : {t₁ : U} → (swap⋆ ◎ unite⋆r) ⟷₂ (unite⋆l {t₁})
  hexagonr⊕l : {t₁ t₂ t₃ : U} →
    ((assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃}) ⟷₂
    (((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊))
  hexagonr⊕r : {t₁ t₂ t₃ : U} →
    (((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)) ⟷₂
    ((assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃})
  hexagonl⊕l : {t₁ t₂ t₃ : U} →
    ((assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃}) ⟷₂
    (((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷))
  hexagonl⊕r : {t₁ t₂ t₃ : U} →
    (((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷)) ⟷₂
    ((assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃})
  hexagonr⊗l : {t₁ t₂ t₃ : U} →
    ((assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃}) ⟷₂
    (((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆))
  hexagonr⊗r : {t₁ t₂ t₃ : U} →
    (((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆)) ⟷₂
    ((assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃})
  hexagonl⊗l : {t₁ t₂ t₃ : U} →
    ((assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃}) ⟷₂
    (((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷))
  hexagonl⊗r : {t₁ t₂ t₃ : U} →
    (((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷)) ⟷₂
    ((assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃})
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
    (((assocl₊ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ dist) ◎ (dist ⊕ id⟷)) ⟷₂
    ((dist ◎ (id⟷ ⊕ dist)) ◎ assocl₊)
  assocl₊-dist-dist⟷₂r : {t₁ t₂ t₃ t₄ : U} →
    ((dist {t₁} ◎ (id⟷ ⊕ dist {t₂} {t₃} {t₄})) ◎ assocl₊) ⟷₂
    (((assocl₊ ⊗ id⟷) ◎ dist) ◎ (dist ⊕ id⟷))

xcx : ((id⟷ ⊗ swap₊) ◎ cx) ⟷₂ (cx ◎ (id⟷ ⊗ swap₊))
xcx = {!!} 

