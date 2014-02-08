{-# OPTIONS --without-K #-}
module Exercises.Exercises3 where

open import HoTT public

-- 3.1. Prove that if A ≃ B and A is a set, then so is B.

module _ {i} (A B : Type i) (e : A ≃ B) (Aprop : is-prop A) where

  equiv-to-prop-is-prop : is-prop B
  -- B is a mere prop if whenever z, w : B, z == w is inhabited
  equiv-to-prop-is-prop = all-paths-is-prop (λ z w →
    let x = <– e z
        y = <– e w
        x=y = fst (Aprop x y)
    in z      =⟨ ! (<–-inv-r e z) ⟩
       –> e x =⟨ ap (–> e) x=y ⟩
       –> e y =⟨ <–-inv-r e w ⟩
       w ∎)

module _ {i} (A B : Type i) (e : A ≃ B) (Aset : is-set A) where

  equiv-to-set-is-set : is-set B
  -- B is a set if every equality type (z == w) where z, w : B is a mere prop
  equiv-to-set-is-set z w = all-paths-is-prop all-paths-in-B
    where
      x : A
      x = <– e z
      y : A
      y = <– e w
      x=y-prop : is-prop (x == y)
      x=y-prop = Aset x y
      path-spaces-equiv : (x == y) ≃ (z == w)
      path-spaces-equiv = (equiv-ap (e ⁻¹) z w) ⁻¹
      all-paths-in-B : (p q : z == w) → p == q
      all-paths-in-B p q = fst (z=w-prop p q)
        where
          z=w-prop : is-prop (z == w)
          z=w-prop = equiv-to-prop-is-prop (x == y) (z == w) path-spaces-equiv x=y-prop

  -- Alternatively, this is actually already proved in the library, in the form of
  -- equiv-preserves-level.  I will use equiv-preserves-level without comment from now.
  equiv-to-set-is-set′ : is-set B
  equiv-to-set-is-set′ = equiv-preserves-level e Aset

-- 3.2. Prove that if A and B are sets, then so is A + B.

module _ {i} (A B : Type i) (Aset : is-set A) (Bset : is-set B) where

  coprod-is-set : is-set (Coprod A B)
  -- again, prove that whenever x, y : A + B, x == y is a mere prop
  -- In the cis cases, inl a₁ == inl a₂ is equivalent to a₁ == a₂, which is 1 since A is a set
  coprod-is-set (inl a₁) (inl a₂) = equiv-preserves-level (inl=inl-equiv a₁ a₂ ⁻¹) (Aset a₁ a₂)
  coprod-is-set (inr b₁) (inr b₂) = equiv-preserves-level (inr=inr-equiv b₁ b₂ ⁻¹) (Bset b₁ b₂)
  -- In the trans cases, a path x == y can be used to deduce from 0
  coprod-is-set (inl a₁) (inr b₂) = λ l=r → Empty-rec (inl≠inr a₁ b₂ l=r)
  coprod-is-set (inr b₁) (inl a₂) = λ r=l → Empty-rec (inr≠inl b₁ a₂ r=l)
