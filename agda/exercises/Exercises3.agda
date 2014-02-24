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

-- 3.3. Prove that if A is a set and B : A → U is a type family such that B(x) is a set for all
-- x : A, then Σ (x:A). B(x) is a set.

-- With a bit more work this could probably be folded into an inductive Σ-preserves-level.

Σ-preserves-prop : ∀ {i} (A : Type i) (B : A → Type i)
                     (Aprop : is-prop A) (Bprop : (a : A) → is-prop (B a)) →
                   is-prop (Σ A B)
Σ-preserves-prop A B Aprop Bprop = all-paths-is-prop Σ-has-all-paths
  where
    Σ-has-all-paths : (p₁ p₂ : Σ A B) → p₁ == p₂
    Σ-has-all-paths (a₁ , b₁) (a₂ , b₂) =
      pair= (prop-has-all-paths Aprop a₁ a₂) (prop-has-all-paths-↓ (Bprop a₂))

Σ-preserves-set : ∀ {i} (A : Type i) (B : A → Type i)
                    (Aset : is-set A) (Bset : (x : A) → is-set (B x)) →
                  is-set (Σ A B)
-- for each (a₁ , b₁) (a₂ , b₂) : Σ A B, (a₁ , b₁) == (a₂ , b₂) needs to be a mere prop.
Σ-preserves-set A B Aset Bset (a₁ , b₁) (a₂ , b₂) = path-space-is-prop
  where
    =Σ-prop : is-prop (=Σ (a₁ , b₁) (a₂ , b₂))
    =Σ-prop = Σ-preserves-prop (a₁ == a₂)   (λ p → b₁ == b₂ [ B ↓ p ])
                               (Aset a₁ a₂) (λ p → =-[-↓-]-level Bset)

    path-space-is-prop : is-prop ((a₁ , b₁) == (a₂ , b₂))
    path-space-is-prop = equiv-preserves-level (=Σ-eqv (a₁ , b₁) (a₂ , b₂)) =Σ-prop

-- 3.4. Show that A is a mere proposition if and only if A → A is contractible.

prop-→-is-contr : ∀ {i} (A : Type i) → is-prop A → is-contr (A → A)
-- If A is a mere prop, every function is contractible onto the identity function.
prop-→-is-contr A Aprop = (idf A , (λ f → λ= (λ x → prop-has-all-paths Aprop x (f x))))

contr-→-gives-prop : ∀ {i} (A : Type i) → is-contr (A → A) → is-prop A
contr-→-gives-prop _ (g , g=) =
  -- Construct a path x == y by using g= to construct a path from the constant function x
  -- to the constant function y.
  all-paths-is-prop (λ x y → app= (! (g= (cst x)) ∙ g= (cst y)) x)

-- 3.5. Show that isProp(A) ≃ (A → isContr(A)).

-- 3.13. We showed in Corollary 3.2.7 that the following naive form of LEM is inconsistent with
-- univalence: Π(A:U). A + (¬A).  In the absence of univalence, this axiom is
-- consistent. However, show that it implies the axiom of choice (3.8.1).

module _ {i} where

  -- Just notation
  ∥_∥ : Type i → Type i
  ∥ A ∥ = Trunc ⟨-1⟩ A

  -- This is the simplified equivalent form of the axiom of choice: if every member of a family
  -- of types is merely inhabited, their dependent product is merely inhabited.
  set-choice : Type (lsucc i)
  set-choice = (X : Type i) → (Y : X → Type i) → is-set X → ((x : X) → is-set (Y x)) →
               Π X (λ x → ∥ Y x ∥) → ∥ Π X Y ∥

  -- Since 0 is a mere proposition, merely inhabiting a type we know is empty yields empty.
  mere-contr-elim : {A : Type i} → ∥ A ∥ → ¬ A → ⊥
  mere-contr-elim ∥a∥ = Trunc-rec (Π-is-prop (λ _ → ⊥-is-prop)) (λ a ¬a → ¬a a) ∥a∥

  -- The idea here is: Given x : X, lem (Y x) lives in (Y x) + ¬ (Y x), so we can match on it.
  -- If we have Y x, that is the corresponding point of Π X Y.  If we have ¬ (Y x), we can lift
  -- mere-section x from ∥ Y x ∥ to Y x and apply it to get 0, from which we get a point of Π X
  -- Y.
  strong-LEM→set-choice : Π (Type i) (λ A → Coprod A (¬ A)) → set-choice
  strong-LEM→set-choice LEM X Y Xset Yset mere-section =
    [ untruncated-version LEM X Y Xset Yset mere-section ]
    where
      untruncated-version : Π (Type i) (λ A → Coprod A (¬ A)) →
                            (X : Type i) → (Y : X → Type i) →
                            is-set X → ((x : X) → is-set (Y x)) →
                            Π X (λ x → ∥ Y x ∥) → Π X Y
      untruncated-version LEM X Y Xset Yset mere-section x with LEM (Y x)
      ... | inl y  = y
      ... | inr ¬y = ⊥-rec (mere-contr-elim (mere-section x) ¬y)

-- 3.14. Show that assuming LEM, the double negation ¬¬A has the same universal property as the
-- propositional truncation ∥A∥, and is therefore equivalent to it. Thus, under LEM, the
-- propositional truncation can be defined rather than taken as a separate type former.

module _ {i} where

  LEM : Type (lsucc i)
  LEM = Π (Type i) (λ A → is-prop A → Coprod A (¬ A))

  module _ {lem : LEM} where
    ¬¬-is-prop : (A : Type i) → is-prop (¬ (¬ A))
    ¬¬-is-prop A = Π-is-prop (λ _ → ⊥-is-prop)

    -- Truncation of an element into the truncated type
    ¬¬ : {A : Type i} → A → ¬ (¬ A)
    ¬¬ a ¬a = ¬a a
 
    -- Universal property of truncation
    ¬¬-is-trunc : {A B : Type i} → is-prop B → (f : A → B) → (¬ (¬ A) → B)
    ¬¬-is-trunc {A} {B} Bprop f with lem B Bprop
    ... | inl b  = λ _ → b
    ... | inr ¬b = (λ ¬¬a → ⊥-elim (¬¬a (¬b ∘ f)))
