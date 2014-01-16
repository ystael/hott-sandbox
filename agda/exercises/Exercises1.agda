{-# OPTIONS --without-K #-}
module exercises.Exercises1 where

open import HoTT public

-- 1.1. Given functions f : A → B and g : B → C, define their composite g ◦ f : A → C.
-- Show that we have h ◦ ( g ◦ f ) ≡ ( h ◦ g ) ◦ f .

∘-associative : {ℓ : ULevel} → {A B C D : Type ℓ} →
                (f : A → B) → (g : B → C) → (h : C → D) →
                h ∘ (g ∘ f) == (h ∘ g) ∘ f
-- idp (refl) typechecks without any help; that means the equality is judgmental
∘-associative f g h = idp

-- 1.2. Derive the recursion principle for products rec A × B using only the projections, and
-- verify that the definitional equalities are valid. Do the same for Σ-types.

rec-A×B : {ℓ : ULevel} → {A B C : Type ℓ} → (A → B → C) → A × B → C
rec-A×B g p = g (fst p) (snd p)

rec-A×B-correct-1 : {ℓ : ULevel} → {A B : Type ℓ} → rec-A×B (λ (a : A) (b : B) → a) == fst
rec-A×B-correct-1 = idp

rec-A×B-correct-2 : {ℓ : ULevel} → {A B : Type ℓ} → rec-A×B (λ (a : A) (b : B) → b) == snd
rec-A×B-correct-2 = idp

rec-ΣAB : {ℓ : ULevel} → {A : Type ℓ} → {B : A → Type ℓ} → {C : Type ℓ} →
          ((x : A) → B x → C) → Σ A B → C
rec-ΣAB g p = g (fst p) (snd p)

rec-ΣAB-correct-1 : {ℓ : ULevel} → {A : Type ℓ} → {B : A → Type ℓ} →
                    rec-ΣAB (λ (a : A) (b : B a) → a) == fst
rec-ΣAB-correct-1 = idp

-- Can't do the correctness theorem for the second coordinate because C would need to be a
-- dependent type.  Have to do the full induction principle instead.
ind-ΣAB : {ℓ : ULevel} → {A : Type ℓ} → {B : A → Type ℓ} → {C : Σ A B → Type ℓ} →
          ((a : A) → (b : B a) → C (a , b)) → (ab : Σ A B) → C ab
ind-ΣAB g p = g (fst p) (snd p)

ind-ΣAB-correct-1 : {ℓ : ULevel} → {A : Type ℓ} → {B : A → Type ℓ} →
                    ind-ΣAB (λ (a : A) (b : B a) → a) == fst
ind-ΣAB-correct-1 = idp

ind-ΣAB-correct-2 : {ℓ : ULevel} → {A : Type ℓ} → {B : A → Type ℓ} →
                    ind-ΣAB (λ (a : A) (b : B a) → b) == snd
ind-ΣAB-correct-2 = idp

-- 1.4. Assuming as given only the iterator for natural numbers:

ℕ-iter : {ℓ : ULevel} → {C : Type ℓ} → C → (C → C) → ℕ → C
ℕ-iter c₀ cₛ O     = c₀
ℕ-iter c₀ cₛ (S n) = cₛ (ℕ-iter c₀ cₛ n)

-- derive a function having the type of the recursor rec-ℕ. Show that the defining equations
-- of the recursor hold propositionally for this function, using the induction principle for ℕ.

iter-augment : {ℓ : ULevel} → {C : Type ℓ} → (ℕ → C → C) → (ℕ × C) → (ℕ × C)
iter-augment f (n , c) = (S n , f n c)

rec-ℕ′ : {ℓ : ULevel} → {C : Type ℓ} → C → (ℕ → C → C) → ℕ → C
rec-ℕ′ c₀ cₛ n = snd (ℕ-iter (0 , c₀) (iter-augment cₛ) n)

rec-ℕ : {ℓ : ULevel} → {C : Type ℓ} → C → (ℕ → C → C) → ℕ → C
rec-ℕ c₀ cₛ O     = c₀
rec-ℕ c₀ cₛ (S n) = cₛ n (rec-ℕ c₀ cₛ n)

ind-ℕ : {ℓ : ULevel} → {C : ℕ → Type ℓ} → C 0 → ((m : ℕ) → C m → C (S m)) →
        (n : ℕ) → C n
ind-ℕ c₀ cₛ O     = c₀
ind-ℕ c₀ cₛ (S n) = cₛ n (ind-ℕ c₀ cₛ n)

rec-ℕ′-correct-O : {ℓ : ULevel} → {C : Type ℓ} → (c₀ : C) → (cₛ : ℕ → C → C) →
                  rec-ℕ′ c₀ cₛ 0 == c₀
rec-ℕ′-correct-O c₀ cₛ = idp

rec-ℕ′-correct-S : {ℓ : ULevel} → {C : Type ℓ} → (c₀ : C) → (cₛ : ℕ → C → C) →
                  (n : ℕ) → rec-ℕ′ c₀ cₛ (S n) == cₛ n (rec-ℕ′ c₀ cₛ n)
rec-ℕ′-correct-S c₀ cₛ = ind-ℕ idp reduce
  where
    iter-augment-counts-first : (n : ℕ) → fst (ℕ-iter (0 , c₀) (iter-augment cₛ) n) == n
    iter-augment-counts-first = ind-ℕ idp (λ _ pf → ap S pf)

    reduce : (m : ℕ) → rec-ℕ′ c₀ cₛ (S m) == cₛ m (rec-ℕ′ c₀ cₛ m) →
             rec-ℕ′ c₀ cₛ (S (S m)) == cₛ (S m) (rec-ℕ′ c₀ cₛ (S m))
    reduce m pf rewrite iter-augment-counts-first m = idp

-- 1.5. Show that if we define A + B : ≡ ∑ ( x:2 ) rec 2 (U , A, B, x ) , then we can give a
-- definition of ind A + B for which the definitional equalities stated in §1.7 hold.

-- 0 is false and 1 is true, despite the fact that this reverses the usual case order
rec-Bool : {ℓ : ULevel} → {C : Type ℓ} → C → C → Bool → C
rec-Bool c₀ c₁ false = c₀
rec-Bool c₀ c₁ true  = c₁

_⊕_ : {ℓ : ULevel} → Type ℓ → Type ℓ → Type ℓ
A ⊕ B = Σ Bool (rec-Bool A B)

inl′ : {ℓ : ULevel} → {A B : Type ℓ} → A → A ⊕ B
inl′ a = (false , a)

inr′ : {ℓ : ULevel} → {A B : Type ℓ} → B → A ⊕ B
inr′ b = (true , b)

ind-⊕ : {ℓ : ULevel} → {A B : Type ℓ} → {C : A ⊕ B → Type ℓ} →
        ((a : A) → C (inl′ a)) → ((b : B) → C (inr′ b)) → Π (A ⊕ B) C
ind-⊕ g₀ g₁ (false , a) = g₀ a
ind-⊕ g₀ g₁ (true  , b) = g₁ b

-- 1.8. Define multiplication and exponentiation using rec N . Verify that ( N, + , 0, × , 1 )
-- is a semiring using only ind N . You will probably also need to use symmetry and
-- transitivity of equality, Lemmas 2.1.1 and 2.1.2.

_·_ : ℕ → ℕ → ℕ
_·_ = rec-ℕ (λ _ → 0) (λ _ g n → n + g n)

rexp : ℕ → ℕ → ℕ
rexp = rec-ℕ (λ _ → 1) (λ _ g n → n · g n)

_^_ : ℕ → ℕ → ℕ
m ^ n = rexp n m

-- These are not actually that simple; the pattern match hides an appropriate invocation of
-- the induction principle for identity types, but just accept it for now.
==-sym : {ℓ : ULevel} → {A : Type ℓ} → {a b : A} → a == b → b == a
==-sym idp = idp

==-trans : {ℓ : ULevel} → {A : Type ℓ} → {a b c : A} → a == b → b == c → a == c
==-trans idp idp = idp

+-assoc′ : (a b c : ℕ) → (a + b) + c == a + (b + c)
+-assoc′ = ind-ℕ (λ b c → idp) (λ _ pfs → λ b c → ap S (pfs b c))

+-unit-r′ : (a : ℕ) → a + 0 == a
+-unit-r′ = ind-ℕ idp (λ _ pf → ap S pf)

+-βr′ : (a b : ℕ) → a + (S b) == S (a + b)
+-βr′ = ind-ℕ (λ _ → idp) (λ _ pfs → λ b → ap S (pfs b))

+-comm′ : (a b : ℕ) → a + b == b + a
+-comm′ = ind-ℕ (λ b → ==-sym (+-unit-r′ b))
                (λ _ pfs → λ b → {!!})
