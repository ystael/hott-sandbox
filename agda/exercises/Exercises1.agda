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
                (λ a pfs → λ b → ==-sym (+-βr′ b a ∙ ap S (==-sym (pfs b))))

·-unit-l : (a : ℕ) → 1 · a == a
·-unit-l = +-unit-r′

·-unit-r : (a : ℕ) → a · 1 == a
·-unit-r = ind-ℕ idp (λ _ pf → ap S pf)

·-absorb-l : (a : ℕ) → 0 · a == 0
·-absorb-l a = idp

·-absorb-r : (a : ℕ) → a · 0 == 0
·-absorb-r = ind-ℕ idp (λ _ pf → pf)

·-βr : (a b : ℕ) → a · S b == a + (a · b)
·-βr = ind-ℕ (λ _ → idp)
             (λ a pfs → λ b →
               ap S (b + (a · S b)     =⟨ (pfs b) |in-ctx (_+_ b) ⟩
                     b + (a + (a · b)) =⟨ ==-sym (+-assoc′ b a (a · b)) ⟩
                     (b + a) + (a · b) =⟨ (+-comm′ b a) |in-ctx (λ e → e + (a · b)) ⟩
                     (a + b) + (a · b) =⟨ +-assoc′ a b (a · b) ⟩ 
                     (a + (b + (a · b)) ∎) ))

·-comm : (a b : ℕ) → a · b == b · a
·-comm = ind-ℕ (λ b → ·-absorb-l b ∙ ==-sym (·-absorb-r b))
               (λ a pfs → λ b →
                 b + (a · b) =⟨ (pfs b) |in-ctx (_+_ b) ⟩
                 b + (b · a) =⟨ ==-sym (·-βr b a) ⟩
                 b · S a ∎)

left-distrib : (a b c : ℕ) → a · (b + c) == (a · b) + (a · c)
left-distrib =
  ind-ℕ (λ b c → idp)
        (λ a pfs → λ b c →
           (b + c) + (a · (b + c))       =⟨ (pfs b c) |in-ctx (_+_ (b + c)) ⟩
           (b + c) + ((a · b) + (a · c)) =⟨ +-four-exch b c (a · b) (a · c) ⟩
           ((b + (a · b)) + (c + (a · c)) ∎))
  where
    +-four-exch : (a b c d : ℕ) → (a + b) + (c + d) == (a + c) + (b + d)
    +-four-exch a b c d =
      (a + b) + (c + d) =⟨ +-assoc′ a b (c + d) ⟩
      a + (b + (c + d)) =⟨ ==-sym ((+-assoc′ b c d) |in-ctx (_+_ a)) ⟩
      a + ((b + c) + d) =⟨ (+-comm′ b c) |in-ctx (λ e → a + (e + d)) ⟩
      a + ((c + b) + d) =⟨ (+-assoc′ c b d) |in-ctx (_+_ a) ⟩
      a + (c + (b + d)) =⟨ ==-sym (+-assoc′ a c (b + d)) ⟩
      (a + c) + (b + d) ∎

right-distrib : (a b c : ℕ) → (b + c) · a == (b · a) + (c · a)
right-distrib a b c =
  (b + c) · a       =⟨ ·-comm (b + c) a ⟩
  a · (b + c)       =⟨ left-distrib a b c ⟩
  (a · b) + (a · c) =⟨ (·-comm a c) |in-ctx (_+_ (a · b)) ⟩
  (a · b) + (c · a) =⟨ (·-comm a b) |in-ctx (λ e → e + (c · a)) ⟩
  (b · a) + (c · a) ∎

-- 1.9. Define the type family Fin : N → U mentioned at the end of §1.3, and the dependent
-- function fmax : Π (n:N) Fin(n + 1) mentioned in §1.4.

-- 0 = inl unit; 1 = inr (inl unit); 2 = inr (inr (inl unit)); ...
Fin : ℕ → Type₀
Fin O     = Empty
Fin (S n) = Coprod Unit (Fin n)

fmax : (n : ℕ) → Fin (S n)
fmax O     = inl unit
fmax (S n) = inr (fmax n)

-- 1.10. Show that the Ackermann function ack : N → N → N is definable using only recN
-- satisfying the following equations:
-- ack(0, n) :== succ(n),
-- ack(succ(m), 0) :== ack(m, 1),
-- ack(succ(m), succ(n)) :== ack(m, ack(succ(m), n)).

ack : ℕ → ℕ → ℕ
ack = rec-ℕ S ack-step
  where ack-step : ℕ → (ℕ → ℕ) → ℕ → ℕ
        ack-step m aₘ = rec-ℕ (aₘ 1) (λ _ a-Sm-n → aₘ a-Sm-n)

ack-correct-1 : (n : ℕ) → ack 0 n == S n
ack-correct-1 n = idp

ack-correct-2 : (m : ℕ) → ack (S m) 0 == ack m 1
ack-correct-2 m = idp

ack-correct-3 : (m n : ℕ) → ack (S m) (S n) == ack m (ack (S m) n)
ack-correct-3 m n = idp

-- 1.11. Show that for any type A, we have ¬¬¬A → ¬A.

¬¬¬A→¬A : {ℓ : ULevel} → {A : Type ℓ} → ¬ (¬ (¬ A)) → ¬ A
¬¬¬A→¬A ¬¬¬a = λ a → ¬¬¬a (A→¬¬A a)
  where A→¬¬A : {ℓ : ULevel} → {A : Type ℓ} → A → ¬ (¬ A)
        A→¬¬A a = λ ¬a → ¬a a

-- 1.12. Using the propositions as types interpretation, derive the following tautologies.
-- (i) If A, then (if B then A).

A→B→A : {ℓ : ULevel} → {A B : Type ℓ} → A → B → A
A→B→A = λ a → λ b → a

-- (ii) If A, then not (not A).

A→¬¬A : {ℓ : ULevel} → {A : Type ℓ} → A → ¬ (¬ A)
A→¬¬A a = λ ¬a → ¬a a

-- (iii) If (not A or not B), then not (A and B).

¬A∨¬B→¬[A∧B] : {ℓ : ULevel} → {A B : Type ℓ} → Coprod (¬ A) (¬ B) → ¬ (A × B)
¬A∨¬B→¬[A∧B] (inl ¬a) = ¬a ∘ fst
¬A∨¬B→¬[A∧B] (inr ¬b) = ¬b ∘ snd

-- 1.13. Using propositions-as-types, derive the double negation of the principle of excluded
-- middle, i.e. prove not (not (P or not P))

¬¬LEM : {ℓ : ULevel} → (A : Type ℓ) → ¬ (¬ (Coprod A (¬ A)))
¬¬LEM A ¬[a∨¬a] = (snd ¬a∧¬¬a) (fst ¬a∧¬¬a)
  where ¬a∧¬¬a : (¬ A) × ¬ (¬ A)
        ¬a∧¬¬a = (¬[a∨¬a] ∘ inl , ¬[a∨¬a] ∘ inr)

-- 1.15. Show that indiscernability of identicals follows from path induction.

ind-a==b : {ℓ : ULevel} → {A : Type ℓ} → (C : (x y : A) → x == y → Type ℓ) →
           ((x : A) → C x x idp) → ((x y : A) → (p : x == y) → C x y p)
ind-a==b C f x .x idp = f x

indiscern : {ℓ : ULevel} → {A : Type ℓ} → (C : A → Type ℓ) →
            Σ ((x y : A) → (p : x == y) → C x → C y)
              (λ f → ((x : A) → f x x idp == idf (C x)))
indiscern {ℓ} {A} C = (transfer , (λ _ → idp))
  where transfer : (x y : A) → (p : x == y) → C x → C y
        transfer = ind-a==b (λ x y _ → C x → C y) (λ x → idf (C x))
