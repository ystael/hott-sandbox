{-# OPTIONS --without-K #-}
module Exercises.Exercises2 where

open import HoTT public
open import exercises.Exercises1 using (ind-a==b)

-- 2.1. Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.

module _ {i} {A : Type i} where

  _∙″_ : {x y z : A} → x == y → y == z → x == z
  idp ∙″ idp = idp

  ∙=∙″ : {x y z : A} (p : x == y) (q : y == z) → p ∙ q == p ∙″ q
  ∙=∙″ idp idp = idp

  -- The proof that any particular instances of the compositions are equal is a trivial path
  -- induction, but to prove the operators themselves are equal we require extensionality.
  ∙=∙'₁ : {x y z : A} → _∙_ {x = x} {y = y} {z = z} == _∙'_ {x = x} {y = y} {z = z}
  ∙=∙'₁ = λ= (λ p → λ= (λ q → ∙=∙' p q))

  -- Explicit eta expansion is required here to work around problems combining λ= with implicit
  -- arguments.  Thanks to Jason Gross for the hint.  One could instead define alternate
  -- versions of the composition arguments that take the arguments x y z explicitly.
  ∙=∙'₂ : (λ x y z → _∙_ {x = x} {y = y} {z = z}) == (λ x y z → _∙'_ {x = x} {y = y} {z = z})
  ∙=∙'₂ = λ= (λ x → λ= (λ y → λ= (λ z → ∙=∙'₁ {x} {y} {z})))

  ∙=∙″₁ : {x y z : A} → _∙_ {x = x} {y = y} {z = z} == _∙″_ {x = x} {y = y} {z = z}
  ∙=∙″₁ = λ= (λ p → λ= (λ q → ∙=∙″ p q))

  ∙=∙″₂ : (λ x y z → _∙_ {x = x} {y = y} {z = z}) == (λ x y z → _∙″_ {x = x} {y = y} {z = z})
  ∙=∙″₂ = λ= (λ x → λ= (λ y → λ= (λ z → ∙=∙″₁ {x} {y} {z})))

-- 2.2. Show that the three equalities of proofs constructed in the previous exercise form a
-- commutative triangle. In other words, if the three definitions of concatenation are denoted
-- by (p ∙ q), (p ∙′ q), and (p ∙″ q), then the concatenated equality
-- (p ∙ q) = (p ∙′ q) = (p ∙″ q) is equal to the equality (p ∙ q) = (p ∙″ q).

  ∙'=∙″ : {x y z : A} (p : x == y) (q : y == z) → p ∙' q == p ∙″ q
  ∙'=∙″ idp idp = idp

  ∙=-transitive : {x y z : A} (p : x == y) (q : y == z) →
                  (∙=∙' p q) ∙ (∙'=∙″ p q) == (∙=∙″ p q)
  ∙=-transitive idp idp = idp

-- 2.3. Give a fourth, different, proof of Lemma 2.1.2, and prove that it is equal to the
-- others.

  -- This is the double-induction proof from the text, but reversed to induct on q first
  -- instead of p.  It could be rephrased to use pattern matching instead of explicit path
  -- induction.
  _∙‴_ : {x y z : A} → (p : x == y) → (q : y == z) → x == z
  _∙‴_ {x} {y} {z} p q = ind-a==b D d y z q x p
    where
      D : (y z : A) → y == z → Type i
      D y z _ = (x : A) → x == y → x == z
      E : (x z : A) → x == z → Type i
      E x z _ = x == z
      e : (z : A) → E z z idp
      e z = idp
      d : (z : A) → D z z idp
      d z = λ x → ind-a==b E e x z

  ∙=∙‴ : {x y z : A} (p : x == y) (q : y == z) → p ∙ q == p ∙‴ q
  ∙=∙‴ idp idp = idp

  ∙=∙‴₁ : {x y z : A} → _∙_ {x = x} {y = y} {z = z} == _∙‴_ {x = x} {y = y} {z = z}
  ∙=∙‴₁ = λ= (λ p → λ= (λ q → ∙=∙‴ p q))

  ∙=∙‴₂ : (λ x y z → _∙_ {x = x} {y = y} {z = z}) == (λ x y z → _∙‴_ {x = x} {y = y} {z = z})
  ∙=∙‴₂ = λ= (λ x → λ= (λ y → λ= (λ z → ∙=∙‴₁ {x} {y} {z})))

-- 2.4. Define, by induction on n, a general notion of n-dimensional path in a type A,
-- simultaneously with the type of boundaries for such paths.

  data NBoundary : (n : ℕ) → Type i
  data NPath : (n : ℕ) → (b : NBoundary n) → Type i
  ∂ : {n : ℕ} → {b : NBoundary n} → NPath n b → NBoundary n
  ∂² : {n : ℕ} → NBoundary (S n) → NBoundary n
  ∂-source : {n : ℕ} → (b : NBoundary (S n)) → NPath n (∂² b)
  ∂-target : {n : ℕ} → (b : NBoundary (S n)) → NPath n (∂² b)
  
  data NBoundary where
    boundary₀ : NBoundary 0
    boundaryₙ : {n : ℕ} → {b : NBoundary n} → NPath n b → NPath n b → NBoundary (S n)

  data NPath where
    path₀ : A → NPath 0 boundary₀
    pathₙ : {n : ℕ} → (b : NBoundary (S n)) → (∂-source b) == (∂-target b) → NPath (S n) b

  ∂ {_} {b} _ = b
  ∂² (boundaryₙ {_} {b} _ _) = b
  ∂-source (boundaryₙ s _) = s
  ∂-target (boundaryₙ _ t) = t

-- 2.5. Prove that the functions (2.3.6) and (2.3.7) are inverse equivalences.  (For any x, y :
-- A and p : x = y and f : A → B, by concatenating with transportconst^B_p(f(x)) and its
-- inverse, respectively, we obtain functions f(x) = f(y) → p_*(f(x)) = f(y)􏰆and p_*(f(x)) =
-- f(y) → f(x) = f(y).)

transportconst : ∀ {i j} {A : Type i} (B : Type j) {x y : A} (p : x == y) (b : B)
                 → transport (cst B) p b == b
transportconst B idp b = idp

transportconst-left : ∀ {i j} {A : Type i} (B : Type j) {x y : A} (p : x == y) (f : A → B) →
                      f x == f y → transport (cst B) p (f x) == f y
transportconst-left B {x = x} p f q = (transportconst B p (f x)) ∙ q

transportconst-left! : ∀ {i j} {A : Type i} (B : Type j) {x y : A} (p : x == y) (f : A → B) →
                       transport (cst B) p (f x) == f y → f x == f y
transportconst-left! B {x = x} p f q′ = (! (transportconst B p (f x))) ∙ q′

tc-left-equiv₁ : ∀ {i j} {A : Type i} (B : Type j) {x y : A} (p : x == y) (f : A → B)
                 (q : f x == f y) →
                 transportconst-left! B p f (transportconst-left B p f q) == q
tc-left-equiv₁ B {x = x} p f q =
  let tc = transportconst B p (f x)
  in transportconst-left! B p f (transportconst-left B p f q)
       =⟨ ! (∙-assoc (! tc) tc q) ⟩
     (! tc ∙ tc) ∙ q
       =⟨ !-inv-l tc |in-ctx (λ p → p ∙ q) ⟩
     q ∎

tc-left-equiv₂ : ∀ {i j} {A : Type i} (B : Type j) {x y : A} (p : x == y) (f : A → B)
                 (q′ : transport (cst B) p (f x) == f y) →
                 transportconst-left B p f (transportconst-left! B p f q′) == q′
tc-left-equiv₂ B {x = x} p f q′ =
  let tc = transportconst B p (f x)
  in transportconst-left B p f (transportconst-left! B p f q′)
       =⟨ ! (∙-assoc tc (! tc) q′) ⟩
     (tc ∙ ! tc) ∙ q′
       =⟨ !-inv-r tc |in-ctx (λ p → p ∙ q′) ⟩
     q′ ∎

tc-left-equiv : ∀ {i j} {A : Type i} (B : Type j) {x y : A} (p : x == y) (f : A → B) →
                is-equiv (transportconst-left B p f)
tc-left-equiv B p f = is-eq (transportconst-left B p f) (transportconst-left! B p f)
                            (tc-left-equiv₂ B p f) (tc-left-equiv₁ B p f)

tc-left!-equiv : ∀ {i j} {A : Type i} (B : Type j) {x y : A} (p : x == y) (f : A → B) →
                 is-equiv (transportconst-left! B p f)
tc-left!-equiv B p f = is-eq (transportconst-left! B p f) (transportconst-left B p f)
                             (tc-left-equiv₁ B p f) (tc-left-equiv₂ B p f)

-- 2.6. Prove that if p : x = y, then the function (p ∙ –) : (y = z) → (x = z) is an
-- equivalence.

∙-left-equiv : ∀ {i} {A : Type i} {x y : A} (p : x == y) → {z : A} →
               is-equiv (λ (q : y == z) → p ∙ q)
∙-left-equiv p = is-eq (_∙_ p) (_∙_ (! p)) (∙-left-equiv₂ p) (∙-left-equiv₁ p)
  where
    ∙-left-equiv₁ : ∀ {i} {A : Type i} {x y : A} (p : x == y) {z : A} (q : y == z) →
                    (! p) ∙ (p ∙ q) == q
    ∙-left-equiv₁ p q = (! p) ∙ (p ∙ q) =⟨ ! (∙-assoc (! p) p q) ⟩
                        ((! p) ∙ p) ∙ q =⟨ !-inv-l p |in-ctx (λ p → p ∙ q) ⟩
                        q ∎

    ∙-left-equiv₂ : ∀ {i} {A : Type i} {x y : A} (p : x == y) {z : A} (q : x == z) →
                    p ∙ ((! p) ∙ q) == q
    ∙-left-equiv₂ p q = p ∙ ((! p) ∙ q) =⟨ ! (∙-assoc p (! p) q) ⟩
                        (p ∙ (! p)) ∙ q =⟨ !-inv-r p |in-ctx (λ p → p ∙ q) ⟩
                        q ∎

-- 2.7. State and prove a generalization of Theorem 2.6.5 from cartesian products to Σ-types.

module _ {i} {A A′ : Type i} {B : A → Type i} {B′ : A′ → Type i} where

  _,→_ : (g : A → A′) → (h : {a : A} → B a → B′ (g a)) → Σ A B → Σ A′ B′
  _,→_ g h (a , b) = (g a , h b)

  -- This seems to be difficult to get into the right type.  Come back to this later.

  -- ap-Σ : ∀ (g : A → A′) (h : {a : A} → B a → B′ (g a)) (x y : Σ A B)
  --          (p : fst x == fst y) (q : snd x == snd y [ B ↓ p ]) →
  --        ap (g ,→ h) (pair= p q) == pair= (ap g p) {!!}
  -- ap-Σ g h (a , b) (.a , .b) idp idp = {!!}

-- 2.8. State and prove an analogue of Theorem 2.6.5 for coproducts.

module _ {i} {A A′ B B′ : Type i} where

  _+→_ : (g : A → A′) → (h : B → B′) → Coprod A B → Coprod A′ B′
  _+→_ g _ (inl a) = inl (g a)
  _+→_ _ h (inr b) = inr (h b)

  ap-coprod : ∀ (g : A → A′) (h : B → B′) {x y : A} (p : x == y) →
              ap (g +→ h) (ap inl p) == ap (inl ∘ g) p
  ap-coprod g h idp = idp

  ap-coprod′ : ∀ (g : A → A′) (h : B → B′) {x y : B} (q : x == y) →
              ap (g +→ h) (ap inr q) == ap (inr ∘ h) q
  ap-coprod′ g h idp = idp
