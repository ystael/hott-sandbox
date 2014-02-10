{-# OPTIONS --without-K #-}
module Exercises.Exercises2 where

open import HoTT public
open import exercises.Exercises1 using (ind-a==b; ∘-assoc)

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

-- 2.9. Prove that coproducts have the expected universal property,
-- (A + B → X) ≃ (A → X) × (B → X).
-- Can you generalize this to an equivalence involving dependent functions?

module _ {i} (A B X : Type i) where

  coprod-universal : (Coprod A B → X) ≃ ((A → X) × (B → X))
  coprod-universal = (split , is-eq split combine split-combine combine-split)
    where
      split : (Coprod A B → X) → ((A → X) × (B → X))
      split f = (λ a → f (inl a)) , (λ b → f (inr b))

      combine : (A → X) × (B → X) → Coprod A B → X
      combine (g , h) (inl a) = g a
      combine (g , h) (inr b) = h b

      split-combine : (gh : (A → X) × (B → X)) → split (combine gh) == gh
      split-combine (g , h) = pair×= (λ= (split-combine-ext-l g h))
                                     (λ= (split-combine-ext-r g h))
        where
          split-combine-ext-l : (g : A → X) → (h : B → X) → (a : A) →
                                combine (g , h) (inl a) == g a
          split-combine-ext-l g h a = idp
          split-combine-ext-r : (g : A → X) → (h : B → X) → (b : B) →
                                combine (g , h) (inr b) == h b
          split-combine-ext-r g h b = idp

      combine-split : (f : Coprod A B → X) → combine (split f) == f
      combine-split f = λ= (combine-split-ext f)
        where
          combine-split-ext : (f : Coprod A B → X) → (ab : Coprod A B) →
                              combine (split f) ab == f ab
          combine-split-ext f (inl a) = idp
          combine-split-ext f (inr b) = idp

module _ {i} (A B : Type i) (C : A → Type i) (D : B → Type i) where

  private
    E : Coprod A B → Type i
    E (inl a) = C a
    E (inr b) = D b

  coprod-univ-dep : ((ab : Coprod A B) → E ab) ≃ (((a : A) → C a) × ((b : B) → D b))
  coprod-univ-dep = (split , is-eq split combine split-combine combine-split)
    where
      split : ((ab : Coprod A B) → E ab) → (((a : A) → C a) × ((b : B) → D b))
      split f = (λ a → f (inl a)) , (λ b → f (inr b))

      combine : (((a : A) → C a) × ((b : B) → D b)) → ((ab : Coprod A B) → E ab)
      combine (g , h) (inl a) = g a
      combine (g , h) (inr b) = h b

      split-combine : (gh : ((a : A) → C a) × ((b : B) → D b)) → split (combine gh) == gh
      split-combine (g , h) = pair×= (λ= (split-combine-ext-l g h))
                                     (λ= (split-combine-ext-r g h))
        where
          split-combine-ext-l : (g : (a : A) → C a) → (h : (b : B) → D b) → (a : A) →
                                combine (g , h) (inl a) == g a
          split-combine-ext-l g h a = idp
          split-combine-ext-r : (g : (a : A) → C a) → (h : (b : B) → D b) → (b : B) →
                                combine (g , h) (inr b) == h b
          split-combine-ext-r g h b = idp

      combine-split : (f : (ab : Coprod A B) → E ab) → combine (split f) == f
      combine-split f = λ= (combine-split-ext f)
        where
          combine-split-ext : (f : (ab : Coprod A B) → E ab) → (ab : Coprod A B) →
                              combine (split f) ab == f ab
          combine-split-ext f (inl a) = idp
          combine-split-ext f (inr b) = idp

-- 2.10. Prove that Σ-types are “associative”, in that for any A : U and families B : A → U and
-- C : (Σx:A. B(x)) → U, we have Σx:A. Σy:B(x). C((x,y)) ≅ Σp:(Σx:A. B(x)). C(p).

module _ {i} (A : Type i) (B : A → Type i) (C : Σ A B → Type i) where

  Σ-assoc : Σ A (λ a → Σ (B a) (λ b → C (a , b))) ≃ Σ (Σ A B) C
  Σ-assoc = (pull , is-eq pull push pull-push push-pull)
    where
      pull : Σ A (λ a → Σ (B a) (λ b → C (a , b))) → Σ (Σ A B) C
      pull (a , (b , c)) = ((a , b) , c)

      push : Σ (Σ A B) C → Σ A (λ a → Σ (B a) (λ b → C (a , b)))
      push ((a , b) , c) = (a , (b , c))

      pull-push : (w : Σ (Σ A B) C) → pull (push w) == w
      pull-push ((a , b) , c) = idp

      push-pull : (z : Σ A (λ a → Σ (B a) (λ b → C (a , b)))) → push (pull z) == z
      push-pull (a , (b , c)) = idp

-- 2.11. A (homotopy) commutative square
-- P --h-> A
-- |       |
-- |k      |f
-- ↓       ↓
-- B --g-> C
-- consists of functions f, g, h, and k as shown, together with a path f ◦ h = g ◦ k. Note that
-- this is exactly an element of the pullback (P → A) ×_{P→C} (P → B) as defined in
-- (2.15.11). A commutative square is called a (homotopy) pullback square if for any X, the
-- induced map (X → P) → (X → A) ×_{X→C} (X → B) is an equivalence. Prove that the pullback P
-- = A ×_C B defined in (2.15.11) is the corner of a pullback square.
-- That is, P = A ×_C B = Σa:A. Σb:B. (f(a) = g(b)).

-- The problem here is to prove (1) that the type Σa:A. Σb:B. (f(a) = g(b)) (together with the
-- obvious projections onto A and B serving as h and k) yields a commutative square; and (2)
-- that this type has the claimed universal property, that is, that any cone over the diagram
-- A -f-> C <-g- B (pair of maps α : X → A, β : X → B such that fα = gβ) factors uniquely
-- through P (so that maps X → P are equivalent to these cones, which are clearly classified by
-- Σα:X→A. Σβ:X→B. (fα = gβ)).

-- General definitions for commutative squares and pullbacks
record Square {i} (A B C D : Type i) : Type i where
  constructor □
  field
    -- order: top left right bottom
    f : A → B
    g : A → C
    h : B → D
    k : C → D
    commutes : h ∘ f == k ∘ g

is-pullback : ∀ {i} {A B C D : Type i} → Square A B C D → Type (lsucc i)
is-pullback {i} {A} {B} {C} {D} (□ f g h k commutes) =
  (X : Type i) → (X → A) ≃ Σ (X → B) (λ β → Σ (X → C) (λ γ → h ∘ β == k ∘ γ))

PullbackSquare : ∀ {i} (A B C D : Type i) → Type (lsucc i)
PullbackSquare A B C D = Σ (Square A B C D) is-pullback

module Ex2-11 {i} (A B C : Type i) (f : A → C) (g : B → C) where

  P : Type i
  P = Σ A (λ a → Σ B (λ b → f a == g b))
  -- Projections
  h : P → A
  h = fst
  k : P → B
  k = fst ∘ snd
  commutes-ext : (p : P) → f (h p) == g (k p)
  commutes-ext = snd ∘ snd

  square : Square P A B C
  square = □ h k f g (λ= commutes-ext)

  pullback-square : PullbackSquare P A B C
  pullback-square = (square , P-is-pullback)
    where
      P-is-pullback : is-pullback square
      P-is-pullback X = (split , is-eq split combine split-combine combine-split)
        where
          split : (X → P) → Σ (X → A) (λ α → Σ (X → B) (λ β → f ∘ α == g ∘ β))
          split π = (h ∘ π , (k ∘ π , λ= (commutes-ext ∘ π)))

          combine : Σ (X → A) (λ α → Σ (X → B) (λ β → f ∘ α == g ∘ β)) → (X → P)
          combine (α , (β , ϑ)) x = (α x , (β x , app= ϑ x))

          split-combine : (ω : Σ (X → A) (λ α → Σ (X → B) (λ β → f ∘ α == g ∘ β))) →
                          split (combine ω) == ω
          split-combine (α , (β , ϑ)) = pair= idp (pair= idp (! (λ=-η ϑ)))

          combine-split : (π : X → P) → combine (split π) == π
          combine-split π = λ= combine-split-ext
            where
              combine-split-ext : (x : X) → combine (split π) x == π x
              combine-split-ext x = pair= idp (pair= idp (app=-β (commutes-ext ∘ π) x))

-- 2.12. Suppose given two commutative squares
-- A → C → E
-- ↓   ↓   ↓
-- B → D → F
-- and suppose that the right-hand square is a pullback square. Prove that the left-hand square
-- is a pullback square if and only if the outer rectangle is a pullback square.

module Ex2-12 {i} {A B C D E F : Type i}
              (L : Square A C B D) (RP : PullbackSquare C E D F)
              (shared : Square.h L == Square.g (fst RP)) where
  open Square

  R : Square C E D F
  R = fst RP

  outer : Square A E B F
  outer = □ (f R ∘ f L) (g L) (h R) (k R ∘ k L) outer-commutes
    where
      outer-commutes : (h R) ∘ (f R) ∘ (f L) == (k R) ∘ (k L) ∘ (g L)
      outer-commutes = h R ∘ f R ∘ f L =⟨ commutes R |in-ctx (λ φ → φ ∘ f L) ⟩
                       k R ∘ g R ∘ f L =⟨ ! shared   |in-ctx (λ φ → k R ∘ φ ∘ f L) ⟩
                       k R ∘ h L ∘ f L =⟨ commutes L |in-ctx (λ φ → k R ∘ φ) ⟩
                       k R ∘ k L ∘ g L ∎

  left→outer : is-pullback L → is-pullback outer
  left→outer Lpb X = split , is-eq split combine split-combine combine-split
    where
      split : (X → A) → Σ (X → E) (λ ε → Σ (X → B) (λ β → h outer ∘ ε == k outer ∘ β))
      split π = (f R ∘ f L ∘ π , (g L ∘ π , λ= {!!}))

      combine : Σ (X → E) (λ ε → Σ (X → B) (λ β → h outer ∘ ε == k outer ∘ β)) → X → A
      combine (ε , (β , ϑ)) = {!!}

      split-combine : (ω : Σ (X → E) (λ ε → Σ (X → B) (λ β → h outer ∘ ε == k outer ∘ β))) →
                      split (combine ω) == ω
      split-combine (ε , (β , ϑ)) = {!!}

      combine-split : (π : X → A) → combine (split π) == π
      combine-split π = {!!}

  left←outer : is-pullback outer → is-pullback L
  left←outer Opb X = {!!} , is-eq {!!} {!!} {!!} {!!}

