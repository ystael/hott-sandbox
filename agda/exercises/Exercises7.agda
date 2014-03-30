module exercises.Exercises7 where

open import HoTT public

-- 7.12. Show that ¬¬ is a modality.

¬¬-is-prop : ∀ {i} (A : Type i) → is-prop (¬ (¬ A))
¬¬-is-prop A = Π-is-prop (λ _ → ⊥-is-prop)

-- (i) functions η_A : A → ¬¬A for every type A.

¬¬-modal-η : ∀ {i} {A : Type i} → A → ¬ (¬ A)
¬¬-modal-η a ¬a = ¬a a

-- (ii) for every A : U and every type family B : ¬¬A → U, a function
-- ind-¬¬ : Π a:A. ¬¬(B(η_A(a))) → Π z:¬¬A. ¬¬(B(z)) (i.e. to give a
-- dependent function on ¬¬A into a ¬¬ type family, it suffices to give a
-- dependent function on A into the ¬¬-embedding of A in the type family).

¬¬-modal-ind : ∀ {i j} {A : Type i} (B : ¬ (¬ A) → Type j) →
               ((a : A) → ¬ (¬ (B (¬¬-modal-η a)))) →
               (z : ¬ (¬ A)) → ¬ (¬ (B z))
¬¬-modal-ind {A = A} B f z =
  let f' = λ (a : A) →
             let p = prop-has-all-paths (¬¬-is-prop A) (¬¬-modal-η a) z
             in transport (¬ ∘ ¬ ∘ B) p (f a)
  in λ ¬Bz → z (λ a → f' a (¬Bz))

-- (iii) a path ind-¬¬(f)(η_A(a)) = f(a) for each f : Π a:A. ¬¬(B(η_A(a))).

¬¬-modal-β : ∀ {i j} {A : Type i} (B : ¬ (¬ A) → Type j) →
             (f : (a : A) → ¬ (¬ (B (¬¬-modal-η a)))) → (a : A) →
             ¬¬-modal-ind B f (¬¬-modal-η a) == f a
¬¬-modal-β B f a = prop-has-all-paths (¬¬-is-prop (B (¬¬-modal-η a)))
                     (¬¬-modal-ind B f (¬¬-modal-η a)) (f a)

-- (iv) For any z, z' : ¬¬A, the function η_{z=z'} : (z = z') → ¬¬(z = z')
-- is an equivalence.

¬¬-modal-path-equiv : ∀ {i} {A : Type i} {z z' : ¬ (¬ A)} →
                      is-equiv (¬¬-modal-η {A = (z == z')})
¬¬-modal-path-equiv {A = A} {z = z} {z' = z'} = is-eq ¬¬-modal-η g f-g g-f
  where
    f = ¬¬-modal-η
    g : ¬ (¬ (z == z')) → (z == z')
    g _ =  prop-has-all-paths (¬¬-is-prop A) z z'
    f-g : (¬¬p : ¬ (¬ (z == z'))) → f (g ¬¬p) == ¬¬p
    f-g ¬¬p = prop-has-all-paths (¬¬-is-prop (z == z')) (f (g ¬¬p)) ¬¬p
    g-f : (p : z == z') → g (f p) == p
    g-f p = contr-has-all-paths (¬¬-is-prop A z z') (g (f p)) p
