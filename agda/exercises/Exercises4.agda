{-# OPTIONS --without-K #-}
module Exercises.Exercises4 where

open import HoTT public

-- 4.5. Prove that equivalences satisfy the 2-out-of-6 property: given f : A → B and g : B → C
-- and h : C → D, if g ◦ f and h ◦ g are equivalences, so are f , g, h, and h ◦ g ◦ f . Use
-- this to give a higher-level proof of Theorem 2.11.1.

module _ {i} {A B C D : Type i} (f : A → B) (g : B → C) (h : C → D)
             (gf-equiv : is-equiv (g ∘ f)) (hg-equiv : is-equiv (h ∘ g)) where

  private
    e-gf : A ≃ C
    e-gf = (g ∘ f , gf-equiv)

    e-hg : B ≃ D
    e-hg = (h ∘ g , hg-equiv)
    
    equiv-2/6-hgf : is-equiv (h ∘ g ∘ f)
    equiv-2/6-hgf = is-eq (h ∘ g ∘ f) k hgf-k k-hgf
      where
        k : D → A
        k = (<– e-gf) ∘ g ∘ (<– e-hg)

        hgf-k : (d : D) → (h ∘ g ∘ f) (k d) == d
        hgf-k d = (h ∘ g ∘ f) (k d)  =⟨ <–-inv-r e-gf (g (<– e-hg d)) |in-ctx h ⟩
                  h (g (<– e-hg d)) =⟨ <–-inv-r e-hg d ⟩
                  d ∎

        k-hgf : (a : A) → k ((h ∘ g ∘ f) a) == a
        k-hgf a = k ((h ∘ g ∘ f) a)  =⟨ <–-inv-l e-hg (f a) |in-ctx <– e-gf ∘ g ⟩
                  <– e-gf (g (f a)) =⟨ <–-inv-l e-gf a ⟩
                  a ∎

    e-hgf : A ≃ D
    e-hgf = (h ∘ g ∘ f , equiv-2/6-hgf)

    equiv-2/6-h : is-equiv h
    -- Want to just say snd (e-hgf ∘e e-gf ⁻¹) here, but we can't apply the homotopy
    -- automatically to see that hgf ∘ e-gf ⁻¹ is extensionally equal to h.
    equiv-2/6-h = is-eq h k h-k k-h
      where
        k : D → C
        k = fst (e-gf ∘e e-hgf ⁻¹)

        h-k : (d : D) → h (k d) == d
        h-k d = h (k d)           =⟨ <–-inv-r e-gf (g (<– e-hg d)) |in-ctx h ⟩
                h (g (<– e-hg d)) =⟨ <–-inv-r e-hg d ⟩ 
                d ∎

        k-h : (c : C) → k (h c) == c
        k-h c = k (h c)                   =⟨ ! (<–-inv-r e-gf c) |in-ctx k ∘ h ⟩
                k (h (g (f (<– e-gf c)))) =⟨ <–-inv-l e-hgf (<– e-gf c) |in-ctx –> e-gf ⟩
                –> e-gf (<– e-gf c)       =⟨ <–-inv-r e-gf c ⟩
                c ∎

    e-h : C ≃ D
    e-h = (h , equiv-2/6-h)

    equiv-2/6-f : is-equiv f
    -- similar to the above issue
    equiv-2/6-f = is-eq f k f-k k-f
      where
        k : B → A
        k = fst (e-hgf ⁻¹ ∘e e-hg)

        f-k : (b : B) → f (k b) == b
        f-k b = f (k b)                   =⟨ ! (<–-inv-l e-hg (f (k b))) ⟩
                <– e-hg (h (g (f (k b)))) =⟨ <–-inv-r e-hgf (–> e-hg b) |in-ctx <– e-hg ⟩
                <– e-hg (h (g b))         =⟨ <–-inv-l e-hg b ⟩
                b ∎

        k-f : (a : A) → k (f a) == a
        k-f a = <–-inv-l e-hgf a

    e-f : A ≃ B
    e-f = (f , equiv-2/6-f)

    equiv-2/6-g : is-equiv g
    -- similar to the above issue
    equiv-2/6-g = is-eq g k g-k k-g
      where
        k : C → B
        k = fst (e-hg ⁻¹ ∘e e-h)

        g-k : (c : C) → g (k c) == c
        g-k c = g (k c)                             =⟨ ! (<–-inv-r e-gf c) |in-ctx g ∘ <– e-hg ∘ h ⟩
                g (<– e-hg (h (g (f (<– e-gf c))))) =⟨ <–-inv-l e-hg (f (<– e-gf c)) |in-ctx g ⟩
                g (f (<– e-gf c))                   =⟨ <–-inv-r e-gf c ⟩
                c ∎

        k-g : (b : B) → k (g b) == b
        k-g b = <–-inv-l e-hg b

  -- Export the witnesses packed together as a record type
  record equiv-2/6 : Type i
    where
    field
      hgf-equiv : is-equiv (h ∘ g ∘ f)
      h-equiv : is-equiv h
      g-equiv : is-equiv g
      f-equiv : is-equiv f

  is-eq-2/6 : equiv-2/6
  is-eq-2/6 = record {hgf-equiv = equiv-2/6-hgf; h-equiv = equiv-2/6-h;
                      g-equiv   = equiv-2/6-g;   f-equiv = equiv-2/6-f}

equiv-ap′ : ∀ {i} {A B : Type i} (e : A ≃ B) →
            (x y : A) → is-equiv (ap (–> e) {x} {y})
equiv-ap′ e x y = equiv-2/6.g-equiv {!!} (ap (–> e)) (ap (<– e)) {!!} {!!}
                   (is-eq-2/6 {!!} (ap (–> e)) (ap (<– e)) {!!} {!!})
