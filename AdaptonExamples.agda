module AdaptonExamples where

open import StdLib

open import Type
open import Term
open import TypedTerm

------------------------------------
-- Church style well-typed terms

open Church

unitterm : ∀ {n} → WtVTerm {_} {n} [] vunit
unitterm = unit

mapboollist : WtCTerm [] (u (bool ⇒ f bool) ⇒ (bool-list ⇒ f bool-list))
mapboollist = lam (u (bool ⇒ f bool)) (fix (bool-list ⇒ f bool-list) (lam bool-list (
              unroll (var (# 0) refl) (case (var (# 0) refl)
                (ret (var (# 2) refl))
                (split (var (# 0) refl)
                (bind bool-list ← force (var (# 5) refl) ∙ var (# 0) refl within
                  (bind bool ← force (var (# 7) refl) ∙ var (# 2) refl within
                    (ret (roll (vunit ⊕ (bool ⊗ xvar (# 0))) (inj₂ (var (# 3) refl , var (# 1) refl))))) ))))))

copyboollist : WtCTerm [] (bool-list ⇒ f bool-list)
copyboollist = mapboollist ∙ thk (lam bool (ret (var (# 0) refl)))

-- parametric map
--maplist : ∀ τ {σ} → CTerm [] (u (τ ⇒ f σ) ⇒ ((list τ) ⇒ f (list σ)))
--maplist τ {σ} = lam (u (τ ⇒ f σ)) (fix ((list τ) ⇒ f (list τ)) (lam (list τ) (
--               unroll (var (# 0) refl) (case (var (# 0) refl)
--                                                (ret (var (# 2) refl))
--                                                (split (var (# 0) refl)
--                                                  (bind (list τ) ← force (var (# 5) refl) ∙ var (# 0) refl within
--                                                    (bind τ ← force (var (# 7) refl) ∙ var (# 2) refl within
--                                                      (ret (roll (vunit ⊕ (σ ⊗ xvar (# 0))) (inj₂ (var (# 3) refl , var (# 1) refl))))) ))))))
  
