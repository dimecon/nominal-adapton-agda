module TypeChecking where

open import Data.Fin using (Fin; suc; zero; pred)
open import Data.Nat as Nat using (ℕ; _+_)
open import Data.Product
open import Data.Vec using (_∷_; []; lookup)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Type
open import Term
open import TypedTerm

open TypeSubst using () renaming (_[/v_] to _[/vTp_]; _[/c_] to _[/cTp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

-----------------------------------------------
-- convenient syntactic equality preservations

infix 4 _≡vtp_ _≡ctp_

≡suc : ∀ {n} {x y : Fin n} → suc x ≡ suc y → x ≡ y
≡suc refl = refl

_≡vtp_ : ∀ {n} → VType n → VType n → Set
τ ≡vtp σ = τ ≡ σ

_≡ctp_ : ∀ {n} → CType n → CType n → Set
τ ≡ctp σ = τ ≡ σ

≡xvar : ∀ {n} {x y : Fin n} → xvar x ≡vtp xvar y → x ≡ y
≡xvar refl = refl

≡⇒₁ : ∀ {n} {τ τ′ : VType n} {σ σ′ : CType n}
      → τ ⇒ σ ≡ctp τ′ ⇒ σ′ → τ ≡ τ′
≡⇒₁ refl = refl

≡⇒₂ : ∀ {n} {τ τ′ : VType n} {σ σ′ : CType n}
      → τ ⇒ σ ≡ctp τ′ ⇒ σ′ → σ ≡ σ′
≡⇒₂ refl = refl

≡⊕₁ : ∀ {n} {τ σ τ′ σ′ : VType n} → τ ⊕ σ ≡vtp τ′ ⊕ σ′ → τ ≡vtp τ′
≡⊕₁ refl = refl

≡⊕₂ : ∀ {n} {τ σ τ′ σ′ : VType n} → τ ⊕ σ ≡vtp τ′ ⊕ σ′ → σ ≡vtp σ′
≡⊕₂ refl = refl

≡⊗₁ : ∀ {n} {τ σ τ′ σ′ : VType n} → τ ⊗ σ ≡vtp τ′ ⊗ σ′ → τ ≡vtp τ′
≡⊗₁ refl = refl

≡⊗₂ : ∀ {n} {τ σ τ′ σ′ : VType n} → τ ⊗ σ ≡vtp τ′ ⊗ σ′ → σ ≡vtp σ′
≡⊗₂ refl = refl

≡u : ∀ {n} {τ τ′ : CType n} → u τ ≡vtp u τ′ → τ ≡ctp τ′
≡u refl = refl

≡vm : ∀ {n} {τ τ′ : VType n} → vm τ ≡vtp vm τ′ → τ ≡vtp τ′
≡vm refl = refl

≡μ : ∀ {n} {τ τ′ : VType (1 + n)} → μ τ ≡vtp μ τ′ → τ ≡ τ′
≡μ refl = refl

≡f : ∀ {n} {τ τ′ : VType n} → f τ ≡ctp f τ′ → τ ≡ τ′
≡f refl = refl

---------------------------------------------------------------------
-- Decision procedures for syntactic equality of variables and types

infix 4 _≟n_

-- Decide equality of variables
_≟n_ : ∀ {n} → Decidable {A = Fin n} _≡_
zero  ≟n zero   = yes refl
suc x ≟n suc y  with x ≟n y
... | yes x≡y   = yes (cong suc x≡y)
... | no  x≢y   = no (x≢y ∘ ≡suc)
zero  ≟n suc y  = no λ()
suc x ≟n zero   = no λ()

-- Decide equality of types
_≟v_ : ∀ {n} → Decidable {A = VType n} _≡_
_≟c_ : ∀ {n} → Decidable {A = CType n} _≡_

vunit ≟v vunit               = yes refl
vunit ≟v xvar x              = no (λ ())
vunit ≟v (_ ⊕ _)             = no (λ ())
vunit ≟v (_ ⊗ _)             = no (λ ())
vunit ≟v u _                 = no (λ ())
vunit ≟v vm _                = no (λ ())
vunit ≟v μ _                 = no (λ ())
xvar x ≟v vunit              = no (λ ())
xvar x ≟v xvar y    with x ≟n y
xvar x ≟v xvar .x | yes refl = yes refl
...               | no  x≢y  = no (x≢y ∘ ≡xvar)
xvar x ≟v (_ ⊕ _)            = no (λ ())
xvar x ≟v (_ ⊗ _)            = no (λ ())
xvar x ≟v u _                = no (λ ())
xvar x ≟v vm _               = no (λ ())
xvar x ≟v μ _                = no (λ ())
(x ⊕ y) ≟v vunit             = no (λ ())
(x ⊕ y) ≟v xvar _            = no (λ ())
(x ⊕ y) ≟v (x′ ⊕ y′) with x ≟v x′ | y ≟v y′
(x ⊕ y) ≟v (.x ⊕ .y) | yes refl | yes refl = yes refl
... | no x≢x′ | _      = no (x≢x′ ∘ ≡⊕₁)
... | _      | no y≢y′ = no (y≢y′ ∘ ≡⊕₂)
(x ⊕ y) ≟v (_ ⊗ _) = no (λ ())
(x ⊕ y) ≟v u _ = no (λ ())
(x ⊕ y) ≟v vm _ = no (λ ())
(x ⊕ y) ≟v μ _ = no (λ ())
(x ⊗ y) ≟v vunit = no (λ ())
(x ⊗ y) ≟v xvar _ = no (λ ())
(x ⊗ y) ≟v (_ ⊕ _) = no (λ ())
(x ⊗ y) ≟v (x′ ⊗ y′) with x ≟v x′ | y ≟v y′
(x ⊗ y) ≟v (.x ⊗ .y) | yes refl | yes refl = yes refl
... | no x≢x′ | _      = no (x≢x′ ∘ ≡⊗₁)
... | _      | no y≢y′ = no (y≢y′ ∘ ≡⊗₂)
(x ⊗ y) ≟v u _ = no (λ ())
(x ⊗ y) ≟v vm _ = no (λ ())
(x ⊗ y) ≟v μ _ = no (λ ())
u x ≟v vunit = no (λ ())
u x ≟v xvar _ = no (λ ())
u x ≟v (_ ⊕ _) = no (λ ())
u x ≟v (_ ⊗ _) = no (λ ())
u x ≟v u y with x ≟c y
u x ≟v u .x | yes refl = yes refl
...         | no x≢y = no (x≢y ∘ ≡u)
u x ≟v vm _ = no (λ ())
u x ≟v μ _ = no (λ ())
vm x ≟v vunit = no (λ ())
vm x ≟v xvar _ = no (λ ())
vm x ≟v (_ ⊕ _) = no (λ ())
vm x ≟v (_ ⊗ _) = no (λ ())
vm x ≟v u _ = no (λ ())
vm x ≟v vm y with x ≟v y
vm x ≟v vm .x | yes refl = yes refl
... | no x≢y = no (x≢y ∘ ≡vm)
vm x ≟v μ _ = no (λ ())
μ x ≟v vunit = no (λ ())
μ x ≟v xvar _ = no (λ ())
μ x ≟v (_ ⊕ _) = no (λ ())
μ x ≟v (_ ⊗ _) = no (λ ())
μ x ≟v u _ = no (λ ())
μ x ≟v vm _ = no (λ ())
μ x ≟v μ y with x ≟v y
μ x ≟v μ .x | yes refl = yes refl
... | no x≢y = no (x≢y ∘ ≡μ)

(x ⇒ y) ≟c (x′ ⇒ y′) with x ≟v x′ | y ≟c y′
(x ⇒ y) ≟c (.x ⇒ .y) | yes refl | yes refl = yes refl
... | no x≢x′ | _      = no (x≢x′ ∘ ≡⇒₁)
... | _      | no y≢y′ = no (y≢y′ ∘ ≡⇒₂)
(x ⇒ y) ≟c f _ = no (λ ())
f x ≟c (_ ⇒ _) = no (λ ())
f x ≟c f y with x ≟v y
f x ≟c f .x | yes refl = yes refl
... | no x≢y = no (x≢y ∘ ≡f)
