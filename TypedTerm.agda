module TypedTerm where

open import Data.Fin using (Fin; zero; suc; toℕ; #_; inject+)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; suc; _+_; _≤?_; _≥_) 
open import Data.Vec using (Vec; []; _∷_; lookup; _[_]=_; here; there; map)
open import Data.Vec.Properties
  using (map-∘; map-cong; lookup-morphism; lookup-++-inject+)
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; cong; cong₂; sym; subst)
open PropEq.≡-Reasoning
open import Relation.Nullary using (Dec; yes; no; ¬_) 
open import Function using (_∘_; _$_; flip) 
open import Data.String using (String) renaming (_≟_ to ≟-String)

open import Term
open import Type

Ctx : ℕ → ℕ → Set
Ctx m n = Vec (VType n) m

-- Type and variable substitutions lifted to typing contexts
module CtxSubst where
  --inflixl 8 _/_ _/Var_

  -- Type substitution
  _/_ : ∀ {m n k} → Ctx m n → Sub VType n k → Ctx m k
  Γ / ρ = Γ TypeSubst.⊙ ρ

  weaken : ∀ {m n} → Ctx m n → Ctx m (1 + n)
  weaken Γ = map TypeSubst.weaken Γ

  _/Var_ : ∀ {m n k} → Sub Fin m k → Ctx k n → Ctx m n
  ρ /Var Γ = map (λ x → lookup x Γ) ρ

open TypeSubst using () renaming (_[/v_]  to _[/vtp_])
open CtxSubst  using () renaming (weaken to weakenCtx)
open TermTermSubst using () renaming (weaken to weakenVTerm)

infix 4 _V⊢_∈_  _C⊢_∈_
infix 4 _V⊢_∉_  _C⊢_∉_
infix 4 _V⊢ˢ_∈_ _C⊢ˢ_∈_
infix 4 _t⊢_∈_

data _V⊢_∈_ {m n} (Γ : Ctx m n) : VTerm m n → VType n → Set
data _C⊢_∈_ {m n} (Γ : Ctx m n) : CTerm m n → CType n → Set

data _V⊢_∈_ {m n} (Γ : Ctx m n) where
  unit :
        ------------------- V-UNIT
        Γ V⊢ unit ∈ vunit

  var : (x : Fin m)
      → ------------------------- V-VAR
        Γ V⊢ xvar x ∈ lookup x Γ

  _,,_ : ∀ {v₁ v₂ τ₁ τ₂}
  
      → Γ V⊢ v₁ ∈ τ₁
      → Γ V⊢ v₂ ∈ τ₂
      → --------------------------------- V-PAIR
        Γ V⊢ (v₁ ,, v₂) ∈ τ₁ ⊗ τ₂

  inj₁ : ∀ {v τ₁ τ₂}
  
       → Γ V⊢ v ∈ τ₁
       → --------------------------- V-INJ₁
         Γ V⊢ inj₁ v ∈ τ₁ ⊕ τ₂

  inj₂ : ∀ {v τ₁ τ₂}
  
       → Γ V⊢ v ∈ τ₂
       → --------------------------- V-INJ₁
         Γ V⊢ inj₂ v ∈ τ₁ ⊕ τ₂

  thk : ∀ {e σ}
  
      → Γ C⊢ e ∈ σ
      → ------------------------ V-THUNK
        Γ V⊢ thunk e ∈ u σ

  roll : ∀ {v} (τ : VType (1 + n))
  
       → Γ V⊢ v ∈ τ [/vtp μ τ ]
       → ---------------------- V-ROLL
         Γ V⊢ roll τ v ∈ μ τ

data _C⊢_∈_ {m n} (Γ : Ctx m n) where
  lam : ∀ {σ e} (τ : VType n)
  
      → τ ∷ Γ C⊢ e ∈ σ
      → ----------------------- E-LAM
        Γ C⊢ lam τ e ∈ τ ⇒ σ

  ret : ∀ {v τ}
  
      → Γ V⊢ v ∈ τ
      → --------------------- E-RET
        Γ C⊢ ret v ∈ f τ

  _∙_ : ∀ {e v τ σ}
  
      → Γ C⊢ e ∈ τ ⇒ σ
      → Γ V⊢ v ∈ τ
      → -------------------- E-APP
        Γ C⊢ e ∙ v ∈ σ

  bind_←_within_ : ∀ τ {e₁ e₂ σ}
  
                 → Γ C⊢ e₁ ∈ f τ
                 → τ ∷ Γ C⊢ e₂ ∈ σ
                 → ------------------------------------ E-BIND
                   Γ C⊢ bind τ ← e₁ within e₂ ∈ σ

  case : ∀ {v σ τ₁ τ₂ e₁ e₂}
  
       → Γ V⊢ v ∈ τ₁ ⊕ τ₂
       → τ₁ ∷ Γ C⊢ e₁ ∈ σ
       → τ₂ ∷ Γ C⊢ e₂ ∈ σ
       → --------------------------------------- E-CASE
         Γ C⊢ case v ,[ τ₁ ] e₁ ,[ τ₂ ] e₂ ∈ σ

  split : ∀ {v e τ₁ τ₂ σ}

        → Γ V⊢ v ∈ τ₁ ⊗ τ₂
        → τ₂ ∷ τ₁ ∷ Γ C⊢ e ∈ σ
        → ---------------------------------------- E-SPLIT
          Γ C⊢ split weakenVTerm v ,[ τ₁ ][ τ₂ ] e ∈ σ

  fix : ∀ {σ e}
  
      → u σ ∷ Γ C⊢ e ∈ σ
      → ------------------------ E-FIX
        Γ C⊢ fix σ e ∈ σ

  force : ∀ {v σ}

        → Γ V⊢ v ∈ u σ
        → ------------------- E-FORCE
          Γ C⊢ force v ∈ σ

    -- unsure if this is different from below
--  unroll : ∀ {v e τ σ}
--
--         → Γ V⊢ v ∈ μ τ
--         → τ [/tp μ τ ] ∷ Γ C⊢ e ∈ σ
--         → ------------------------------------------ E-UNROLL
--           Γ C⊢ unroll τ (ret v) ∈ σ

  unroll : ∀ {v} → (τ : VType (1 + n))

         → Γ V⊢ v ∈ μ τ
         → ------------------------------------------ E-UNROLL
           Γ C⊢ unroll τ (ret v) ∈ f (τ [/vtp μ τ ])

  ref : ∀ {v τ}

      → Γ V⊢ v ∈ τ
      → ---------------------- E-REF
        Γ C⊢ ref v ∈ f (vm τ)

  get : ∀ {v τ}

      → Γ V⊢ v ∈ vm τ
      → ----------------- E-GET
        Γ C⊢ get v ∈ f τ

-- Shorthand for negations of well-typed terms
_V⊢_∉_ : ∀ {m n} → Ctx m n → VTerm m n → VType n → Set
Γ V⊢ v ∉ τ = ¬ Γ V⊢ v ∈ τ

_C⊢_∉_ : ∀ {m n} → Ctx m n → CTerm m n → CType n → Set
Γ C⊢ e ∉ σ = ¬ Γ C⊢ e ∈ σ

-- Well-typed terminal values
data _t⊢_∈_ {m n} (Γ : Ctx m n) : Terminal m n → CType n → Set where
  ret : ∀ {v τ} → Γ V⊢ v ∈ τ → Γ t⊢ ret v ∈ f τ 
  lam : ∀ {e σ} → (τ : VType n) → τ ∷ Γ C⊢ e ∈ σ → Γ t⊢ lam τ e ∈ τ ⇒ σ

⊢⌜_⌝ : ∀ {m n} {Γ : Ctx m n} {t τ}
     → Γ t⊢ t ∈ τ
     → Γ C⊢ ⌜ t ⌝ ∈ τ
⊢⌜ ret x ⌝   = ret x
⊢⌜ lam τ x ⌝ = lam τ x

-- Sequences of typing derivations for well-typed terms
data _V⊢ˢ_∈_ {m n} (Γ : Ctx m n) : ∀ {k} → Vec (VTerm m n) k → Vec (VType n) k → Set where
  []  : Γ V⊢ˢ [] ∈ []
  _∷_ : ∀ {v τ k} {vs : Vec (VTerm m n) k} {τs : Vec (VType n) k}
      → Γ V⊢ v ∈ τ → Γ V⊢ˢ vs ∈ τs → Γ V⊢ˢ v ∷ vs ∈ τ ∷ τs

data _C⊢ˢ_∈_ {m n} (Γ : Ctx m n) : ∀ {k} → Vec (CTerm m n) k → Vec (CType n) k → Set where
  []  : Γ C⊢ˢ [] ∈ []
  _∷_ : ∀ {e σ k} {es : Vec (CTerm m n) k} {σs : Vec (CType n) k}
      → Γ C⊢ e ∈ σ → Γ C⊢ˢ es ∈ σs → Γ C⊢ˢ e ∷ es ∈ σ ∷ σs

lookup-V⊢ : ∀ {m n k} {Γ : Ctx m n} {vs : Vec (VTerm m n) k} {τs : Vec (VType n) k}
          → (x : Fin k) → Γ V⊢ˢ vs ∈ τs → Γ V⊢ lookup x vs ∈ lookup x τs
lookup-V⊢ zero    (tm ∷ tms) = tm
lookup-V⊢ (suc x) (tm ∷ tms) = lookup-V⊢ x tms

---------------------------------------------------
-- Lemmas for substitutions in typing contexts Γ

module CtxLemmas where
  open CtxSubst public

  -- term variable substitution invariants
  idVar-/Var : ∀ {m n} (Γ : Ctx m n) → Γ ≡ (VarSubst.id /Var Γ)
  wkVar-/Var-∷ : ∀ {m n} (Γ : Ctx m n) (τ : VType n) → Γ ≡ (VarSubst.wk /Var (τ ∷ Γ))

  idVar-/Var [] = refl
  idVar-/Var (τ ∷ Γ) = cong (_∷_ τ) (wkVar-/Var-∷ Γ τ)

  wkVar-/Var-∷ Γ τ = begin
    Γ
      ≡⟨ idVar-/Var Γ ⟩
    VarSubst.id /Var Γ
      ≡⟨ map-∘ _ _ VarSubst.id ⟩
    VarSubst.wk /Var (τ ∷ Γ) ∎

----------------------------------------------------------
-- Substitution of well-typed value terms in well-typed terms
module WtTermTermSubst where
  private
    module TmTm = TermTermSubst
    TmSub = TmTm.TermSub VTerm

  infix 4 _⇒_⊢_

  _⇒_⊢_ : ∀ {m n k} → Ctx m n → Ctx k n → TmSub m n k → Set
  Γ ⇒ Δ ⊢ ρ = Δ V⊢ˢ ρ ∈ Γ

-----------------------------------------------------------------------------------
-- Typed terms (Church style)
-----------------------------------------------------------------------------------
module Church where
  data WtVTerm {m n} (Γ : Ctx m n) : VType n → Set
  data WtCTerm {m n} (Γ : Ctx m n) : CType n → Set

  data WtVTerm {m n} (Γ : Ctx m n) where
    unit :
           ------------- V-UNIT
           WtVTerm Γ vunit
         
    var : ∀ {τ} (v : Fin m) → lookup v Γ ≡ τ
        → -------------------------------------------- V-VAR
          WtVTerm Γ τ
        
    _,_ : ∀ {τ₁ τ₂} → WtVTerm Γ τ₁ → WtVTerm Γ τ₂
        → ------------------------------------ V-PAIR
          WtVTerm Γ (τ₁ ⊗ τ₂)
      
    inj₁ : ∀ {τ₁ τ₂} → WtVTerm Γ τ₁
         → ---------------------- V-INJ₁
           WtVTerm Γ (τ₁ ⊕ τ₂)
         
    inj₂ : ∀ {τ₁ τ₂} → WtVTerm Γ τ₂
         → ---------------------- V-INJ₂
           WtVTerm Γ (τ₁ ⊕ τ₂)
         
    thk : ∀ {τ} → WtCTerm Γ τ
        → ------------------ V-THUNK
          WtVTerm Γ (u τ)

    roll : ∀ (τ : VType (1 + n)) → WtVTerm Γ (τ [/vtp μ τ ])
         → ---------------------------------------------- ROLL
           WtVTerm Γ (μ τ)

  data WtCTerm {m n} (Γ : Ctx m n) where
    lam : ∀ σ {τ} → WtCTerm (σ ∷ Γ) τ
        → --------------------------------- E-LAM
          WtCTerm Γ (σ ⇒ τ)
        
    ret : ∀ {τ} → WtVTerm Γ τ
        → ------------------ E-RET
          WtCTerm Γ (f τ)
        
    _∙_ : ∀ {σ τ} → WtCTerm Γ (σ ⇒ τ) → WtVTerm Γ σ
        → -------------------------------------- E-APP
          WtCTerm Γ τ
        
    bind_←_within_ : ∀ σ {τ} → WtCTerm Γ (f σ) → WtCTerm (σ ∷ Γ) τ
                   → ------------------------------------------ E-BIND
                     WtCTerm Γ τ
                   
    case : ∀ {σ₁ σ₂ τ} → WtVTerm Γ (σ₁ ⊕ σ₂) → WtCTerm (σ₁ ∷ Γ) τ → WtCTerm (σ₂ ∷ Γ) τ
              → ---------------------------------------------------------------------------------------- E-CASE
                WtCTerm Γ τ
              
    split : ∀ {σ₁ σ₂ τ} → WtVTerm Γ (σ₁ ⊗ σ₂) → WtCTerm (σ₂ ∷ (σ₁ ∷ Γ)) τ
             → -------------------------------------------------------------------------- E-SPLIT
               WtCTerm Γ τ
             
    fix : ∀ τ → WtCTerm (u τ ∷ Γ) τ
        → --------------------------------- E-FIX
          WtCTerm Γ τ
        
    force : ∀ {τ} → WtVTerm Γ (u τ)
          → --------------------- E-FORCE
            WtCTerm Γ τ

    unroll : ∀ {τ} {σ} → WtVTerm Γ (μ τ) → WtCTerm ((τ [/vtp μ τ ]) ∷ Γ) σ
           → ------------------------------------------------------- UNROLL
             WtCTerm Γ σ
          
    ref : ∀ {τ} → WtVTerm Γ τ
        → ----------------- E-REF
          WtCTerm Γ (f (vm τ))
        
    get : ∀ {τ} → WtVTerm Γ (vm τ)
        → --------------------- E-GET
          WtCTerm Γ (f τ)

