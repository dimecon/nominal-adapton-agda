module Term where

open import Data.Fin using (Fin; zero; suc; toℕ; #_; inject+)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; suc; _+_; _≤?_; _≥_) 
open import Data.Vec using (Vec; []; _∷_; lookup; _[_]=_; here; there; map) 
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; cong; cong₂; sym) 
open import Relation.Nullary using (Dec; yes; no) 
open import Function using (_∘_; _$_; flip) 
open import Data.String using (String) renaming (_≟_ to ≟-String)

open import Type
open import Graphs.Core

-------------------------------------------------------------------------------------
-- Untyped terms and terminal values

-- Untyped terms with up to m free term variables and up to n free type variables
data VTerm (m n : ℕ) : Set
data CTerm (m n : ℕ) : Set

infixl 9 _∙_
data VTerm (m n : ℕ) where
  xvar : (x : Fin m) → VTerm m n -- value term variable
  unit : VTerm m n
  _,,_ : VTerm m n → VTerm m n → VTerm m n -- pair term
  inj₁ : VTerm m n → VTerm m n -- sum terms
  inj₂ : VTerm m n → VTerm m n
  thunk : CTerm m n → VTerm m n
  roll : VType (1 + n) → VTerm m n → VTerm m n -- roll recursive type
  -- programmers don't write these
  nm : Name → VTerm m n
  
data CTerm (m n : ℕ) where
  lam : VType n → CTerm (1 + m) n → CTerm m n -- term abstraction
  _∙_ : CTerm m n → VTerm m n → CTerm m n -- term application
  bind_←_within_ : VType n → CTerm m n → CTerm (1 + m) n → CTerm m n
  ret : VTerm m n → CTerm m n
  fix : CType n → CTerm (1 + m) n → CTerm m n
  case_,[_]_,[_]_ : VTerm m n → VType n → CTerm (1 + m) n → VType n → CTerm (1 + m) n → CTerm m n
  split_,[_][_]_ : VTerm (1 + m) n → VType n → VType n → CTerm (2 + m) n → CTerm m n
  force : VTerm m n → CTerm m n
  ref : VTerm m n → CTerm m n
  get : VTerm m n → CTerm m n
  unroll : VType (1 + n) → CTerm m n → CTerm m n -- unroll recursive type
  -- programmers don't write these
  fork : VTerm m n → CTerm m n

data Term (m n : ℕ) : Set where
  vterm : VTerm m n → Term m n
  cterm : CTerm m n → Term m n

-- Untyped Terminal Values
data Terminal (m n : ℕ) : Set where
  ret : VTerm m n → Terminal m n
  lam : VType n → CTerm (1 + m) n → Terminal m n

-- convert untyped terminal values to untyped terms
⌜_⌝ : ∀ {m n} → Terminal m n → CTerm m n
⌜ ret x ⌝ = ret x
⌜ lam τ e ⌝ = lam τ e

------------------------------------------------------------------------------------
-- Type substitutions in terms
module TermTypeSubst where
  module TermTypeApp {T} (l : Lift T VType) where
    open Lift l hiding (var)
    open TypeSubst.TypeApp l renaming (_/v_ to _/vtp_; _/c_ to _/ctp_)

    infixl 8 _/v_
    infixl 8 _/c_

    -- Apply a type substitution to a term
    _/v_ : ∀ {m n k} → VTerm m n → Sub T n k → VTerm m k
    _/c_ : ∀ {m n k} → CTerm m n → Sub T n k → CTerm m k
    xvar x /v ρ = xvar x
    nm x /v ρ = nm x
    unit /v ρ = unit
    x ,, y /v ρ = (x /v ρ) ,, (y /v ρ)
    inj₁ x /v ρ = inj₁ (x /v ρ)
    inj₂ x /v ρ = inj₂ (x /v ρ)
    thunk x /v ρ = thunk (x /c ρ)
    roll τ v /v ρ = roll (τ /vtp ρ ↑) (v /v ρ)
    lam τ e /c ρ = lam (τ /vtp ρ) (e /c ρ)
    e ∙ v /c ρ = (e /c ρ) ∙ (v /v ρ)
    bind τ ← e within e' /c ρ = bind τ /vtp ρ ← e /c ρ within (e' /c ρ)
    ret x /c ρ = ret (x /v ρ)
    fix σ e /c ρ = fix (σ /ctp ρ) (e /c ρ)
    case v ,[ τ ] e ,[ σ ] e' /c ρ = case v /v ρ ,[ τ /vtp ρ ] e /c ρ ,[ σ /vtp ρ ] (e' /c ρ)
    split v ,[ τ ][ σ ] e /c ρ = split v /v ρ ,[ τ /vtp ρ ][ σ /vtp ρ ] (e /c ρ)
    force v /c ρ = force (v /v ρ)
    ref x /c ρ = ref (x /v ρ)
    get x /c ρ = get (x /v ρ)
    unroll τ x /c ρ = unroll (τ /vtp ρ ↑) (x /c ρ)
    fork v /c ρ = fork (v /v ρ)

  open TypeSubst using (varLift; termLift; sub)

  module Lifted {T} (lift : Lift T VType) {m} where
    application : Application (VTerm m) T
    application = record { _/_ = TermTypeApp._/v_ lift {m = m} }

    -- TODO: may need to rename _/✶_ and _⊙_ to _/✶v_ and _⊙v_, ... for value and compuations
    open Application application public renaming (_/_ to _/v_)
    open Application (record { _/_ = TermTypeApp._/c_ lift {m = m} } ) public
      renaming (_/_ to _/c_) hiding (_/✶_; _⊙_)

  open Lifted termLift public

  -- Apply a type variable substitution (renaming) to a term
  _/vVar_ : ∀ {m n k} → VTerm m n → Sub Fin n k → VTerm m k
  _/cVar_ : ∀ {m n k} → CTerm m n → Sub Fin n k → CTerm m k
  _/vVar_ = TermTypeApp._/v_ varLift
  _/cVar_ = TermTypeApp._/c_ varLift

  -- Weaken a term with an additional type variable
  v-weaken : ∀ {m n} → VTerm m n → VTerm m (suc n)
  c-weaken : ∀ {m n} → CTerm m n → CTerm m (suc n)
  v-weaken t = t /vVar VarSubst.wk
  c-weaken t = t /cVar VarSubst.wk

  infix 8 _[/v_] _[/c_]

  -- Shorthand for single-variable type substitutions in terms
  _[/v_] : ∀ {m n} → VTerm m (1 + n) → VType n → VTerm m n
  v [/v τ ] = v /v sub τ
  
  _[/c_] : ∀ {m n} → CTerm m (1 + n) → VType n → CTerm m n
  e [/c τ ] = e /c sub τ

-- Substitution of value terms in terms
module TermTermSubst where
  TermSub : (ℕ → ℕ → Set) → ℕ → ℕ → ℕ → Set
  TermSub T m n k = Sub (flip T n) m k

  record TermLift (T : ℕ → ℕ → Set) : Set where
    infix 10 _↑tm _↑tp
    field
      lift : ∀ {m n} → T m n → VTerm m n
      _↑tm : ∀ {m n k} → TermSub T m n k → TermSub T (suc m) n (suc k)
      _↑tp : ∀ {m n k} → TermSub T m n k → TermSub T m (suc n) k

  module TermTermApp {T} (l : TermLift T) where
    open TermLift l

    infixl 8 _/v_
    infixl 8 _/c_
    
    _/v_ : ∀ {m n k} → VTerm m n → TermSub T m n k → VTerm k n
    _/c_ : ∀ {m n k} → CTerm m n → TermSub T m n k → CTerm k n
    unit /v ρ = unit
    nm x /v ρ = nm x
    xvar i /v ρ = lift (lookup i ρ)
    (v ,, v') /v ρ = (v /v ρ) ,, (v' /v ρ)
    inj₁ v /v ρ = inj₁ (v /v ρ)
    inj₂ v /v ρ = inj₂ (v /v ρ)
    thunk e /v ρ = thunk (e /c ρ)
    roll τ v /v ρ = roll τ (v /v ρ)
    lam σ e /c ρ = lam σ (e /c ρ ↑tm)
    ret v /c ρ = ret (v /v ρ)
    e ∙ v /c ρ = (e /c ρ) ∙ (v /v ρ)
    bind σ ← e within e' /c ρ = bind σ ← e /c ρ within (e' /c ρ ↑tm)
    case v ,[ τ ] e₁ ,[ σ ] e₂ /c ρ = case v /v ρ ,[ τ ] (e₁ /c ρ ↑tm) ,[ σ ] (e₂ /c ρ ↑tm)
    split v ,[ τ ][ σ ] e /c ρ = split v /v (ρ ↑tm) ,[ τ ][ σ ] (e /c ρ ↑tm ↑tm)
    fix σ e /c ρ = fix σ (e /c ρ ↑tm)
    force v /c ρ = force (v /v ρ)
    unroll τ e /c ρ = unroll τ (e /c ρ)
    ref v /c ρ = ref (v /v ρ)
    get v /c ρ = get (v /v ρ)
    fork v /c ρ = fork (v /v ρ)

  Fin' : ℕ → ℕ → Set
  Fin' m _ = Fin m
  
  varLift : TermLift Fin'
  varLift = record { lift = xvar; _↑tm = VarSubst._↑; _↑tp = Function.id }

  infixl 8 _/vVar_ _/cVar_

  _/vVar_ : ∀ {m n k} → VTerm m n → Sub Fin m k → VTerm k n
  _/vVar_ = TermTermApp._/v_ varLift

  _/cVar_ : ∀ {m n k} → CTerm m n → Sub Fin m k → CTerm k n
  _/cVar_ = TermTermApp._/c_ varLift

  VTerm′ : ℕ → ℕ → Set
  VTerm′ = flip VTerm

  CTerm′ : ℕ → ℕ → Set
  CTerm′ = flip CTerm

  private
    module ExpandSimple {n : ℕ} where
      v-simple : Simple (VTerm′ n)
      v-simple = record { var = xvar; weaken = λ t → t /vVar VarSubst.wk }

      open Simple v-simple public

  open ExpandSimple  using (_↑; v-simple)
  open TermTypeSubst using () renaming (v-weaken to v-weakenTp; c-weaken to c-weakenTp)

  termLift : TermLift VTerm
  termLift = record
    { lift = Function.id; _↑tm = _↑ ; _↑tp = λ ρ → map v-weakenTp ρ }

  --ctermLift : TermLift CTerm
  --ctermLift = record
  --  { lift = {!!}; _↑tm = {!!} ; _↑tp = λ ρ → map c-weakenTp ρ }

  private
    module ExpandSubst {n : ℕ} where
      v-app : Application (VTerm′ n) (VTerm′ n)
      v-app = record { _/_ = TermTermApp._/v_ termLift {n = n} }

      v-subst : Subst (flip VTerm n)
      v-subst = record
        { simple      = v-simple
        ; application = v-app
        }

      open Subst v-subst public

      c-app : Application (CTerm′ n) (VTerm′ n)
      c-app = record { _/_ = TermTermApp._/c_ termLift {n = n} }
      
      --c-subst : Subst (flip CTerm n)
      --c-subst = record
      --  { simple      = v-simple
      --  ; application = c-app
      --  }

      -- TODO: the star and circle dot things (value and compuation)
      open Application c-app public renaming (_/_ to _/c_) hiding (_/✶_; _⊙_)

  open ExpandSubst public hiding (var; simple)

  infix 8 _[/v_] _[/c_]
  
  _[/v_] : ∀ {m n} → VTerm (1 + m) n → VTerm m n → VTerm m n
  v [/v vₛ ] = v / sub vₛ
    
  _[/c_] : ∀ {m n} → CTerm (1 + m) n → VTerm m n → CTerm m n
  e [/c v ] = e /c sub v
