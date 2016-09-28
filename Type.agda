module Type where

open import Data.Fin using (Fin; zero; suc; toℕ; inject; #_) renaming (inject₁ to injectFin)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_) renaming (_≟_ to _≟ℕ_)
open import Data.Vec using (Vec; []; _∷_; lookup; _[_]=_; here; there) 
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; cong; cong₂) 
open import Relation.Nullary using (¬_; Dec; yes; no) 
open import Function using (_∘_; _$_) 
open import Data.String using (String) renaming (_≟_ to ≟-String)
--open import Data.Sum public hiding (map)
--open import Data.Product public hiding (map)
--open import Data.Empty 
--open import Data.Unit hiding (_≤?_)
open import Data.Sum using (_⊎_) renaming (inj₁ to ι₁; inj₂ to ι₂)

module Syntax where
  -- Types
  data VType : Set
  data CType : Set
  
  infixr 7 _⇒_
  data VType where
    vunit : VType
    _⊕_ : VType → VType → VType
    _⊗_ : VType → VType → VType
    u   : CType → VType
    m   : String → VType
    μ   : String → VType → VType
      
  data CType where
    _⇒_ : VType → CType → CType
    f   : VType → CType

-- Types with up to n free variables
data VType (n : ℕ) : Set
data CType (n : ℕ) : Set

--infixr 5 _⊗_
infixr 7 _⇒_
data VType (n : ℕ) where
  vunit : VType n
  xvar  : Fin n → VType n
  _⊕_   : VType n → VType n → VType n
  _⊗_   : VType n → VType n → VType n
  u     : CType n → VType n
  vm    : VType n → VType n
  μ     : VType (1 + n) → VType n
    
data CType (n : ℕ) where
  _⇒_  : VType n → CType n → CType n
  f    : VType n → CType n

-- This just seems to be useless
data Type (n : ℕ) : Set where
  vtype : VType n → Type n
  ctype : CType n → Type n

bool : ∀ {n} → VType n 
bool = vunit ⊕ vunit

--------------------------------------------
-- Type substitutions using standard library
module TypeSubst where
  -- Following Data.Fin.Substitutions.Example
  module TypeApp {T} (l : Lift T VType) where
    open Lift l hiding (var)

    -- Applies a substitution to a type
    infixl 8 _/v_
    infixl 8 _/c_

    _/v_ : ∀ {m n} → VType m → Sub T m n → VType n
    _/c_ : ∀ {m n} → CType m → Sub T m n → CType n
    vunit /v ρ = vunit
    (xvar x) /v ρ = lift (lookup x ρ)
    (σ ⊕ τ) /v ρ = (τ /v ρ) ⊕ (τ /v ρ)
    (σ ⊗ τ) /v ρ = (σ /v ρ) ⊗ (τ /v ρ)
    (u σ) /v ρ = u (σ /c ρ)
    (vm a) /v ρ = vm (a /v ρ)
    (μ τ) /v ρ = μ (τ /v ρ ↑)
    (σ ⇒ τ) /c ρ = σ /v ρ ⇒ τ /c ρ
    f x /c ρ = f (x /v ρ)

    open Application (record { _/_ = _/v_ }) using (_/✶_)

  typeSubst : TermSubst VType
  typeSubst = record { var = xvar; app = TypeApp._/v_ }

  open TermSubst typeSubst public hiding (var) renaming (_/_ to _/v_)

  weaken↑ : ∀ {n} → VType (1 + n) → VType (2 + n)
  weaken↑ τ = τ /v (wk ↑)
  
  infix 8 _[/v_] _[/c_]

  -- single type substitution
  _[/v_] : ∀ {n} → VType (1 + n) → VType n → VType n
  τ [/v σ ] = τ /v sub σ

  open Application (record { _/_ = TypeApp._/c_ termLift }) renaming (_/_ to _/c_)

  _[/c_] : ∀ {n} → CType (1 + n) → VType n → CType n
  σ [/c τ ] = σ /c sub τ

  private
    -- example sub of vtype into a ctype
    fx : CType 1
    fx = f (xvar (# 0))

    subinc : CType 0
    subinc = fx [/c vunit ]

list : ∀ {n} → VType n → VType n
list τ = μ (vunit ⊕ (TypeSubst.weaken τ ⊗ xvar zero))

bool-list : VType 0
bool-list = list bool

