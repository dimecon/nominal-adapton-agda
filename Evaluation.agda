module Evaluation where

open import Coinduction using (∞; ♯_; ♭)
open import Category.Monad
open import Category.Monad.Partiality.All as All using (All; now; later)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe as Maybe using (just; nothing)
open import Data.Nat using (_+_; ℕ)
open import Data.Vec using ([])
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

open import PartialityAndFailure as PF hiding (fail)
open PF.Equality hiding (fail)
open PF.Equivalence
private module M {f} = RawMonad (PF.monad {f})

open import Type
open import Term
open import TypedTerm

open import Graphs

open TypeSubst using () renaming (_[/v_] to _[/vTp_]; _[/c_] to _[/cTp_])
open TermTypeSubst using () renaming (_[/v_] to _[/vTmTp]_]; _[/c_] to _[/cTmTp_])
open TermTermSubst using () renaming (_[/v_] to _[/vTmTm]_]; _[/c_] to _[/cTmTm_]; weaken to weakenVTerm)
--open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
--open WtTermTermSubst using () renaming (_[/_] to _[/⊢tmTm_])

-----------------
-- With relations
module Common where
  data _⊢⟨_⟩_⇓_,_ {m n k} : DCG m n k → Pointer → CTerm m n → DCG m n k → Terminal m n → Set where
    term : ∀ {g₁ g₂ p,ω t}

         → ------------------------------- Eval-term
           g₁ ⊢⟨ p,ω ⟩ ⌜ t ⌝ ⇓ g₂ , t

    app : ∀ {g₁ g₂ g₃ p,ω e₁ e₂ t τ v}

        → g₁ ⊢⟨ p,ω ⟩ e₁ ⇓ g₂ , lam τ e₂
        → g₂ ⊢⟨ p,ω ⟩ e₂ [/cTmTm v ] ⇓ g₃ , t
        → -------------------------------------- Eval-app
          g₁ ⊢⟨ p,ω ⟩ e₁ ∙ v ⇓ g₃ , t

    fix : ∀ {g₁ g₂ p,ω fun e t}

        → g₁ ⊢⟨ p,ω ⟩ e [/cTmTm thunk (fix fun e) ] ⇓ g₂ , t
        → ---------------------------------------------------- Eval-fix
          g₁ ⊢⟨ p,ω ⟩ fix fun e ⇓ g₂ , t

    bind : ∀ {g₁ g₂ g₃ e₁ e₂ v t p,ω τ}

         → g₁ ⊢⟨ p,ω ⟩ e₁ ⇓ g₂ , ret v
         → g₂ ⊢⟨ p,ω ⟩ e₂ [/cTmTm v ] ⇓ g₃ , t
         → --------------------------------------------- Eval-bind
           g₁ ⊢⟨ p,ω ⟩ bind τ ← e₁ within e₂ ⇓ g₃ , t

    case₁ : ∀ {g₁ g₂ p,ω v e₁ e₂ t τ₁ τ₂}

         → g₁ ⊢⟨ p,ω ⟩ e₁ [/cTmTm v ] ⇓ g₂ , t
         → -------------------------------------------------- Eval-case
           g₁ ⊢⟨ p,ω ⟩ case inj₁ v ,[ τ₁ ] e₁ ,[ τ₂ ] e₂ ⇓ g₂ , t

    case₂ : ∀ {g₁ g₂ p,ω v e₁ e₂ t τ₁ τ₂}

         → g₁ ⊢⟨ p,ω ⟩ e₂ [/cTmTm v ] ⇓ g₂ , t
         → -------------------------------------------------- Eval-case
           g₁ ⊢⟨ p,ω ⟩ case inj₂ v ,[ τ₁ ] e₁ ,[ τ₂ ] e₂ ⇓ g₂ , t

    -- TODO: check weakening stuff
    split : ∀ {g₁ g₂ v₁ v₂ e t p,ω τ₁ τ₂}

          → g₁ ⊢⟨ p,ω ⟩ (e [/cTmTm v₁ ]) [/cTmTm v₂ ] ⇓ g₂ , t
          → ---------------------------------------------------------- Eval-split
            g₁ ⊢⟨ p,ω ⟩ split (v₁ ,, weakenVTerm v₂) ,[ τ₁ ][ τ₂ ] e ⇓ g₂ , t

    fork : ∀ {g p,ω k}

         → --
           g ⊢⟨ p,ω ⟩ fork (nm k) ⇓ g , ret (nm (k ∙1) ,, nm (k ∙2))

module NonIncremental where
  open Common

module Incremental where
  open  Common
