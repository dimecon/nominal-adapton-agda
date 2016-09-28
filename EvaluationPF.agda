module EvaluationPF where

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

open TypeSubst using () renaming (_[/v_] to _[/vTp_]; _[/c_] to _[/cTp)
open TermTypeSubst using () renaming (_[/v_] to _[/vTmTp]_]; _[/c_] to _[/cTmTp_])
open TermTermSubst using () renaming (_[/v_] to _[/vTmTm]_]; _[/c_] to _[/cTmTm_]; weaken to weakenVTerm)
--open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
--open WtTermTermSubst using () renaming (_[/_] to _[/⊢tmTm_])

------------------------------
-- Graphs, pointers, and names
data Name : Set where
  •     : Name
  left  : Name → Name
  right : Name → Name

data Namespace : Set where
  top  : Namespace
  nest : Name → Namespace

data Pointer : Set where
  _at_  : Name → Namespace → Pointer

data Action (m n : ℕ) : Set where
  alloc-ref : VTerm m n → Action m n
  alloc-thk : CTerm m n  → Action m n
  obs-ref   : VTerm m n  → Action m n
  obs-thk   : CTerm m n → Action m n

data Status : Set where
  clean dirty : Status

data Edge (m n : ℕ) : Set where
  edge : Pointer → Action m n → Status → Pointer → Edge m n

data Graph (m n : ℕ) : Set where
  ε : Graph m n
  ref : Graph m n → Pointer → VTerm m n → Graph m n
  thk : Graph m n → Pointer → CTerm m n → Graph m n
  res : Graph m n → Pointer → CTerm m n → CTerm m n → Graph m n
  edge : Graph m n → Edge m n → Graph m n

-----------------
-- With relations
module Common where

module NonIncremental where
  open Common

module Incremental where
  open  Common
