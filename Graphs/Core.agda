module Graphs.Core where

open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe as Maybe using (just; nothing)
open import Data.Nat using (_+_; ℕ)
open import Data.Vec using ([])
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
--open import Data.Graph.Acyclic

------------------------------
-- Graphs, pointers, and names
data Name : Set where
  □   : Name
  _∙1 : Name → Name
  _∙2 : Name → Name

data Namespace : Set where
  ∅    : Namespace
  _∷∙_ : Namespace → Name → Namespace

data Pointer : Set where
  _◂_  : Name → Namespace → Pointer
