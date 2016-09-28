module Graphs where

open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe as Maybe using (just; nothing)
open import Data.Nat using (_+_; ℕ)
open import Data.Vec using ([])
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Data.Graph.Acyclic as Dag

open import Term
open import Graphs.Core public

data Action (m n : ℕ) : Set where
  alloc-ref : VTerm m n → Action m n
  alloc-thk : CTerm m n  → Action m n
  obs-ref   : VTerm m n  → Action m n
  obs-thk   : CTerm m n → Action m n

data Status : Set where
  clean dirty : Status

data Edge (m n : ℕ) : Set where
  edge : Pointer → Action m n → Status → Pointer → Edge m n

data Node (m n : ℕ) : Set where
  ref-_⟩_ : Pointer → VTerm m n → Node m n
  thk-_⟩_ : Pointer → CTerm m n → Node m n
  res-_⟩_[_] : Pointer → CTerm m n → CTerm m n → Node m n

-- demanded computation graphs
-- k nodes, m free term vars, n free type vars
DCG : ℕ → ℕ → ℕ → Set
DCG m n k = Dag.Graph (Node m n) (Edge m n) k

--private
--  example : DCG 0 0 3
--  example = (context {!!} {!!}) & {!!}

