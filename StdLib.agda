module StdLib where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_) public
open import Data.Fin using (Fin; zero; suc; toℕ; #_) public
open import Data.List using (List; []; _∷_; length) public
open import Data.Vec using (Vec; []; _∷_; lookup; _[_]=_; here; there) public
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂) public
open import Relation.Nullary using (Dec; yes; no) public
open import Function using (_∘_; _$_) public
open import Data.Sum public hiding (map)
open import Data.Product public hiding (map)
open import Data.Empty public
open import Data.Unit public hiding (_≤?_)

open import Relation.Nullary using (¬_; Dec; yes; no)

-- https://github.com/zmthy/recursive-types/blob/master/src/Language.agda
module VectorUtils where
  -- An empty vector cannot be indexed into.
  index-empty : ∀ {a} {A : Set a} {x : A} → ¬ ∃ λ i → [] [ i ]= x
  index-empty (_ , ())

  -- If a value is at a certain index in a vector, it is at the index one larger
  -- as the tail of another vector.
  index+1 : ∀ {a} {A : Set a} {n x y} {v : Vec A n} →
    (∃ λ i → v [ i ]= x) → (∃ λ i → (y ∷ v) [ i ]= x)
  index+1 (.zero , here)            = suc zero , there here
  index+1 (._    , there {i = i} p) = suc (suc i) , there (there p)

  -- If a value is at a certain index in a vector, and it is not the head of
  -- vector, it is at the index one smaller in the tail of that vector.
  index-1 : ∀ {a} {A : Set a} {n} {v : Vec A n} {x y} →
    x ≢ y → ∃ (λ i → y ∷ v [ i ]= x) → ∃ λ i → v [ i ]= x
  index-1 x≠y (.zero , here)
   with x≠y refl
  ... | ()
  index-1 x≠y (._    , there p) = _ , p

  -- Try and locate the given value in the given vector. If it exists, return
  -- the index it appeared at, and a proof that it appeared there.
  find : ∀ {a} {A : Set a} {n} (_≟_ : Decidable {A = A} _≡_)
    (x : A) (v : Vec A n) → Dec (∃ λ i → v [ i ]= x)
  find _   x []       = no index-empty
  find _≟_ x (y ∷ v)
   with x ≟ y
  ... | yes x=y rewrite x=y = yes (zero , here)
  ... | no x≠y
     with find _≟_ x v
  ...   | yes p        = yes (index+1 p)
  ...   | no ¬p        = no (¬p ∘ index-1 x≠y)
