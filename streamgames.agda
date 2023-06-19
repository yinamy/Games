{-# OPTIONS --guardedness #-}
module streamgames where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; _≟_; zero; suc; s≤s; _<_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List
open import Agda.Builtin.Bool
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Codata.Musical.Notation
open import Codata.Musical.Stream hiding (_≈_)
open import Codata.Musical.Conat using (Coℕ; zero; suc)


-- The two players are S (spoiler), and D (duplicator)
data Player : Set where
    S D : Player

data Two : Set where
    First Second : Two

-- Get the opposite of a player
op : Player → Player
op S = D
op D = S

-- A game is a set of configurations (C) and moves (M)
record Game (C : Player → Set) (M : (p : Player) → (c : C p) → Set) : Set where
  field
    -- δ is a function that makes a move to yield a new configuration for the other player
    δ : (p : Player) → (c : C p) → (m : M p c) → C (op p)
    -- a run of the game
  data Run (p : Player) (c : C p) : Set where
    end : (¬ M p c) → Run p c
    step : (m : M p c) → ∞ (Run (op p) (δ p c m)) → Run p c
    -- winning conditions for S (omitting D winning because D-Win = ¬ S-Win)
  data S-Win : (p : Player) (c : C p) (r : Run p c) → Set where
    finished : ∀{p : Player}{c}{x} → S-Win D c (end x)
    step : ∀{p}{c}{m}{r}
         → S-Win (op p) (δ p c m) (♭ r)
         → S-Win p c (step m r)

-- gets the nth element of a stream
nth : Stream ℕ → ℕ → ℕ
nth (x ∷ xs) zero = x
nth (x ∷ xs) (suc n) = nth (♭ xs) n

-- deletes the nth element of a stream
del : Stream ℕ → ℕ → Stream ℕ
del (x ∷ xs) zero = ♭ xs
del (x ∷ xs) (suc n) = x ∷ ♯ (del (♭ xs) n)

-- Definition of stream equivalence
infix 4 _≈_
data _≈_ : Stream ℕ → Stream ℕ → Set where
  step : ∀{m n : ℕ} (A : Stream ℕ) (B : Stream ℕ)
       → nth A n ≡ nth B m
       → ∞ (del A n ≈ del B n)
       → A ≈ B
