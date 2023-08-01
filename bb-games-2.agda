{-# OPTIONS --guardedness #-}

module bb-games-2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; _≟_; zero; suc; s≤s; _<_)
open import Agda.Builtin.Bool
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Codata.Musical.Notation
open import Codata.Musical.Stream hiding (_≈_)

-- A generic game with finite or infinite runs --------------------------------

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

  -- A winning strategy for S
  data SWStrat : (p : Player) (c : C p) → Set where
    end : ∀ {c} → (¬ M D c) → SWStrat D c
    stepS : ∀{c} → (m : M S c) → SWStrat D (δ S c m) → SWStrat S c
    stepD : ∀{c} → ((m : M D c) → SWStrat S (δ D c m)) → SWStrat D c

  -- A winning strategy for D
  data DWStrat : (p : Player) (c : C p) → Set where
    end : ∀ {c} → (¬ M S c) → DWStrat S c
    stepD : ∀{c} → (m : M D c) → ∞ (DWStrat S (δ D c m)) → DWStrat D c
    stepS : ∀{c} → (∀ (m : M S c) → DWStrat D (δ S c m)) → DWStrat S c

    -- law of the excluded middle (if there is an S-winning strategy there can't be one for D)
  exclMid : (p : Player) (c : C p) → SWStrat p c → ¬ (DWStrat p c)
  exclMid .D c (end x) (stepD m x₁) = x m
  exclMid .S c (stepS m q) (end x) = x m
  exclMid .S c (stepS m q) (stepS x) = exclMid D (δ S c m) q (x m)
  exclMid .D c (stepD x) (stepD m x₁) = exclMid S (δ D c m) (x m) (♭ x₁)

  -- other law of the excluded middle (if there is an D-winning strategy there can't be one for S)
  exclMid′ : (p : Player) (c : C p) → DWStrat p c → ¬ (SWStrat p c)
  exclMid′ .S c (end x) (stepS m p) = x m
  exclMid′ .D c (stepD m x) (end x₁) = x₁ m
  exclMid′ .D c (stepD m x) (stepD x₁) = exclMid′ S (δ D c m) (♭ x) (x₁ m)
  exclMid′ .S c (stepS x) (stepS m p) = exclMid′ D (δ S c m) (x m) p

-- A labelled transition system
record LTS : Set₁ where
  field
    Q : Set
    A : Set
    _-⟨_⟩→_ : Q → A → Q → Set
    _-⟨τ⟩→_ : Q → Q → Set


  -- Thing in Rob's deifnition of branching bisimulation that I need to use
  data _⇒_  : Q → Q → Set where
    n=0 : {s : Q} → s ⇒ s
    n>0 : {s t s₀ : Q} → s -⟨τ⟩→ s₀ → s₀ ⇒ t → s ⇒ t

  -- Branching bisimulation
  record _≈_ (s t : Q) : Set where
    coinductive
    field
      d₁-a : ∀{s′}{a}
        → s -⟨ a ⟩→ s′
        → ∃ (λ t₁ → ∃ (λ t′
          → t ⇒ t₁
            × t₁ -⟨ a ⟩→ t′
            × (s ≈ t₁) × (s′ ≈ t′)))
      d₁-τ : ∀{s′}
        → s -⟨τ⟩→ s′ → ∃ (λ t′ → t ⇒ t′ × (s′ ≈ t′))
      d₂-a : ∀{t′}{a}
        → t -⟨ a ⟩→ t′
        → ∃ (λ s₁ → ∃ (λ s′
          → s ⇒ s₁
            × s₁ -⟨ a ⟩→ s′
            × (s₁ ≈ t) × (s′ ≈ t′)))
      d₂-τ : ∀{t′}
        → t -⟨τ⟩→ t′ → ∃ (λ s′ → s ⇒ s′ × (s′ ≈ t′))



  BC : Player → Set
  BC S = Q × Q × Q
  BC D = Q × Q × Q × Maybe A

  BM : (p : Player) (c : BC p) → Set
  BM S (q₁ , q₂ , q₃) = {!!}
  BM D (q₁ , q₂ , q₃ , just x) = {!!}
  BM D (q₁ , q₂ , q₃ , nothing) = {!!}

  {-BM : (p : Player) (c : BC p) → Set
  BM S (q₁ , q₂) = Σ A (λ a → Σ Q (λ q₁′ → q₁ -⟨ a ⟩→ q₁′ )) ⊎  Σ A (λ a → Σ Q (λ q₂′ → q₂ -⟨ a ⟩→ q₂′ ))
  BM D (q₁ , q₂ , a , First) = Σ Q (λ q₂′ → q₂ -⟨ a ⟩→ q₂′)
  BM D (q₁ , q₂ , a , Second) =  Σ Q (λ q₁′ → q₁ -⟨ a ⟩→ q₁′)-}
