{-# OPTIONS --guardedness #-}

module branching-bisim-games where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; _≟_; zero; suc; s≤s; _<_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Codata.Musical.Notation
open import Data.Maybe

-- A generic game with finite or infinite runs --------------------------------

-- The two players are S (spoiler), and D (duplicator)
data Player : Set where
    S D : Player

data Reward : Set where
    ✓ ⋆ : Reward

-- Get the opposite of a player
op : Player → Player
op S = D
op D = S

-- A game is a set of configurations (C) and moves (M)
record Game (C : Player → Set) (M : (p : Player) → (c : C p) → Set) : Set₁ where
  field
    -- δ is a function that makes a move to yield a new configuration for the other player
    δ : (p : Player) → (c : C p) → (m : M p c) → C (op p)
    reward? : {p : Player} → C p → Set

  -- The winning strategy of each player
  data DWStrat : (p : Player) (c : C p) → Set where
    -- A D-winning strategy for a finite play (where S eventually gets stuck)
    end : ∀ {c} → (¬ M S c) → DWStrat S c
    stepDFin : ∀{c} → (m : M D c) → DWStrat S (δ D c m) → DWStrat D c
    stepSFin : ∀{c} → (m : M S c) → DWStrat D (δ S c m) → DWStrat S c
    -- or an infinite play (with an infinite amount of ✓ rewards)
    stepDInf : ∀{c} → (m : M D c) → reward? c → ∞ (DWStrat S (δ D c m)) → DWStrat D c
    stepSInf : ∀{c} → (m : M S c) → reward? c → ∞ (DWStrat D (δ S c m)) → DWStrat S c

    -- An S-winning strategy for a finite play (where D eventually gets stuck)
  data SWStrat : (p : Player) (c : C p) → Set where
    end : ∀ {c} → (¬ M D c) → SWStrat D c
    stepSFin : ∀{c} → (m : M S c) → SWStrat D (δ S c m) → SWStrat S c
    stepDFin : ∀{c} → ((m : M D c) → SWStrat S (δ D c m)) → SWStrat D c
    -- or an infinite play (where the amount of ✓ rewards is finite)
    stepSInf : ∀{c} → (m : M S c) → ¬ (reward? c) → ∞ (SWStrat D (δ S c m)) → SWStrat S c
    stepDInf : ∀{c} → (m : M D c) → ¬ (reward? c) → ∞ (SWStrat S (δ D c m)) → SWStrat D c


-- A labelled transition system
record LTS : Set₁ where
  field
    Q : Set
    A : Set
    _-⟨_⟩→_ : Q → A → Q → Set
    _-⟨τ⟩→_ : Q → Q → Set

  data Challenge : Set where
    † : Challenge
    _,_ : A → Q → Challenge
    τ,_ : Q → Challenge

  -- Thing in Rob's deifnition of branching bisimulation that I need to use
  data _⇒_ (s t : Q) : Set where
    n=0 : s -⟨τ⟩→ t → s ⇒ t
    n≥0 : ∃ (λ s₀ → s -⟨τ⟩→ s₀ × s₀ ⇒ t) → s ⇒ t

  -- Branching bisimulation
  record _≈_ (s t : Q) : Set where
    coinductive
    field
      d₁ : ∀{s′}{a}
        → s -⟨ a ⟩→ s′ ⊎ s -⟨τ⟩→ s′
        → ∃ (λ t₁ → ∃ (λ t₂ → ∃ (λ t′
          → t ⇒ t₁
          → t₁ -⟨ a ⟩→ t₂ ⊎ t₁ -⟨τ⟩→ t₂
          → t₂ ≡ t′ × (s ≈ t₁) × (s′ ≈ t′))))

      d₂ : ∀{t′}{a}
        → t -⟨ a ⟩→ t′ ⊎ t -⟨τ⟩→ t′
        → ∃ (λ s₁ → ∃ (λ s₂ → ∃ (λ s′
          → s ⇒ s₁
          → s₁ -⟨ a ⟩→ s₂ ⊎ s₁ -⟨τ⟩→ s₂
          → s₂ ≡ s′ × (s₁ ≈ t) × (s′ ≈ t′))))

  -- Game configurations
  BC : Player → Set
  BC S = Q × Q × Challenge × Reward
  BC D = Q × Q × Challenge × Reward

  -- The possible moves
  BM : (p : Player) (c : BC p) → Set
  BM S (q₁ , q₂ , c , r) = Σ A (λ a → Σ Q (λ q₁′ → q₁ -⟨ a ⟩→ q₁′ × Dec (c ≡ (a , q₁′))))
    ⊎  Σ A (λ a → Σ Q (λ q₂′ → q₂ -⟨ a ⟩→ q₂′ × Dec (c ≡ (a , q₂′))))
    ⊎  Σ Q (λ q₁′ → q₁ -⟨τ⟩→ q₁′ × Dec (c ≡ (τ, q₁′)))
    ⊎  Σ Q (λ q₂′ → q₂ -⟨τ⟩→ q₂′ × Dec (c ≡ (τ, q₂′)))
  BM D (q₁ , q₂ , † , r) =  ⊥
  BM D (q₁ , q₂ , (τ, x) , r) = Maybe (Σ Q (λ q₂′ → q₂ -⟨τ⟩→ q₂′))
    ⊎ (Σ Q (λ q₂′ → q₂ -⟨τ⟩→ q₂′))
  BM D (q₁ , q₂ , (a , q₁′) , r) = Σ Q (λ q₂′ → q₂ -⟨ a ⟩→ q₂′)
    ⊎ (Σ Q (λ q₂′ → q₂ -⟨τ⟩→ q₂′))

  -- Updating the configuration after each move
  update-C : (p : Player) (c : BC p) (m : BM p c) → BC (op p)
  -- if S does not make a τ-move
  update-C S (q₁ , q₂ , c , r) (inj₁ (a , q₁′ , t , dec)) with dec in p
  ... | yes _ = q₁ , (q₂ , (c , ⋆))
  ... | no _ = q₁ , (q₂ , ((a , q₁′) , ✓))
  update-C S (q₁ , q₂ , c , r) (inj₂ (inj₁ (a , q₂′ , t , dec))) = q₂ , (q₁ , ((a , q₂′) , ✓))
  -- if S makes a τ-move
  update-C S (q₁ , q₂ , c , r) (inj₂ (inj₂ (inj₁ (q₁′ , t , dec)))) with dec in p
  ... | yes _ = q₁ , (q₂ , (c , ⋆))
  ... | no _ = q₁ , (q₂ , ((τ, q₁′) , ✓))
  update-C S (q₁ , q₂ , c , r) (inj₂ (inj₂ (inj₂ (q₂′ , t , dec)))) = q₂ , (q₁ , ((τ, q₂′) , ✓))
  -- if D answers the challenge
  update-C D (q₁ , q₂ , (a , q₁′) , r) (inj₁ (q₂′ , t)) = q₁′ , q₂′ , † , ✓
  -- if D procrastinates the challenge by making a τ-move
  update-C D (q₁ , q₂ , (a , q₁′) , r) (inj₂ (q₂′ , t)) = q₁ , q₂′ , (a , q₁′) , ⋆
  -- if the challenge to D is a τ-move, D can either make a corresponding τ-move
  update-C D (q₁ , q₂ , (τ, q₁′) , r) (inj₁ (just (q₂′ , t))) = q₁′ , q₂′ , † , ✓
  -- ... or D can do nothing
  update-C D (q₁ , q₂ , (τ, q₁′) , r) (inj₁ nothing) = q₁′ , q₂ , † , ✓
  -- or D can still procrastinate by making a random τ-move
  update-C D (q₁ , q₂ , (τ, q₁′) , r) (inj₂ (q₂′ , t)) = q₁ , q₂′ , (τ, q₁′) , ⋆

  reward-C : {p : Player} → (c : BC p) → Set
  reward-C {S} (_ , _ , _ , ✓) = ⊤
  reward-C {S} (_ , _ , _ , ⋆) = ⊥
  reward-C {D} (_ , _ , _ , ✓) = ⊤
  reward-C {D} (_ , _ , _ , ⋆) = ⊥

  BranchingBisimGame : Game BC BM
  BranchingBisimGame = record
                     { δ = update-C ;
                       reward? = reward-C
                     }
