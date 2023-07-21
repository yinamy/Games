{-# OPTIONS --guardedness #-}

module branching-bisim-games where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; _≟_; zero; suc; s≤s; _<_)
open import Agda.Builtin.Bool
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Codata.Musical.Notation
open import Codata.Musical.Colist

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


  BC : Player → Set
  BC S = Q × Q × Challenge × Reward
  BC D = Q × Q × Challenge × Reward

  BM : (p : Player) (c : BC p) → Set
  BM S (q₁ , q₂ , c , r) = Σ A (λ a → Σ Q (λ q₁′ → q₁ -⟨ a ⟩→ q₁′ × Dec (c ≡ (a , q₁′))))
    ⊎  Σ A (λ a → Σ Q (λ q₂′ → q₂ -⟨ a ⟩→ q₂′ × Dec (c ≡ (a , q₂′))))
    ⊎  Σ Q (λ q₁′ → q₁ -⟨τ⟩→ q₁′ × Dec (c ≡ (τ, q₁′)))
    ⊎  Σ Q (λ q₂′ → q₂ -⟨τ⟩→ q₂′ × Dec (c ≡ (τ, q₂′)))
  BM D (q₁ , q₂ , † , r) =  ⊥
  BM D (q₁ , q₂ , (a , x) , r) = {!!}
  BM D (q₁ , q₂ , (τ, x) , r) = {!!}


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
  -- if S does make a τ-move
  update-C D (q₁ , q₂ , c , r) m = {!!}
