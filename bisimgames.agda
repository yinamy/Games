{-# OPTIONS --guardedness #-}

module bisimgames where

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

  -- Bisimulation
  record _≈_ (s t : Q) : Set where
    coinductive
    field
      d₁ : ∀{s′}{a} → s -⟨ a ⟩→ s′ → ∃ (λ t′ → t -⟨ a ⟩→ t′ × s′ ≈ t′)
      d₂ : ∀{t′}{a} → t -⟨ a ⟩→ t′ → ∃ (λ s′ → s -⟨ a ⟩→ s′ × s′ ≈ t′)


  BC : Player → Set
  BC S = Q × Q
  BC D = Q × Q × A × Two

  BM : (p : Player) (c : BC p) → Set
  BM S (q₁ , q₂) = Σ A (λ a → Σ Q (λ q₁′ → q₁ -⟨ a ⟩→ q₁′ )) ⊎  Σ A (λ a → Σ Q (λ q₂′ → q₂ -⟨ a ⟩→ q₂′ ))
  BM D (q₁ , q₂ , a , First) = Σ Q (λ q₂′ → q₂ -⟨ a ⟩→ q₂′)
  BM D (q₁ , q₂ , a , Second) =  Σ Q (λ q₁′ → q₁ -⟨ a ⟩→ q₁′)

  update-C : (p : Player) (c : BC p) (m : BM p c) → BC (op p)
  update-C S (q₁ , q₂) (inj₁ (a , q₁′ , t)) = q₁′ , q₂ , a , First
  update-C S (q₁ , q₂) (inj₂ (a , q₂′ , t)) = q₁ , q₂′ , a , Second
  update-C D (q₁ , q₂ , a , First) (q₂′ , t) = q₁ , q₂′
  update-C D (q₁ , q₂ , a , Second) (q₁′ , t) = q₁′ , q₂

  LTSBisimGame : Game BC BM
  LTSBisimGame = record
               { δ = update-C
               }


  open Game LTSBisimGame
  open _≈_

-- If a D-winning strategy exists, a bisimulation exists between 2 states
  LTS-bisim : {c : BC S} (w : DWStrat S c) → proj₁ c ≈ proj₂ c
  d₁ (LTS-bisim {q₁ , q₂} (Game.end x)) = λ x₁ → ⊥-elim (x (inj₁ (_ , (_ , x₁))))
  d₂ (LTS-bisim {q₁ , q₂} (Game.end x)) = λ x₁ → ⊥-elim (x (inj₂ (_ , (_ , x₁))))
  d₁ (LTS-bisim {q₁ , q₂} (Game.stepS x)) t with x (inj₁ (_ , _ , t))
  ... | Game.stepD (q₂′ , t′) x′ = _ , t′ , LTS-bisim (♭ x′)
  d₂ (LTS-bisim {q₁ , q₂} (Game.stepS x)) t with x (inj₂ (_ , _ , t))
  ... | Game.stepD (q₁′ , t′) x′ = _ , t′ , LTS-bisim (♭ x′)

  -- If a bisimulation exists between 2 states, then a D-winning strategy exists
  LTS-bisim₂ : { (q₁ , q₂) : BC S} → q₁ ≈ q₂ → DWStrat S (q₁ , q₂)
  LTS-bisim₂ {q₁ , q₂} p with d₁ p | d₂ p
  ... | z₁ | z₂ = Game.stepS (λ {
    (inj₁ (a , q , t)) → Game.stepD (_ , (proj₁ (proj₂ (z₁ t)))) (♯ (LTS-bisim₂ (proj₂ (proj₂ (z₁ t))))) ;
    (inj₂ (a , q , t)) → Game.stepD {!!} {!!}
    })

-- If an S-winning strategy exists, a bisimulation does not exist between 2 states
  LTS-not-bisim : {c : BC S} (w : SWStrat S c) → ¬ (proj₁ c ≈ proj₂ c)
  LTS-not-bisim {q₁ , q₂} (Game.stepS (inj₁ (a , q₁′ , t)) (Game.end x)) p with d₁ p t
  ... | q₂′ , t′ , p′ = x (_ , t′)
  LTS-not-bisim {q₁ , q₂} (Game.stepS (inj₂ (a , q₂′ , t)) (Game.end x)) p with d₂ p t
  ... | q₁′ , t′ , p′ = x (_ , t′)
  LTS-not-bisim {q₁ , q₂} (Game.stepS (inj₁ (a , q₁′ , t)) (Game.stepD x)) p with d₁ p t
  ... | q₂′ , t′ , p′ = LTS-not-bisim (x (_ , t′)) p′
  LTS-not-bisim {q₁ , q₂} (Game.stepS (inj₂ (a , q₂′ , t)) (Game.stepD x)) p with d₂ p t
  ... | q₁′ , t′ , p′ = LTS-not-bisim (x (_ , t′)) p′

-- Instantiating our bisimulation game to a stream equivalence game

-- A stream as an LTS
StreamLTS : LTS
StreamLTS = record
  { Q = Stream ℕ
  ; A = ℕ
  ; _-⟨_⟩→_ = λ q a q′ → del q a ≡ q′
  }
    where
      del : Stream ℕ → ℕ → Stream ℕ
      del (x ∷ xs) zero = ♭ xs
      del (x ∷ xs) (suc n) = x ∷ ♯ (del (♭ xs) n)
