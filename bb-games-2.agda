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
open import Function.Base using (case_of_)

-- A generic game with finite or infinite runs --------------------------------

-- The two players are S (spoiler), and D (duplicator)
data Player : Set where
    S D : Player

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
        → ∃ (λ t₁ → ∃ (λ t′ → t ⇒ t₁ × t₁ -⟨ a ⟩→ t′ × (s ≈ t₁) × (s′ ≈ t′)))
      d₁-τ : ∀{s′}
        → s -⟨τ⟩→ s′ → ∃ (λ t′ → t ⇒ t′ × (s ≈ t′) × (s′ ≈ t′))
          ⊎  ∃ (λ t₁ → ∃ (λ t′ → t ⇒ t₁ × t₁ -⟨τ⟩→ t′ × (s ≈ t₁) × (s′ ≈ t′)))
      d₂-a : ∀{t′}{a}
        → t -⟨ a ⟩→ t′
        → ∃ (λ s₁ → ∃ (λ s′ → s ⇒ s₁ × s₁ -⟨ a ⟩→ s′ × (t ≈ s₁) × (t′ ≈ s′)))
      d₂-τ : ∀{t′}
        → t -⟨τ⟩→ t′ → ∃ (λ s′ → s ⇒ s′ × (t ≈ s′) × (t′ ≈ s′))
          ⊎ ∃ (λ s₁ → ∃ (λ s′ → s ⇒ s₁ × s₁ -⟨τ⟩→ s′ × (t ≈ s₁) × (t′ ≈ s′)))

  open _≈_

  -- Game configurations
  BC : Player → Set
  BC S = Q × Q × Q × Q
  BC D = Q × Q × Q × Maybe A

  -- The possible moves
  data BM : (p : Player) (c : BC p) → Set where
    s-q₁-a : ∀{q₁ q₂ q₃ q₄ q₁′}{a}  → q₁ -⟨ a ⟩→ q₁′ → BM S (q₁ , q₂ , q₃ , q₄)
    s-q₂-a : ∀{q₁ q₂ q₃ q₄ q₂′}{a}  → q₂ -⟨ a ⟩→ q₂′ → BM S (q₁ , q₂ , q₃ , q₄)
    s-q₃-a : ∀{q₁ q₂ q₃ q₄ q₃′}{a}  → q₃ -⟨ a ⟩→ q₃′ → BM S (q₁ , q₂ , q₃ , q₄)
    s-q₄-a : ∀{q₁ q₂ q₃ q₄ q₄′}{a}  → q₄ -⟨ a ⟩→ q₄′ → BM S (q₁ , q₂ , q₃ , q₄)
    s-q₁-τ : ∀{q₁ q₂ q₃ q₄ q₁′}     → q₁ -⟨τ⟩→ q₁′   → BM S (q₁ , q₂ , q₃ , q₄)
    s-q₂-τ : ∀{q₁ q₂ q₃ q₄ q₂′}     → q₂ -⟨τ⟩→ q₂′   → BM S (q₁ , q₂ , q₃ , q₄)
    s-q₃-τ : ∀{q₁ q₂ q₃ q₄ q₃′}     → q₃ -⟨τ⟩→ q₃′   → BM S (q₁ , q₂ , q₃ , q₄)
    s-q₄-τ : ∀{q₁ q₂ q₃ q₄ q₄′}     → q₄ -⟨τ⟩→ q₄′   → BM S (q₁ , q₂ , q₃ , q₄)

    d-a : ∀{q₁ q₂ q₃ q₃′ q₃′′}{a} → q₃ ⇒ q₃′ → q₃′ -⟨ a ⟩→ q₃′′ → BM D (q₁ , q₂ , q₃ , just a)
    d-τ :  ∀{q₁ q₂ q₃ q₃′ q₃′′} → q₃ ⇒ q₃′ → q₃′ -⟨τ⟩→ q₃′′ → BM D (q₁ , q₂ , q₃ , nothing)
    d-empty :  ∀{q₁ q₂ q₃ q₃′} → q₃ ⇒ q₃′ → BM D (q₁ , q₂ , q₃ , nothing)

  update-C : (p : Player) (c : BC p) (m : BM p c) → BC (op p)
  update-C S (q₁ , q₂ , q₃ , q₄) (s-q₁-a {q₁′ = q₁′}{a = a} x) = q₁ , q₁′ , q₂ , just a
  update-C S (q₁ , q₂ , q₃ , q₄) (s-q₂-a {q₂′ = q₂′}{a = a} x) = q₂ , q₂′ , q₁ , just a
  update-C S (q₁ , q₂ , q₃ , q₄) (s-q₃-a {q₃′ = q₃′}{a = a} x) = q₃ , q₃′ , q₄ , just a
  update-C S (q₁ , q₂ , q₃ , q₄) (s-q₄-a {q₄′ = q₄′}{a = a} x) = q₄ , q₄′ , q₃ , just a
  update-C S (q₁ , q₂ , q₃ , q₄) (s-q₁-τ {q₁′ = q₁′} x) = q₁ , q₁′ , q₂ , nothing
  update-C S (q₁ , q₂ , q₃ , q₄) (s-q₂-τ {q₂′ = q₂′} x) = q₂ , q₂′ , q₁ , nothing
  update-C S (q₁ , q₂ , q₃ , q₄) (s-q₃-τ {q₃′ = q₃′} x) = q₃ , q₃′ , q₄ , nothing
  update-C S (q₁ , q₂ , q₃ , q₄) (s-q₄-τ {q₄′ = q₄′} x) = q₄ , q₄′ , q₃ , nothing
  update-C D (q₁ , q₂ , q₃ , just a) (d-a {q₃′ = q₃′}{q₃′′} x x₁) = q₁ , q₃′ , q₂ , q₃′′
  update-C D (q₁ , q₂ , q₃ , nothing) (d-τ {q₃′ = q₃′}{q₃′′} x x₁) = q₁ , q₃′ , q₂ , q₃′′
  update-C D (q₁ , q₂ , q₃ , nothing) (d-empty {q₃′ = q₃′} x) = q₁ , q₃′ , q₂ , q₃′

  BranchingBisimGame : Game BC BM
  BranchingBisimGame = record
                     { δ = update-C
                     }

  open Game BranchingBisimGame
  open _≈_

  -- If a winning strategy exists for S, then two states are branching bisimilar
  LTS-bisim₁ : {q₁ q₂ q₃ q₄ : Q} (w : DWStrat S (q₁ , q₂ , q₃ , q₄)) → q₁ ≈ q₂
  LTS-bisim₂ : {q₁ q₂ q₃ q₄ : Q} (w : DWStrat S (q₁ , q₂ , q₃ , q₄)) → q₃ ≈ q₄
  d₁-a (LTS-bisim₁ (Game.end x)) t = ⊥-elim (x (s-q₁-a t) )
  d₁-a (LTS-bisim₁ (Game.stepS x)) t with x (s-q₁-a t)
  ... | Game.stepD (d-a x₂ x₃) x₁ = _ , _ , x₂ , x₃ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁)
  d₁-τ (LTS-bisim₁ (Game.end x)) t = ⊥-elim (x (s-q₁-τ t))
  d₁-τ (LTS-bisim₁ (Game.stepS x)) t with x (s-q₁-τ t)
  ... | Game.stepD (d-τ x₂ x₃) x₁ = inj₂ (_ , _ , x₂ , x₃ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁))
  ... | Game.stepD (d-empty x₂) x₁ = inj₁ (_ , x₂ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁) )
  d₂-a (LTS-bisim₁ (Game.end x)) t = ⊥-elim (x (s-q₂-a t))
  d₂-a (LTS-bisim₁ (Game.stepS x)) t with x (s-q₂-a t)
  ... | Game.stepD (d-a x₂ x₃) x₁ = _ , _ , x₂ , x₃ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁)
  d₂-τ (LTS-bisim₁ (Game.end x)) t = ⊥-elim (x (s-q₂-τ t))
  d₂-τ (LTS-bisim₁ (Game.stepS x)) t with x (s-q₂-τ t)
  ... | Game.stepD (d-τ x₂ x₃) x₁ = inj₂ (_ , _ , x₂ , x₃ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁))
  ... | Game.stepD (d-empty x₂) x₁ = inj₁ (_ , x₂ ,  LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁))
  d₁-a (LTS-bisim₂ (Game.end x)) t = ⊥-elim (x (s-q₃-a t))
  d₁-a (LTS-bisim₂ (Game.stepS x)) t with x (s-q₃-a t)
  ... | Game.stepD (d-a x₂ x₃) x₁ = _ , _ , x₂ , x₃ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁)
  d₁-τ (LTS-bisim₂ (Game.end x)) t = ⊥-elim (x (s-q₃-τ t))
  d₁-τ (LTS-bisim₂ (Game.stepS x)) t with x (s-q₃-τ t)
  ... | Game.stepD (d-τ x₂ x₃) x₁ = inj₂ (_ , _ , x₂ , x₃ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁))
  ... | Game.stepD (d-empty x₂) x₁ = inj₁ (_ , x₂ ,  LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁))
  d₂-a (LTS-bisim₂ (Game.end x)) t = ⊥-elim (x (s-q₄-a t))
  d₂-a (LTS-bisim₂ (Game.stepS x)) t with x (s-q₄-a t)
  ... | Game.stepD (d-a x₂ x₃) x₁ = _ , _ , x₂ , x₃ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁)
  d₂-τ (LTS-bisim₂ (Game.end x)) t = ⊥-elim (x (s-q₄-τ t))
  d₂-τ (LTS-bisim₂ (Game.stepS x)) t with x (s-q₄-τ t)
  ... | Game.stepD (d-τ x₂ x₃) x₁ = inj₂ (_ , _ , x₂ , x₃ , LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁))
  ... | Game.stepD (d-empty x₂) x₁ = inj₁ (_ , x₂ ,  LTS-bisim₁ (♭ x₁) , LTS-bisim₂ (♭ x₁))

  -- If two states are branching bisimilar, then a winning strategy exists for S
  LTS-bisim₃ : {q₁ q₂ q₃ q₄ : Q} → q₁ ≈ q₂ → q₃ ≈ q₄ → DWStrat S (q₁ , q₂ , q₃ , q₄)
  LTS-bisim₃ {q₁}{q₂} b₁ b₂ with d₁-a b₁ | d₂-a b₁ | d₁-a b₂ | d₂-a b₂ | d₁-τ b₁ | d₂-τ b₁ | d₁-τ b₂ | d₂-τ b₂
  ... | z₁ | z₂ | z₃ | z₄ | y₁ | y₂ | y₃ | y₄ = Game.stepS
    (λ { (s-q₁-a t) → let (_ , _ , t₁ , t₂ , b₃ , b₄) = z₁ t in Game.stepD (d-a t₁ t₂) (♯ LTS-bisim₃ b₃ b₄) ;
         (s-q₂-a t) → let (_ , _ , t₁ , t₂ , b₃ , b₄) = z₂ t in Game.stepD (d-a t₁ t₂) (♯ LTS-bisim₃ b₃ b₄) ;
         (s-q₃-a t) → let (_ , _ , t₁ , t₂ , b₃ , b₄) = z₃ t in Game.stepD (d-a t₁ t₂) (♯ LTS-bisim₃ b₃ b₄) ;
         (s-q₄-a t) → let (_ , _ , t₁ , t₂ , b₃ , b₄) = z₄ t in Game.stepD (d-a t₁ t₂) (♯ LTS-bisim₃ b₃ b₄) ;
         (s-q₁-τ t) → case (d₁-τ b₁ t) of
           λ { (inj₁ (_ , t₁ , b₃ , b₄)) → Game.stepD (d-empty t₁) (♯ (LTS-bisim₃ b₃ b₄)) ;
               (inj₂ (_ , _ , t₁ , t₂ , b₃ , b₄)) → Game.stepD (d-τ t₁ t₂) (♯ (LTS-bisim₃ b₃ b₄)) } ;
         (s-q₂-τ t) → case (d₂-τ b₁ t) of
           λ { (inj₁ (_ , t₁ , b₃ , b₄)) → Game.stepD (d-empty t₁) (♯ (LTS-bisim₃ b₃ b₄)) ;
               (inj₂ (_ , _ , t₁ , t₂ , b₃ , b₄)) → Game.stepD (d-τ t₁ t₂) (♯ (LTS-bisim₃ b₃ b₄)) } ;
         (s-q₃-τ t) → case (d₁-τ b₂ t) of
           λ { (inj₁ (_ , t₁ , b₃ , b₄)) → Game.stepD (d-empty t₁) (♯ (LTS-bisim₃ b₃ b₄)) ;
               (inj₂ (_ , _ , t₁ , t₂ , b₃ , b₄)) → Game.stepD (d-τ t₁ t₂) (♯ (LTS-bisim₃ b₃ b₄)) } ;
         (s-q₄-τ t) → case (d₂-τ b₂ t) of
           λ { (inj₁ (_ , t₁ , b₃ , b₄)) → Game.stepD (d-empty t₁) (♯ (LTS-bisim₃ b₃ b₄)) ;
               (inj₂ (_ , _ , t₁ , t₂ , b₃ , b₄)) → Game.stepD (d-τ t₁ t₂) (♯ (LTS-bisim₃ b₃ b₄)) }
         })

  -- If an S-winning strategy exists, a bisimulation does not exist between 2 states
  LTS-not-bisim : {q₁ q₂ q₃ q₄ : Q} (w : SWStrat S (q₁ , q₂ , q₃ , q₄)) → ¬ (q₁ ≈ q₂ × q₃ ≈ q₄)
  LTS-not-bisim {q₁} (Game.stepS (s-q₁-a x) (Game.end x₁)) (p , _) with d₁-a p x
  ... | _ , _ , t₁ , t₂ , _ , _ = ⊥-elim (x₁ (d-a t₁ t₂))
  LTS-not-bisim (Game.stepS (s-q₁-a x) (Game.stepD x₁)) (p , _) with d₁-a p x
  ... | _ , _ , t₁ , t₂ , b₁ , b₂ = ⊥-elim ((LTS-not-bisim (x₁ (d-a t₁ t₂))) (b₁ , b₂))
  LTS-not-bisim (Game.stepS (s-q₂-a x) (Game.end x₁)) (p , _) with d₂-a p x
  ... | _ , _ , t₁ , t₂ , b₁ , b₂ = ⊥-elim (x₁ (d-a t₁ t₂))
  LTS-not-bisim (Game.stepS (s-q₂-a x) (Game.stepD x₁)) (p , _) with d₂-a p x
  ... | _ , _ , t₁ , t₂ , b₁ , b₂ = ⊥-elim ((LTS-not-bisim (x₁ (d-a t₁ t₂))) (b₁ , b₂))
  LTS-not-bisim (Game.stepS (s-q₃-a x) (Game.end x₁)) (_ , q) with d₁-a q x
  ... | _ , _ , t₁ , t₂ , _ , _ = ⊥-elim (x₁ (d-a t₁ t₂))
  LTS-not-bisim (Game.stepS (s-q₃-a x) (Game.stepD x₁)) (_ , q) with d₁-a q x
  ... | _ , _ , t₁ , t₂ , b₁ , b₂ = ⊥-elim ((LTS-not-bisim (x₁ (d-a t₁ t₂))) (b₁ , b₂))
  LTS-not-bisim (Game.stepS (s-q₄-a x) (Game.end x₁)) (_ , q) with d₂-a q x
  ... | _ , _ , t₁ , t₂ , _ , _ = ⊥-elim (x₁ (d-a t₁ t₂))
  LTS-not-bisim (Game.stepS (s-q₄-a x) (Game.stepD x₁)) (_ , q) with d₂-a q x
  ... | _ , _ , t₁ , t₂ , b₁ , b₂ = ⊥-elim ((LTS-not-bisim (x₁ (d-a t₁ t₂))) (b₁ , b₂))
  LTS-not-bisim (Game.stepS (s-q₁-τ x) (Game.end x₁)) (p , _) with d₁-τ p x
  ... | inj₁ (_ , t₁ , b₁ , b₂) = ⊥-elim (x₁ (d-empty t₁))
  ... | inj₂ (_ , _ , t₁ , t₂ , b₁ , b₂) = ⊥-elim (x₁ (d-τ t₁ t₂))
  LTS-not-bisim (Game.stepS (s-q₁-τ x) (Game.stepD x₁)) (p , _) with d₁-τ p x
  ... | inj₁ (_ , t₁ , b₁ , b₂) = ⊥-elim (LTS-not-bisim (x₁ (d-empty t₁)) (b₁ , b₂))
  ... | inj₂ (_ , _ , t₁ , t₂ , b₁ , b₂) = ⊥-elim (LTS-not-bisim (x₁ (d-τ t₁ t₂)) (b₁ , b₂))
  LTS-not-bisim (Game.stepS (s-q₂-τ x) (Game.end x₁)) (p , _) with d₂-τ p x
  ... | inj₁ (_ , t₁ , b₁ , b₂) = ⊥-elim (x₁ (d-empty t₁))
  ... | inj₂ (_ , _ , t₁ , t₂ , b₁ , b₂) = ⊥-elim (x₁ (d-τ t₁ t₂))
  LTS-not-bisim (Game.stepS (s-q₂-τ x) (Game.stepD x₁)) (p , _) with d₂-τ p x
  ... | inj₁ (_ , t₁ , b₁ , b₂) = ⊥-elim (LTS-not-bisim (x₁ (d-empty t₁)) (b₁ , b₂))
  ... | inj₂ (_ , _ , t₁ , t₂ , b₁ , b₂) = ⊥-elim (LTS-not-bisim (x₁ (d-τ t₁ t₂)) (b₁ , b₂))
  LTS-not-bisim (Game.stepS (s-q₃-τ x) (Game.end x₁)) (_ , q) with d₁-τ q x
  ... | inj₁ (_ , t₁ , b₁ , b₂) = ⊥-elim (x₁ (d-empty t₁))
  ... | inj₂ (_ , _ , t₁ , t₂ , b₁ , b₂) = ⊥-elim (x₁ (d-τ t₁ t₂))
  LTS-not-bisim (Game.stepS (s-q₃-τ x) (Game.stepD x₁)) (_ , q) with d₁-τ q x
  ... | inj₁ (_ , t₁ , b₁ , b₂) = ⊥-elim (LTS-not-bisim (x₁ (d-empty t₁)) (b₁ , b₂))
  ... | inj₂ (_ , _ , t₁ , t₂ , b₁ , b₂) = ⊥-elim (LTS-not-bisim (x₁ (d-τ t₁ t₂)) (b₁ , b₂))
  LTS-not-bisim (Game.stepS (s-q₄-τ x) (Game.end x₁)) (_ , q) with d₂-τ q x
  ... | inj₁ (_ , t₁ , b₁ , b₂) = ⊥-elim (x₁ (d-empty t₁))
  ... | inj₂ (_ , _ , t₁ , t₂ , b₁ , b₂) = ⊥-elim (x₁ (d-τ t₁ t₂))
  LTS-not-bisim (Game.stepS (s-q₄-τ x) (Game.stepD x₁)) (_ , q) with d₂-τ q x
  ... | inj₁ (_ , t₁ , b₁ , b₂) = ⊥-elim (LTS-not-bisim (x₁ (d-empty t₁)) (b₁ , b₂))
  ... | inj₂ (_ , _ , t₁ , t₂ , b₁ , b₂) = ⊥-elim (LTS-not-bisim (x₁ (d-τ t₁ t₂)) (b₁ , b₂))
