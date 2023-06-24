{-# OPTIONS --guardedness #-}
module streamgames where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; _≟_; zero; suc; s≤s; _<_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List
open import Agda.Builtin.Bool
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Codata.Musical.Notation
open import Codata.Musical.Stream hiding (_≈_)
open import Codata.Musical.Conat using (Coℕ; zero; suc)

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
    -- a run of the game
  data Run (p : Player) (c : C p) : Set where
    end : (¬ M p c) → Run p c
    step : (m : M p c) → ∞ (Run (op p) (δ p c m)) → Run p c
    -- winning conditions for S (omitting D winning because D-Win = ¬ S-Win)
  data S-Win : (p : Player) (c : C p) (r : Run p c) → Set where
    finished : ∀{p : Player}{c}{x} → S-Win D c (end x)
    unfinished : ∀{p}{c}{m}{r}
         → S-Win (op p) (δ p c m) (♭ r)
         → S-Win p c (step m r)

-- A stream equivalence game --------------------------------------------------

-- A configuration for a stream equivalence game
LC : Player → Set
LC S = (Stream ℕ × Stream ℕ)
LC D = (Stream ℕ × Stream ℕ × ℕ × Two)

-- gets you the right stream at D's turn based on S's choice
op-list : LC D → Two → Stream ℕ
op-list a First = proj₁ (proj₂ a)
op-list a Second = proj₁ a

-- gets the nth element of a stream
nth : Stream ℕ → ℕ → ℕ
nth (x ∷ xs) zero = x
nth (x ∷ xs) (suc n) = nth (♭ xs) n

-- deletes the nth element of a stream
del : Stream ℕ → ℕ → Stream ℕ
del (x ∷ xs) zero = ♭ xs
del (x ∷ xs) (suc n) = x ∷ ♯ (del (♭ xs) n)

-- A move in a stream equivalence game
LM : (p : Player) → (c : LC p) → Set
LM S (s₁ , s₂) = ℕ ⊎ ℕ
LM D (s₁ , s₂ , x , First) = Σ ℕ (λ n → x ≡ nth s₂ n)
LM D (s₁ , s₂ , x , Second) = Σ ℕ (λ n → x ≡ nth s₁ n)

-- Updating a configuration when a move is made, and sending that configuration to the opposite player
update-C : (p : Player) → (c : LC p) → (m : LM p c) → LC (op p)
update-C S (s₁ , s₂) (inj₁ x) = (del s₁ x) , s₂ , (nth s₁ x) , First
update-C S (s₁ , s₂) (inj₂ y) = s₁ , (del s₂ y) , (nth s₂ y) , Second
update-C D (s₁ , s₂ , x , First) (i , _) = s₁ , del s₂ i
update-C D (s₁ , s₂ , x , Second) (i , _) = del s₁ i , s₂

StreamEquivGame : Game LC LM
StreamEquivGame = record {
                δ = update-C
                }

-- Defining stream equivalence in a non-game way -------------------------------------

-- Definition of stream equivalence
infix 4 _≈_

data _≈_ : Stream ℕ → Stream ℕ → Set where
  step : ∀{m n : ℕ} (A : Stream ℕ) (B : Stream ℕ)
       → nth A m ≡ nth B n
       → ∞ (del A m ≈ del B n)
       → A ≈ B

-- If S never wins the game, the streams are equal -----
open Game StreamEquivGame
open ≡-Reasoning


w1 : { s₁ s₂ : Stream ℕ } { a b : ℕ } {r₁ : Run S (s₁ , s₂)}
           {r₂ : Run S (del s₁ a , del s₂ b)}
           { w : ¬ (S-Win S (s₁ , s₂) r₁) }
           → ¬ S-Win S (del s₁ a , del s₂ b) r₂
w1 {s₁} {s₂} {a} {b} {r₁} {r₂} {w} = ⊥-elim (w {!!})


w2 : { s₁ s₂ : Stream ℕ } { a : ℕ } {r₁ : Run S (s₁ , s₂)} {m : LM S (s₁ , s₂)}
           {r₂ :  Run D (del s₁ a , s₂ , nth s₁ a , First)}
           { w : ¬ (S-Win S (s₁ , s₂) r₁) }
           → ¬ S-Win D (del s₁ a , s₂ , nth s₁ a , First) r₂
w2 {s₁}{s₂}{a}{r₁}{m}{r₂}{w} = λ x → ⊥-elim (w {!!})

-- absolutely horrible!
second-step : { s₁ s₂ : Stream ℕ } { a : ℕ } { m : LM S (s₁ , s₂) }
         {r₁ : Run S (s₁ , s₂)}
         {r₂ : Run D (del s₁ a , s₂ , nth s₁ a , First)}
         { w : ¬ (S-Win S (s₁ , s₂) r₁)}
         → Σ ℕ (λ b → ( (nth s₁ a ≡ nth s₂ b) × Run S (del s₁ a , del s₂ b)))
second-step {s₁} {s₂} {a} {m} {r₁} {Game.end x} {w} = ⊥-elim (w2 {a = a}{m = m}{w = w} (Game.finished {p = D}{x = x}))
second-step {s₁} {s₂} {a} {m₂} {r₁} {Game.step m x} {w} = (proj₁ m) , ((proj₂ m) , (♭ x))

-- if D wins, then the streams must be equivalent
streamequiv-eq : { c : LC S } { r : Run S c } { w : ¬ (S-Win S c r) } → proj₁ c ≈ proj₂ c
streamequiv-eq {s₁ , s₂} {Game.end x} {w} = ⊥-elim (x (inj₁ zero))
streamequiv-eq {s₁ , s₂} {Game.step (inj₁ a) x} {w} =
               step s₁ s₂
                 (proj₁ (proj₂ (second-step {m = inj₁ a} {r₂ = ♭ x}{w = w})))
                 (♯ (streamequiv-eq {r = proj₂ (proj₂ (second-step {m = inj₁ a}{r₂ = ♭ x}{w = w}))}
                 ))
streamequiv-eq {s₁ , s₂} {Game.step (inj₂ b) x} {w} = {!!}
