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

  data SWStrat : (p : Player) (c : C p) → Set where
    end : ∀ {c} → (¬ M D c) → SWStrat D c
    stepS : ∀{c} → (m : M S c) → SWStrat D (δ S c m) → SWStrat S c
    stepD : ∀{c} → ((m : M D c) → SWStrat S (δ D c m)) → SWStrat D c

  data DWStrat : (p : Player) (c : C p) → Set where
    end : ∀ {c} → (¬ M S c) → DWStrat S c
    stepD : ∀{c} → (m : M D c) → ∞ (DWStrat S (δ D c m)) → DWStrat D c
    stepS : ∀{c} → (∀ (m : M S c) → DWStrat D (δ S c m)) → DWStrat S c

    -- winning conditions for S (omitting D winning because D-Win = ¬ S-Win)
  {-data S-Win : (p : Player) (c : C p) (r : Run p c) → Set where
    finished : ∀{c}{x} → S-Win D c (end x)
    unfinished : ∀{p}{c}{m}{r}
         → S-Win (op p) (δ p c m) (♭ r)
         → S-Win p c (step m r)-}

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

≈sym : ∀ {m n : Stream ℕ} → m ≈ n → n ≈ m
≈sym {m} {n} (step .m .n x x₁) = step n m (sym x) (♯ (≈sym (♭ x₁)))

open Game StreamEquivGame
open ≡-Reasoning

-- If there is a D-win strategy for the game, then there must exist some valid D-move after any S-move

prf : { fst snd : Stream ℕ } { n : ℕ }
    {m : Σ ℕ (λ n₁ → nth fst n ≡ nth snd n₁)} (m₁ : ℕ ⊎ ℕ)
    → m₁ ≡ inj₁ n
    → DWStrat D (update-C S (fst , snd) m₁)
    → DWStrat S (del fst n , del snd (proj₁ m))
prf {fst}{snd} m₁ p (Game.stepD m x) = {!cong₂ (♭ x) ? ?!}
--subst (λ x → (DWStrat S (update-C D (update-C S (fst , snd) x) _))) p (♭ x)

-- If a winning strategy exists for D, then the streams must be equivalent
streamequiv-eq : { c : LC S } { r : Run S c } ( w : DWStrat S c ) → proj₁ c ≈ proj₂ c
streamequiv-eq {fst , snd} {Game.end x} w = ⊥-elim (x (inj₁ zero))
streamequiv-eq {c} {Game.step (inj₁ n) x} (Game.end x₂) with ♭ x in eq
... | Game.end x′ = ⊥-elim (x₂ (inj₁ zero))
... | Game.step m x′ = ⊥-elim (x₂ (inj₁ zero))
streamequiv-eq {fst , snd} {Game.step (inj₁ n) x} w@(Game.stepS x₂) with ♭ x in eq
... | Game.end x′ with (x₂ (inj₁ n)) in hq
... | Game.stepD m y = ⊥-elim (x′ m)
streamequiv-eq {fst , snd} {Game.step (inj₁ n) x} w@(Game.stepS x₂) | Game.step m x′ with (x₂ (inj₁ n)) in hq
... | Game.stepD m y = step fst snd (proj₂ m) (♯ (streamequiv-eq ?))
streamequiv-eq {c} {Game.step (inj₂ n) x} w = {!!}


{-
-- if D wins, then the streams must be equivalent
streamequiv-eq : { c : LC S } { r : Run S c } ( w : ¬ (S-Win S c r) ) → proj₁ c ≈ proj₂ c
streamequiv-eq {s₁ , s₂} {Game.end x} w = ⊥-elim (x (inj₁ zero))
streamequiv-eq {s₁ , s₂} {Game.step (inj₁ a) x} w with ♭ x in eq
... | Game.step m x′ = step s₁ s₂ (proj₂ m)
                (♯ streamequiv-eq {r = ♭ x′} λ y →
                                  ⊥-elim (w (Game.unfinished (subst (λ □ → S-Win D _ □) (sym eq) (Game.unfinished y)))))
... | Game.end x′ = ⊥-elim (w (Game.unfinished (subst (λ □ → S-Win D _ □) (sym eq) Game.finished) ))
streamequiv-eq {s₁ , s₂} {Game.step (inj₂ a) x} w with ♭ x in eq
... | Game.step m x′ = step s₁ s₂ (sym (proj₂ m))
                (♯ streamequiv-eq {r = ♭ x′} λ y →
                                  ⊥-elim (w (Game.unfinished (subst (λ □ → S-Win D _ □) (sym eq) (Game.unfinished y)))))
... | Game.end x′ = ⊥-elim (w (Game.unfinished (subst (λ □ → S-Win D _ □) (sym eq) (Game.finished))))

lemma′ : ∀{m n : ℕ} {A B : Stream ℕ}
       → A ≈ B
       → nth A m ≡ nth B n
       → del A m ≈ del B n
lemma′ {m₁}{n₁} (step {m₂}{n₂} _ _ x x₁) q with m₁ ≟ m₂ | n₁ ≟ n₂
lemma′ {m₁}{n₁} (step {m₂}{n₂} _ _ x x₁) q | yes refl | yes refl = ♭ x₁
lemma′ {m₁}{n₁} (step {m₂}{n₂} _ _ x x₁) q | yes refl | no z = {!!}
lemma′ {m₁}{n₁} (step {m₂}{n₂} _ _ x x₁) q | no y  | yes refl = {!!}
lemma′ {m₁}{n₁}{A}{B} e@(step {m₂}{n₂} _ _ x x₁) q | no y  | no z = {!!}

lemma : ∀{m n : ℕ} {A B : Stream ℕ}
       → nth A m ≡ nth B n
       → ¬ (del A m ≈ del B n)
       → ¬ (A ≈ B)
lemma p q e = ⊥-elim (q (lemma′ e p))

prf′ : { c : LC S } { y : ℕ } → proj₁ c ≈ proj₂ c
     → Σ ℕ (λ n → nth (proj₂ c) y ≡ nth (proj₁ c) n)
prf′ {c} {y} (step {m}{n} .(proj₁ c) .(proj₂ c) x x₁) = {!!}


prf : { c : LC S } { x : ℕ } → proj₁ c ≈ proj₂ c
     → Σ ℕ (λ n → nth (proj₁ c) x ≡ nth (proj₂ c) n)
prf {c}{x} p = {!!}

-- if S wins, then the streams must be not-equivalent
streamequiv-neq : { c : LC S } { r : Run S c } ( w : S-Win S c r ) → ¬ (proj₁ c ≈ proj₂ c)
streamequiv-neq' : {c : LC S }{ m : LM S c } { r : Run D (δ S c m) } ( w : S-Win D (δ S c m) r) → ¬ (proj₁ c ≈ proj₂ c)
streamequiv-neq (Game.unfinished w) = streamequiv-neq' w
streamequiv-neq' {c} {inj₁ x₂} {Game.end x} Game.finished p with p in eq
... | y = ⊥-elim (x (prf y))
streamequiv-neq' {c} {inj₂ x₂} {Game.end x} Game.finished p with p in eq
... | y = ⊥-elim (x (prf′ y))
streamequiv-neq' {fst , snd} {inj₁ x} {Game.step m _} (Game.unfinished w) = lemma (proj₂ m) (streamequiv-neq w)
streamequiv-neq' {fst , snd} {inj₂ y} {(step m _)} (Game.unfinished w) = lemma (sym (proj₂ m)) (streamequiv-neq w)
-}
