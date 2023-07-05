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
{-    -- a run of the game
  data Run (p : Player) (c : C p) : Set where
    end : (¬ M p c) → Run p c
    step : (m : M p c) → ∞ (Run (op p) (δ p c m)) → Run p c-}

  data SWStrat : (p : Player) (c : C p) → Set where
    end : ∀ {c} → (¬ M D c) → SWStrat D c
    stepS : ∀{c} → (m : M S c) → SWStrat D (δ S c m) → SWStrat S c
    stepD : ∀{c} → ((m : M D c) → SWStrat S (δ D c m)) → SWStrat D c

  data DWStrat : (p : Player) (c : C p) → Set where
    end : ∀ {c} → (¬ M S c) → DWStrat S c
    stepD : ∀{c} → (m : M D c) → ∞ (DWStrat S (δ D c m)) → DWStrat D c
    stepS : ∀{c} → (∀ (m : M S c) → DWStrat D (δ S c m)) → DWStrat S c

  -- law of the excluded middle (if there is an S-winning strategy there can't be one for D)
  exclMid : (p : Player) (c : C p) → SWStrat p c → ¬ (DWStrat p c)
  exclMid .D c (end x) (stepD m x₁) = x m
  exclMid .S c (stepS m (end x)) (end x₁) = x₁ m
  exclMid .S c (stepS m (end x)) (stepS x₁) with x₁ m
  ... | stepD m₁ x₂ = x m₁
  exclMid .S c (stepS m (stepD x)) (end x₁) = x₁ m
  exclMid .S c (stepS m (stepD x)) (stepS x₁) with x₁ m
  ... | stepD m₁ x₂ = exclMid S ((δ D (δ S c m) m₁)) (x m₁) (♭ x₂)
  exclMid .D c (stepD x) (stepD m x₁) = exclMid S (δ D c m) (x m) (♭ x₁)

  -- other law of the excluded middle (if there is an D-winning strategy there can't be one for S)
  exclMid′ : (p : Player) (c : C p) → DWStrat p c → ¬ (SWStrat p c)
  exclMid′ = ?

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

record _≈'_ (A : Stream ℕ) (B : Stream ℕ) : Set where
  inductive
  field delA : ∀{n} → ∃ (λ m → nth A n ≡ nth B m × ∞ (del A n ≈' del B m))
  field delB : ∀{n} → ∃ (λ m → nth B n ≡ nth A m × ∞ (del A m ≈' del B n))

data _≈_ : Stream ℕ → Stream ℕ → Set where
  step : ∀{m n : ℕ} (A : Stream ℕ) (B : Stream ℕ)
       → nth A m ≡ nth B n
       → ∞ (del A m ≈ del B n)
       → A ≈ B

≈sym : ∀ {m n : Stream ℕ} → m ≈ n → n ≈ m
≈sym {m} {n} (step .m .n x x₁) = step n m (sym x) (♯ (≈sym (♭ x₁)))

open Game StreamEquivGame
open ≡-Reasoning


streamequiv-eq' : { c : LC S } ( w : DWStrat S c ) → proj₁ c ≈' proj₂ c
streamequiv-eq' {fst , snd} (Game.end x) = ⊥-elim (x (inj₁ zero))
streamequiv-eq' {fst , snd} (Game.stepS x) = record { delA = λ {n₁} → delA n₁ ; delB = λ {n₁} → delB n₁}
  where
    delA : (n : ℕ) → ∃ (λ m → nth fst n ≡ nth snd m × ∞ (del fst n ≈' del snd m))
    delA n with x (inj₁ n)
    ... | Game.stepD (m , p) x = m , p , ♯ streamequiv-eq' (♭ x)

    delB : (n : ℕ) → ∃ (λ m → nth snd n ≡ nth fst m × ∞ (del fst m ≈' del snd n))
    delB n with x (inj₂ n)
    ... | Game.stepD (m , p) x = m , p , ♯ streamequiv-eq' (♭ x)

open _≈'_

streamequiv-neq' : { c : LC S } ( w : SWStrat S c ) → ¬ (proj₁ c ≈' proj₂ c)
streamequiv-neq' {fst , snd} (Game.stepS (inj₁ x₁) (Game.end x)) x₂ = x (let n , p₁ , p₂ = delA x₂ {x₁} in (n , p₁))
streamequiv-neq' {fst , snd} (Game.stepS (inj₂ y) (Game.end x)) x₂ = x (let n , p₁ , p₂ = delB x₂ {y} in (n , p₁))
streamequiv-neq' {fst , snd} (Game.stepS (inj₁ x₁) (Game.stepD x)) x₂ with delA x₂ {x₁}
... | n , p₁ , p₂ = streamequiv-neq' (x (n , p₁)) (♭ p₂)
streamequiv-neq' {fst , snd} (Game.stepS (inj₂ y) (Game.stepD x)) x₂ with delB x₂ {y}
... | n , p₁ , p₂ = streamequiv-neq' (x (n , p₁)) (♭ p₂)


streamequiv-eq : { c : LC S } ( w : DWStrat S c ) → proj₁ c ≈ proj₂ c
streamequiv-eq {fst , snd} (Game.end x) = ⊥-elim (x (inj₁ zero))
streamequiv-eq {fst , snd} (Game.stepS x) with x (inj₁ zero)
... | Game.stepD (n , p) x₁ = step fst snd p (♯ streamequiv-eq (♭ x₁))

{--- If a winning strategy exists for D, then the streams must be equivalent
streamequiv-eq : { c : LC S } { r : Run S c } ( w : DWStrat S c ) → proj₁ c ≈ proj₂ c
streamequiv-eq {fst , snd} {Game.end x} w = ⊥-elim (x (inj₁ zero))
streamequiv-eq {c} {Game.step (inj₁ n) x} (Game.end x₂) = ⊥-elim (x₂ (inj₁ zero))
streamequiv-eq {fst , snd} {Game.step (inj₁ n) x} (Game.stepS x₂) with ♭ x in eq
... | Game.end x′ with (x₂ (inj₁ n)) in hq
... | Game.stepD m y = ⊥-elim (x′ m)
streamequiv-eq {fst , snd} {Game.step (inj₁ n) x} (Game.stepS x₂) | Game.step m x′ with (x₂ (inj₁ n)) in hq
streamequiv-eq {fst , snd} {Game.step (inj₁ n) x} (Game.stepS x₂) | Game.step m x′ | Game.stepD m1 y
   = step fst snd (proj₂ m) (♯ (streamequiv-eq {r = ♭ x′} {!!}))
streamequiv-eq {c} {Game.step (inj₂ n) x} (Game.end x₁) = ⊥-elim (x₁ (inj₁ zero))
streamequiv-eq {c} {Game.step (inj₂ n) x} (Game.stepS x₁) with ♭ x in eq
... | Game.end x′ with (x₁ (inj₂ n)) in hq
... | Game.stepD m y = ⊥-elim (x′ m)
streamequiv-eq {c} {Game.step (inj₂ n) x} (Game.stepS x₁) | Game.step m x′ with (x₁ (inj₂ n)) in hq
... | Game.stepD m y = {!!}


--  If a winning strategy exists for S, then the streams must not be equivalent
streamequiv-neq :  { c : LC S } { r : Run S c } ( w : SWStrat S c ) → ¬ proj₁ c ≈ proj₂ c
streamequiv-neq {fst , snd} {Game.end x} w = ⊥-elim (x (inj₁ zero))
streamequiv-neq {fst , snd} {Game.step (inj₁ y) x} (Game.stepS m (Game.end x₁)) with ♭ x in eq
... | Game.end x′ = λ x₂ → {!x₁!}
... | Game.step m₂ x′ = {!!}
streamequiv-neq {fst , snd} {Game.step (inj₁ y) x} (Game.stepS m (Game.stepD x₁)) = {!!}
streamequiv-neq {fst , snd} {Game.step (inj₂ y) x} w = {!!}
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

-}
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
