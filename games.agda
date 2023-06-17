module games where
open import Data.Nat using (ℕ; _≟_; zero; suc; s≤s; _<_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List
open import Agda.Builtin.Bool
open import Data.Product
open import Data.Fin hiding (_≟_)
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty

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
    step : (m : M p c) → Run (op p) (δ p c m) → Run p c
    -- winning conditions
  win : { p : Player } { c : C p } → Run p c → Player
  win {p} (end x) = op p
  win (step m r) = win r

-- >>> List equivalence game! <<<
-- A game configuration in a list equivalence game
LC : Player → Set
LC S = (List ℕ × List ℕ)
LC D = (List ℕ × List ℕ × ℕ × Two)

-- deletes the nth element of a list
del : (l : List ℕ) → Fin (length l) → List ℕ
del (x ∷ l) zero = l
del (x ∷ l) (suc i) = x ∷ del l i

-- gets the nth element of a list
nth : (l : List ℕ) → Fin (length l) → ℕ
nth (x ∷ l) zero = x
nth (x ∷ l) (suc i) = nth l i

-- gets you the right list at D's turn based on S's choice
op-list : LC D → Two → List ℕ
op-list a First = proj₁ (proj₂ a)
op-list a Second = proj₁ a

-- A move in a list equivalence game
LM : (p : Player) → (c : LC p) → Set
LM S (l₁ , l₂) = Fin (length l₁) ⊎ Fin (length l₂)
LM D (l₁ , l₂ , x , First) = Σ (Fin (length l₂)) (λ f → nth l₂ f ≡ x)
LM D (l₁ , l₂ , x , Second) = Σ (Fin (length l₁)) (λ f → nth l₁ f ≡ x)

-- Updating a configuration when a move is made, and sending that configuration to the opposite player
update-C : (p : Player) → (c : LC p) → (m : LM p c) → LC (op p)
update-C S (l₁ , l₂) (inj₁ i) = (del l₁ i) , l₂ , nth l₁ i , First
update-C S (l₁ , l₂) (inj₂ i) = l₁ , (del l₂ i) , nth l₂ i , Second
update-C D (l₁ , l₂ , x , First) (i , _) = (l₁ , del l₂ i)
update-C D (l₁ , l₂ , x , Second) (i , _) = (del l₁ i , l₂)

-- The game
ListEquivGame : Game LC LM
ListEquivGame = record {
              δ = update-C
              }

open Game ListEquivGame

-- De Morgan's
demorgan : {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
demorgan p = (λ x → p (inj₁ x)) , λ x → p (inj₂ x)

-- not (Fin l) means l ≡ zero
finzero : { l : ℕ } → ¬ Fin l → l ≡ zero
finzero {zero} e = refl
finzero {suc l} e = ⊥-elim (e zero)

open ≡-Reasoning

-- some sort of proof for some properties
proof-del : ∀{x}{f}{n} → length x ≡ suc n → length (del x f) ≡ n
proof-del {x ∷ x₁} {zero} p = suc-injective p
proof-del {x ∷ []} {suc ()} {zero} p
proof-del {x ∷ x₁ ∷ x₂} {suc f} {zero} ()
proof-del {x ∷ x₁} {suc f} {suc n} p
  = begin
      length (x ∷ del x₁ f) ≡⟨⟩
      suc (length (del x₁ f)) ≡⟨ cong suc (proof-del {x₁} {f} {n} (suc-injective p)) ⟩
      suc n ∎

-- length of a list after del is the original length - 1
proof-del' : ∀{x}{f} →  suc (length (del x f)) ≡ length x
proof-del' {x ∷ x₁} {f} = cong suc (proof-del {x ∷ x₁}{f} (cong suc refl))

-- if two lists are of equal length after deleting an element, then they were the same length originally.
proof0 : ∀{x y}{f₁}{f₂} → length (del x f₁) ≡ length (del y f₂)
       → length x ≡ length y
proof0 {x}{y}{f₁}{f₂} e = begin
  length x                ≡⟨ sym (proof-del' {x}{f₁}) ⟩
  suc (length (del x f₁)) ≡⟨ cong suc e ⟩
  suc (length (del y f₂)) ≡⟨ proof-del' {y}{f₂} ⟩
  length y ∎

-- something about lengths of lists after two updates in a listequiv game
proof1 : { c : LC S }( m : LM S c )( m₁ : LM D (update-C S c m)) →
       length (proj₁ (update-C D (update-C S c m) m₁)) ≡ length (proj₂ (update-C D (update-C S c m) m₁))
     → length (proj₁ c) ≡ length (proj₂ c)
proof1 {c}(inj₁ x) (f , _) p = proof0 {proj₁ c}{proj₂ c}{x}{f} p
proof1 {c}(inj₂ y) (f , _) p = proof0 {proj₁ c}{proj₂ c}{f}{y} p

-- >>> in a list equivalence game, if D wins then the lists must be of equal length. <<<
listequiv-length : { c : LC S } → (r : Run S c) → win r ≡ D → length (proj₁ c) ≡ length (proj₂ c)
listequiv-length {c} (Game.end x) p
  = let (p₁ , p₂) = demorgan x
     in begin
       length (proj₁ c) ≡⟨ finzero p₁ ⟩
       zero             ≡⟨ sym (finzero p₂) ⟩
       length (proj₂ c) ∎
listequiv-length (Game.step m (Game.step m₁ r)) p = let x = listequiv-length r p in proof1 m m₁ x

-- gives you the number of occurances of an element in a list
count : List ℕ → ℕ → ℕ
count [] n = zero
count (x ∷ xs) n with x ≟ n
... | yes _ = suc (count xs n)
... | no  _ = count xs n

-- list equality (we don't care about the order of the elements)
list-eq : List ℕ → List ℕ → Set
list-eq a b = ∀ n → count a n ≡ count b n

-- whether a list contains a given element
contains :  (x : ℕ) (l : List ℕ) → Set
contains x l = Σ (Fin (length l)) (λ f → nth l f ≡ x)

-- if the number of occurances of an element is zero, the list does not contain this element
prf : ∀{x}{l} → count l x ≡ zero → ¬ (contains x l)
prf {x} {x₁ ∷ l} c (f , a) with x₁ ≟ x
prf {x} {x₁ ∷ l} () (f , a) | yes y
prf {x} {x₁ ∷ l} c (zero , a) | no n = n a
prf {x} {x₁ ∷ l} c (suc f , a) | no n = prf {x}{l} c (f , a)

-- if the length of a list is zero, then the count of any element in that list is also zero
zero-count : { n : ℕ } { l : List ℕ } → length l ≡ zero → count l n ≡ zero
zero-count {n} {[]} p = refl

-- inserting an element into the beginning of a list (preserving list-eq equality but not element order)
insert : (l : List ℕ) → (a : ℕ) → List ℕ
insert l a = a ∷ l

-- reflexivity for list equality
list-eq-refl : ∀{a} → list-eq a a
list-eq-refl = λ n → refl

-- transistivity for list equality
list-eq-trans : ∀{l₁ l₂ l₃} → list-eq l₁ l₂ → list-eq l₂ l₃ → list-eq l₁ l₃
list-eq-trans {l₁} {l₂} {l₃} a b = λ n → begin
              count l₁ n ≡⟨ a n ⟩
              count l₂ n ≡⟨ b n ⟩
              count l₃ n ∎

-- symmetry for list equality
list-eq-sym : ∀{a b} → list-eq a b → list-eq b a
list-eq-sym {a}{b} p = λ n → begin
            count b n ≡⟨ sym (p n) ⟩
            count a n ∎

-- if two lists are equal, then they have the same count for all elements (seems kinda redundant I know)
list-subst : ∀{a b}{n} → list-eq a b → count a n ≡ count b n
list-subst {a}{b}{n} = λ x → begin
           count a n ≡⟨ x n ⟩
           count b n ∎

-- the number of a given element decreases if you delete one of them from a list, part 1
count-del : { l : List ℕ } { f : Fin (length l) } → count l (nth l f) ≡ suc (count (del l f) (nth l f))
count-del {x ∷ l} {zero} with x ≟ x
count-del {x ∷ l} {zero} | yes _ = refl
count-del {x ∷ l} {zero} | no p =  ⊥-elim (p refl)
count-del {x ∷ l} {suc f} with x ≟ nth l f
count-del {x ∷ l} {suc f} | yes _ = cong suc (count-del {l = l})
count-del {x ∷ l} {suc f} | no _ = count-del {l = l}

-- the number of a given element decreases if you delete one of them from a list, part 2
count-insert : ∀{l}{f}{n} → n ≡ nth l f →  count l n ≡ suc (count (del l f) n)
count-insert {l}{f}{n} p = begin
             count l n ≡⟨ cong (count l) p ⟩
             count l (nth l f) ≡⟨ count-del {l = l} {f = f} ⟩
             suc (count (del l f) (nth l f)) ≡⟨ cong suc (cong (count (del l f)) (sym p)) ⟩
             suc (count (del l f) n) ∎

-- if two lists are (propositionally) equal, then the counts are the same for all elements
count-subst : { a b : List ℕ } { n : ℕ } → a ≡ b → count a n ≡ count b n
count-subst p = cong₂ count p refl

-- the count of an element remains the same if I delete a different element from a list without changing anything else
count-del-neq : { l : List ℕ } { f : Fin (length l)} { n : ℕ } → ¬ nth l f ≡ n → count l n ≡ count (del l f) n
count-del-neq {x ∷ l} {zero} {n} p with x ≟ n
count-del-neq {x ∷ l} {zero} {n} p | yes y = ⊥-elim (p y)
count-del-neq {x ∷ l} {zero} {n} p | no z = refl
count-del-neq {x ∷ l} {suc f} {n} p with x ≟ n
count-del-neq {x ∷ l} {suc f} {n} p | yes y = cong suc (count-del-neq {l = l} p)
count-del-neq {x ∷ l} {suc f} {n} p | no z = count-del-neq {l = l} p

-- deleting then inserting the same element gives a list equivalent to the initial list
insert-del-identity : ∀{l}{f} → list-eq l (insert (del l f) (nth l f))
insert-del-identity {l}{f} n with nth l f ≟ n
insert-del-identity {l}{f} n | yes y = count-insert {l = l}{f = f} (sym y)
insert-del-identity {l}{f} n | no p = count-del-neq {l = l} p

-- inserting the same element into two equivalent lists retains equality, part 1
insert-eq-4 :  { l : List ℕ } { e₁ e₂ : ℕ } → e₁ ≡ e₂ → list-eq (insert l e₁) (insert l e₂)
insert-eq-4 {l₁}{e₁}{e₂} a n with e₁ ≟ n
insert-eq-4 {l₁}{e₁}{e₂} a n | yes y with e₂ ≟ n
insert-eq-4 a n | yes y | yes z = refl
insert-eq-4 {l₁}{e₁}{e₂} a n | yes y | no z = ⊥-elim (z (trans (sym a) y))
insert-eq-4 {l₁}{e₁}{e₂} a n | no p with e₂ ≟ n
insert-eq-4 {l₁}{e₁}{e₂} a n | no p | yes z = ⊥-elim (p (trans a z))
insert-eq-4 {l₁}{e₁}{e₂} a n | no p | no z = refl

-- inserting the same element into two equivalent lists retains equality, part 2
insert-eq-3 :  { l₁ l₂ : List ℕ } { e : ℕ } → list-eq l₁ l₂ → list-eq (insert l₁ e) (insert l₂ e)
insert-eq-3 {l₁}{l₂}{e} a n with e ≟ n
insert-eq-3 {l₁}{l₂}{e} a n | yes y = cong suc (a n)
insert-eq-3 {l₁}{l₂}{e} a n | no p = a n

-- inserting the same element into two equivalent lists retains equality, part 3
insert-eq-2 : { l₁ l₂ : List ℕ } { e₁ e₂ : ℕ } → e₁ ≡ e₂ → list-eq l₁ l₂ → list-eq (insert l₁ e₁) (insert l₂ e₂)
insert-eq-2 {l₁}{l₂}{e₁}{e₂} a b =
            -- we want to show that insert l₁ e₁ = insert l₂ e₁ = insert l₂ e₂
            list-eq-trans {l₁ = insert l₁ e₁}{l₂ = insert l₂ e₁}{l₃ = insert l₂ e₂}
            -- this part shows insert l₁ e₁ = insert l₂ e₁
            (insert-eq-3 {l₁ = l₁} {l₂ = l₂} {e = e₁} b)
            -- this part shows insert l₂ e₁ = insert l₂ e₂
            (insert-eq-4 {l = l₂} {e₁ = e₁} {e₂ = e₂} a)

-- transistivity of list equality but with a different type signature
insert-eq : { l₁ l₂ l₃ : List ℕ } { e₁ e₂ : ℕ } → e₁ ≡ e₂ → list-eq l₁ (insert l₂ e₁)  → list-eq l₂ l₃ → list-eq l₁ (insert l₃ e₂)
insert-eq {l₁}{l₂}{l₃}{e₁}{e₂} a b c =
          list-eq-trans {l₁ = l₁} {l₂ = insert l₂ e₁} {l₃ = insert l₃ e₂} b (insert-eq-2 a c)

-- if I delete something then put the same thing back in, the list should stay the same
proof4 : ( l₁ l₂ : List ℕ ) ( f : Fin (length l₁) ) → list-eq l₂ (del l₁ f) → list-eq l₁ (insert l₂ (nth l₁ f))
proof4 l₁ l₂ f p =
      -- Goal :l₁ = insert (del l₁ f) (nth l₁ f) = (insert l₂ (nth l₁ f))
      list-eq-trans {l₁ = l₁} {l₂ = insert (del l₁ f) (nth l₁ f)} {l₃ = insert l₂ (nth l₁ f)}
      -- l₁ = insert (del l₁ f) (nth l₁ f)
      (insert-del-identity {l = l₁} {f = f})
      -- insert (del l₁ f) (nth l₁ f) = (insert l₂ (nth l₁ f))
      (insert-eq-3 {l₁ = del l₁ f}{l₂ = l₂}{e = nth l₁ f} (list-eq-sym {a = l₂}{b = del l₁ f} p))

-- if two lists are equal after deleting the same element from each, they were equal originally
new-elem-eq :{ l₁ l₂ : List ℕ } ( f₁ : Fin (length l₁) ) (f₂ : Fin (length l₂)) → list-eq (del l₁ f₁) (del l₂ f₂) →
            nth l₁ f₁ ≡ nth l₂ f₂ → list-eq (insert (del l₁ f₁) (nth l₁ f₁)) (insert (del l₂ f₂) (nth l₂ f₂))
new-elem-eq {l₁}{l₂} f₁ f₂ p₁ p₂ n =
            -- z says that list-eq l₁ (insert (del l₁ f₁) (nth l₁ f₁))
            let z = (proof4 l₁ (del l₁ f₁) f₁ λ n₁ → refl) in list-eq-trans
            {l₁ = insert (del l₁ f₁) (nth l₁ f₁)} {l₂ = l₁} {l₃ = (insert (del l₂ f₂) (nth l₂ f₂))} (
            -- list-eq (insert (del l₁ f₁) (nth l₁ f₁)) l₁
            list-eq-sym {a = l₁} {b = insert (del l₁ f₁) (nth l₁ f₁)} z)
            -- list-eq l₁ (insert (del l₂ f₂) (nth l₂ f₂))
            (insert-eq {l₁ = l₁} {l₂ = del l₁ f₁} {l₃ = del l₂ f₂} {e₁ = nth l₁ f₁} {e₂ = nth l₂ f₂} p₂ z p₁) n

-- if two lists are equal after deleting the same element from each, they were equal originally, part 2 (without inserts)
proof3 : { l₁ l₂ : List ℕ } { f₁ : Fin (length l₁) } { f₂ : Fin (length l₂) } →
       list-eq (del l₁ f₁) (del l₂ f₂) → nth l₁ f₁ ≡ nth l₂ f₂ → list-eq l₁ l₂
proof3 {l₁}{l₂}{f₁}{f₂} a b = list-eq-trans {l₁ = l₁} {l₂ =  insert (del l₂ f₂) (nth l₂ f₂)} {l₃ = l₂}
       -- this gives list-eq l₁ (insert (del l₂ f₂) (nth l₂ f₂))
       (list-eq-trans {l₁ = l₁} {l₂ = insert (del l₁ f₁) (nth l₁ f₁)} {l₃ = insert (del l₂ f₂) (nth l₂ f₂)}
       (proof4 l₁ (del l₁ f₁) f₁ λ n → refl)
       (new-elem-eq {l₁ = l₁} {l₂ = l₂} f₁ f₂ a b))
       -- this gives list-eq (insert (del l₂ f₂) (nth l₂ f₂)) l₂
       (list-eq-sym {a = l₂} {b = insert (del l₂ f₂) (nth l₂ f₂)} (proof4 l₂ (del l₂ f₂) f₂ (λ n → refl)))

-- what happens after two steps in the game
proof2 : { c : LC S } { m₁ : LM S c } { m₂ : LM D (update-C S c m₁) } →
       list-eq (proj₁ (update-C D (update-C S c m₁) m₂)) (proj₂ (update-C D (update-C S c m₁) m₂)) →
       list-eq (proj₁ c) (proj₂ c)
proof2 {l₁ , l₂} {inj₁ x} { (f , p) } a n = proof3 {l₁ = l₁} {l₂ = l₂} a (sym p) n
proof2 {l₁ , l₂} {inj₂ y} { (f , p) } a n = proof3 {l₁ = l₁} {l₂ = l₂} a p n

-- in a list equivalence game, if D wins then the lists are equal
listequiv-eq : { c : LC S } → (r : Run S c) → win r ≡ D → list-eq (proj₁ c) (proj₂ c)
listequiv-eq {l₁ , l₂} (Game.end x) a n
  = let (p₁ , p₂) = demorgan x
     in begin
       count l₁ n ≡⟨ zero-count {n = n} {l = l₁} (finzero p₁) ⟩
       zero       ≡⟨ sym (zero-count {n = n} {l = l₂} (finzero p₂)) ⟩
       count l₂ n ∎
listequiv-eq (Game.step m₁ (Game.step m₂ r)) a = let x = listequiv-eq r a in proof2 {m₁ = m₁} {m₂ = m₂} x

nat-pred : ∀( n : ℕ ) → ℕ
nat-pred zero = zero
nat-pred (suc n) = n

proof6 : ∀{ l₁ l₂ : List ℕ } { x : Fin (length l₁) } → list-eq l₁ l₂ → Σ (Fin (length l₂)) (λ f → nth l₂ f ≡ nth l₁ x)
proof6 {l₁}{l₂}{x} n = {!!}

proof5 : { l₁ l₂ : List ℕ } { x : Fin (length l₁) } → ¬ Σ (Fin (length l₂)) (λ f → nth l₂ f ≡ nth l₁ x) → ¬ (list-eq l₁ l₂)
proof5 {l₁} {l₂} {x} a p = a (proof6 {l₁ = l₁}{l₂ = l₂} p)

neq-trans : ∀{ a b n : ℕ } → a ≡ b → ¬ a ≡ n → ¬ b ≡ n
neq-trans p q x = ⊥-elim (q (trans p x))

list-eq-del : {l₁ l₂ : List ℕ } {x : Fin (length l₁)} {f : Fin (length l₂)} →
            list-eq l₁ l₂ → nth l₂ f ≡ nth l₁ x → list-eq (del l₁ x) (del l₂ f)
list-eq-del {l₁}{l₂}{x}{f} a b n with (nth l₁ x) ≟ n
list-eq-del {l₁}{l₂}{x}{f} a b n | yes y = begin
            count (del l₁ x) n ≡⟨ cong nat-pred (sym (count-insert {l = l₁} (sym y))) ⟩
            nat-pred (count l₁ n) ≡⟨ cong nat-pred (a n) ⟩
            nat-pred (count l₂ n) ≡⟨ cong nat-pred (count-insert {l = l₂} (trans (sym y) (sym b))) ⟩
            count (del l₂ f) n ∎
list-eq-del {l₁}{l₂}{x}{f} a b n | no p = begin
            count (del l₁ x) n ≡⟨ sym (count-del-neq {l = l₁} p) ⟩
            count l₁ n ≡⟨ a n ⟩
            count l₂ n ≡⟨ count-del-neq {l = l₂} (neq-trans (sym b) p) ⟩
            count (del l₂ f) n ∎

proof7 : { c : LC S } { m₁ : LM S c } { m₂ : LM D (update-C S c m₁) } → list-eq (proj₁ c) (proj₂ c) →
       list-eq (proj₁ (update-C D (update-C S c m₁) m₂)) (proj₂ (update-C D (update-C S c m₁) m₂))
proof7 {l₁ , l₂} {inj₁ x} {f , p} a = list-eq-del {l₁ = l₁} {l₂ = l₂} a p
proof7 {l₁ , l₂} {inj₂ y} {f , p} a = list-eq-del {l₁ = l₁} {l₂ = l₂} a (sym p)

-- in a list equivalence game, if S wins then the lists are not equal
listequiv-neq : { c : LC S } → (r : Run S c) → win r ≡ S → ¬ (list-eq (proj₁ c) (proj₂ c))
listequiv-neq {l₁ , l₂} (Game.step (inj₁ x₁) (Game.end x)) a n = proof5 {l₁ = l₁} {l₂ = l₂} x n
listequiv-neq {l₁ , l₂} (Game.step (inj₂ y) (Game.end x)) a n = proof5 {l₁ = l₂} {l₂ = l₁} x (list-eq-sym {a = l₁} {b = l₂} n)
listequiv-neq {c} (Game.step m₁ (Game.step m₂ r)) a n = listequiv-neq r a (proof7 {c = c} {m₁ = m₁} n)


{--- if l₁ contains an element not in l₂, l₁ is not equal to l₂
proof20 : { l₁ l₂ : List ℕ } { x : Fin (length l₁) } → ¬ Σ (Fin (length l₂)) (λ f → nth l₂ f ≡ nth l₁ x) → ¬ (l₁ ≡ l₂)
proof20 {l₁} {.l₁} {x} a refl = a (x , refl)

proof30 : { c : LC S } { m : LM S c } { m₁ : LM D (update-C S c m) } →
  ¬ (proj₁ (update-C D (update-C S c m) m₁) ≡ proj₂ (update-C D (update-C S c m) m₁)) →
  ¬ (proj₁ c ≡ proj₂ c)
proof30 {l₁ , l₂} {inj₁ x} {f , b} a = {!!}
proof30 {fst , snd₁} {inj₂ y} {fst₁ , snd₂} a = {!!}

-- >>> in a list equivalence game, if S wins then the lists must be inequal. <<<
listequiv-eq0 : { c : LC S } {r : Run S c } → win r ≡ S → ¬ (proj₁ c ≡ proj₂ c)
listequiv-eq0 {c} {Game.step (inj₁ x₁) (Game.end x)} a = proof20 x
listequiv-eq0 {c} {Game.step (inj₂ y) (Game.end x)} a = λ p → proof20 x (sym p)
listequiv-eq0 {c} {Game.step m (Game.step m₁ r)} a = let d = listequiv-eq0 {r = r} a in {!!} -}
