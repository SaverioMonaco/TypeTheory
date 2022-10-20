-- basic logical tautologies regarding conjunctions

-- Examples_
-- > A ∧ B is equivalent to B ∧ A
-- > ¬(A ∨ B) is equivalent to ¬A ∧ ¬B

-- "A ∧ B" should be the type of witnesses that A is
-- inhabited and that B is inhabited
-- In Type Theory, ∧ is actually ×, here we do 
-- not deal with booleans specifically, but with 
-- types and mainly witnesses.
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B 
  right : B → A ⊎ B 

data ⊥ : Set where:

¬ : Set → Set 
¬ X = X → ⊥

-- 1: A ∧ B is equivalent to B ∧ A
∧-commutative : {A B : Set} → A ∧ B → B ∧ A 
∧-commutative (x , y) = (y, x)

-- 2: ¬(A ∨ B) is equivalent to ¬A ∧ ¬B
de-morgan₁ : {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
--        we use directly A and B in the definition
--        of g, we need them explicit
--         |   | 
de-morgan₁ {A} {B} f = (g , (λ y →  f (right y)))
  where 
  g : ¬ A
  g x = f (left x)

-- 3: If A is false AND B is false then...
de-morgan₂ : {A B : Set} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
de morgan₂ = ?

de-morgan₃ : {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
de-morgan₃ = ?

de-morgan₄ : {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
de-morgan₄ = ? -- this hole cannot be filled

-- law of exluded middle (LEM): A ∨ ¬A
-- For any given type, it is either empty or inhabited
type-of-witnesses-of-lem = {A : Set} → A ⊎ (¬ A)

this-hole-cannot-be-filled : type-of-witnesses-of-lem 
this-hole-cannot-be-filled = ? 

postulate
  -- we just say this is true without proving it 
  oracle : type-of-witnesses-of-lem 
  -- we can even create constant of the empty type
  lol    : ⊥
  -- we can even say 1 = 0 and so on, but we must be
  -- careful with what we postulate

now-it-can-be-filled : type-of-witnesses-of-lem 
now-it-can-be-filled = oracle

-- "Dec A" is the type of witnesses that A is decidable:
-- (more precisely, it is the type of witnesses
--  that A is inhabited or empty)
data Dec (A : Set) : Set where 
  yes :   A → Dec A 
  no  : ¬ A → Dec A 

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ 

data Positive : ℕ → Set where
  succs-are-positive : (a : ℕ) → Positive (succ a)

positivity-is-decidable : (a : ℕ) → Dec (Positive a)
positivity-is-decidable zero      = no  (λ ())
positivity-is-decidable (succ a)  = yes (succs-are-positive a) 


-- "Every set of natural numbers contains a mininmum"
-- this is false because of empty set

-- "Every inhabited set of natural numbers contains a mininmum"
-- this is true
-- We can picture a function P : ℕ → Set as a set of natural numbers
-- namely, the number n belongs to this set if and only if P n is
-- inhabited, hence P n is the type of witnesses that n belongs to the set.
data _≤_ (P : ℕ → Set) → (a₀ : ℕ) → P a₀ → ℕ 
  -- fill this in

minimum : (P : ℕ → Set) → (a₀ : ℕ) → P a₀ → ℕ
minimum = ?
lemma-minimum-is-computed-correctly
  : (P : ℕ → Set) → (a₀ : ℕ) → (p : P a₀)
  → (n : ℕ) → P n → a₀ ≤ n 
lemma-minimum-is-computed-correctly = ?