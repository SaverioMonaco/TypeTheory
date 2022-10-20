#### Basic logical tautologies regarding conjunctions

Examples:
- A ∧ B is equivalent to B ∧ A
- ¬(A ∨ B) is equivalent to ¬A ∧ ¬B

Let us start with the usual definitions
```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ 

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B 
  right : B → A ⊎ B 

data ⊥ : Set where:

¬ : Set → Set 
¬ X = X → ⊥
```
In Agda, AND symbol is actually `×` instead of `∧`, this is because we are not dealing specifically with booleans but with types and mainly we can think about witnesses that a given type is inhabited.
```agda
-- 1: A ∧ B is equivalent to B ∧ A
∧-commutative : {A B : Set} → A ∧ B → B ∧ A 
∧-commutative (x , y) = (y, x)
```

```agda
-- 2: ¬(A ∨ B) is equivalent to ¬A ∧ ¬B
de-morgan₁ : {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
--        we use directly A and B in the definition
--        of g, we need them explicit
--         |   | 
de-morgan₁ {A} {B} f = (g , (λ y →  f (right y)))
  where 
  g : ¬ A
  g x = f (left x)
```
```agda
-- 3: If A is false AND B is false then...
de-morgan₂ : {A B : Set} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
de morgan₂ = ?
```
```agda
de-morgan₃ : {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
de-morgan₃ = ?
```
```agda
de-morgan₄ : {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
de-morgan₄ = ? -- this hole cannot be filled
```
The above hole cannot be filled, the intuitive reason of that is that Agda is a constructive system by default, in constructive mathematics we do not have this in general, assumption can only give us negative information (aka information that something does not hold), while here what we would need to do is to come with positive information (either the left or right holds).

Another apparent easy lemma to demonstrate is the _Law of exluded middle (LEM)_ which states that a given type is either empty of inhabited:
```agda
-- law of exluded middle (LEM): A ∨ ¬A
-- For any given type, it is either empty or inhabited
type-of-witnesses-of-lem = {A : Set} → A ⊎ (¬ A)

this-hole-cannot-be-filled : type-of-witnesses-of-lem 
this-hole-cannot-be-filled = ? 
```
This however cannot be demonstrated aswell. We must postulate it:
```agda
postulate
  -- we just say this is true without proving it 
  oracle : type-of-witnesses-of-lem 
  -- we can even create constant of the empty type
  lol    : ⊥

now-it-can-be-filled : type-of-witnesses-of-lem 
now-it-can-be-filled = oracle
```
With `postulate` we can even say 1 = 0 and so on, but we must be careful with what we postulate.

#### Decidability
_"Decidability in CS is the property (some properties) that there are machines which are able to find out wether that property holds or not"_
**Decidable properties** : Examples:
- property that a natural number being a prime number
- property that a number to be positive or zero
  
**Non-decidable properties** : Examples:
- property that a given function from ℕ to ℕ to have a zero (for this you would need to simulate the input for all possible natural number, which requires an infinite amount of time, just because to prove that a given function does NOT have a zero, you need to try every possible natural number)

How can this be formalized in Agda?

```agda
-- "Dec A" is the type of witnesses that A is decidable:
data Dec (A : Set) : Set where 
  yes :   A → Dec A 
  no  : ¬ A → Dec A 
```
There are two kinds of inhabitands of that type. If you want to verify `A`, you can (at your own choosing) either verify `A` or `¬ A`.

Example: **Positivity is decidable**
```agda
data Positive : ℕ → Set where
  succs-are-positive : (a : ℕ) → Positive (succ a)

positivity-is-decidable : (a : ℕ) → Dec (Positive a)
positivity-is-decidable zero      = ?
positivity-is-decidable (succ a)  = yes (succs-are-positive a) 
```
What do we put for `zero` in `?`?
For a moment let us try to fill that hole with a `yes` 
```agda
positivity-is-decidable : (a : ℕ) → Dec (Positive a)
positivity-is-decidable zero      = yes ?
positivity-is-decidable (succ a)  = yes (succs-are-positive a) 
```
Now in `?` we need a witness that `zero` is positive, which we are not able to.

```agda
data Positive : ℕ → Set where
  succs-are-positive : (a : ℕ) → Positive (succ a)

positivity-is-decidable : (a : ℕ) → Dec (Positive a)
positivity-is-decidable zero      = no  (λ ()) 
positivity-is-decidable (succ a)  = yes (succs-are-positive a) 
```

```agda
-- "Every inhabited set of natural numbers contains a mininmum"
-- this is true
-- We can picture a function P : ℕ → Set as a set of natural numbers
-- namely, the number n belongs to this set if and only if P n is
-- inhabited, hence P n is the type of witnesses that n belongs to the set.
data _≤_ (P : ℕ → Set) → (a₀ : ℕ) → P a₀ → ℕ 
  -- fill this in

-- function that computes the minimum
minimum : (P : ℕ → Set) → (a₀ : ℕ) → P a₀ → ℕ
minimum = ?

-- function that verify that the minimum is
-- computed correctly
lemma-minimum-is-computed-correctly
  : (P : ℕ → Set) → (a₀ : ℕ) → (p : P a₀)
  → (n : ℕ) → P n → a₀ ≤ n 
lemma-minimum-is-computed-correctly = ?
```
The two holes cannot be filled, intuitively: if the given minimum given `a₀` is `zero` we are done.
If it is greater than `zero` we would need to check wether there is a smaller number in the Set, which cannot be mechanically done.