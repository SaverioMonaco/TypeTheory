## More on equality of natural numbers; also polymorphic equality

As always we start with the previous definitions:
```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

data _≡_ : ℕ → ℕ → Set where
  refl : {a : ℕ} → (a ≡ a)   -- "reflexivity"
  -- bailout : {a b : ℕ} → (a ≡ b)

lemma : zero ≡ zero    -- \==
lemma = refl

lemma' : (b : ℕ) → ((zero + b) ≡ b)
lemma' b = refl
```

- `(zero ≡ zero)` is the type of witnesses that zero equals zero (this type is inhabited).
- `(zero ≡ succ zero)` is the type of witnesses that zero equals succ zero (this type is empty).

Last time, we were trying to demonstrate the following lemma:
```agda
lemma'' : (a : ℕ) → ((a + zero) ≡ a)
-- In this case both side are manifestly equal and we can use refl
lemma'' zero     = refl
lemma'' (succ a) = ?
```

What we need is a value of type `(succ (a + zero) ≡ a)`.

```agda
cong : {A B : Set} {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
cong f refl = refl
```

```agda
lemma'' : (a : ℕ) → ((a + zero) ≡ a)
lemma'' zero = refl
lemma'' (succ a) = cong succ (lemma'' a)
```

Let's prove symmetry:
```agda
symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl
```

#### Exercise: Transitivity
```agda
-- For x, y and z natural numbers, if x is equal to y
-- and y is equal to z, then x is equal to z
trans : {x y z : ℕ} → x ≡ y → y ≡ z → x ≡ z 
trans p q = ?
```
<details>
  <summary>Solution</summary>

  ```agda
  trans : {x y z : ℕ} → x ≡ y → y ≡ z → x ≡ z 
  trans p q = ?
  ```

</details>

Now we have all the main properties of the equality, _symmetry_, _transitivity_ and _congruence_ we are unstoppable.

---
Let us get back to the definition of addition how we defined it:
```agda
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)
```
That is not the only way how we could we have defined it:
```agda
_+'_ : ℕ → ℕ → ℕ
a +' zero   = a
a +' succ b = succ (a +' b)
```
That would work just as well, two different definitions with the same result that we could prove and we kinda already did:
```agda
lemma-+-zero : (a : ℕ) → ((a + zero) ≡ a )
lemma-+-zero zero     = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

lemma-+-succ : (a b : ℕ) → ((a + succ b) ≡ succ (a + b))
lemma-+-succ zero     b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)
```

Let us now try to prove commutativity of the addition, namely that `a + b = b + a` for every pair of natural numbers a and b:
```agda
-- function that takes a and b as natural numbers as 
-- inputs, and which outputs a witness that a+b=b+a
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
-- first we demonstrate that zero + b = b + zero, namely that
-- b = b + zero (direct computation from the definition of +)
-- lemma-+-commutative zero  b = (lemma-+-zero b)
-- would not work, lemma-+-zero shows a witness that
-- (b + zero) = b, but what we need is that b = (b + zero),
-- the other way around!
lemma-+-commutative zero     b = symm (lemma-+-zero b)
-- by itself(by what we proved)
-- Agda computes succ a + b = succ (a + b)
{-
  succ a + b = succ (a + b) = succ (b + a) = b + succ a
             ^              ^              ^
             |              |              |
            def    induction hypothesis    +---- symm (lemma-+-succ b a)
-}
lemma-+-commutative (succ a) b =
  --     cong : x ≡ y → f x ≡  f y
  --                induction
  --                                                (a + succ b) ≡ succ (a + b)
  --                                           succ (a + b) ≡ (a + succ b)
  trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))
```
This was our first true non trivial proof, hurray! :tada:

Let us go back to the equality and let us make it more general so it can take any type of variable:
```agda
data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → (a ≡ a)   -- "reflexivity"
  -- bailout : {a b : ℕ} → (a ≡ b)
```
---
#### Easy lemmas about Lists:
```agda
data List (A : Set) : Set where
  []  : List A              -- empty list
  _∷_ : A → List A → List A -- prepend constructor
```

First, let us prove that if we reverse a list twice, we get the initial list (for instance, "reverse (a ∷ b ∷ c ∷ [])" is "c ∷ b ∷ a ∷ []"):

##### modules
Sometimes Agda can be too pedantic, using modules we can avoid repeating ourselves by assuming _that something is kept fixed_:

```agda
-- fix the set A, a favorite-number and a function f:
module _ {A : Set} (favorite-number : ℕ) (f : ℕ → ℕ) where
  -- the "snoc" operation ("backwards cons"),
  -- i.e. append an element at the end
  _∷ʳ_ : List A → A → List A
  []       ∷ʳ y = y ∷ []
  (x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

  reverse : List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ∷ʳ x

  lemma-reverse-∷ʳ : (ys : List A) (x : A) → reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
  lemma-reverse-∷ʳ []       x = refl
  lemma-reverse-∷ʳ (y ∷ ys) x = {!!}

  lemma-reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
  lemma-reverse-reverse []       = refl
  lemma-reverse-reverse (x ∷ xs) =
    trans (lemma-reverse-∷ʳ (reverse xs) x)
          (cong (λ zs → x ∷ zs) (lemma-reverse-reverse xs))
```


