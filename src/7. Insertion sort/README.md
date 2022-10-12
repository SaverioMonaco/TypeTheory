## Correctness of insertion sort
-- Today: Implement a sorting algorithm and verify its correctness.

-- TWO METHODS FOR VERIFYING CORRECTNESS:
-- (a) first implement, then separately verify correctness
-- (b) correct by construction

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

-- Goal: Define sort : ??? → List A → List A.

module Implementation
  {A : Set}
  (_≤_ : A → A → Set)    -- for values x, y : A, the type "x ≤ y" is the
                         -- type of witnesses that x is less than or equal to y
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- Given an ordered list "ys", "insert x ys" is the same as "ys", but with
  -- "x" inserted at the correct place to ensure that the resulting
  -- list is again sorted.
  insert : A → List A → List A
  insert x []       = x ∷ []   -- in Haskell, this would be written "[x]"
  insert x (y ∷ ys) with cmp x y
  ... | left  x≤y = x ∷ (y ∷ ys)
  ... | right y≤x = y ∷ insert x ys

  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs)

module Verification
  {A : Set}
  (_≤_ : A → A → Set)    -- for values x, y : A, the type "x ≤ y" is the
                         -- type of witnesses that x is less than or equal to y
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  open Implementation _≤_ cmp

  -- "IsOrdered xs" is the type of witnesses that the list "xs" is ordered.
  -- This type is empty if and only if the list is not ordered.
  data IsOrdered : List A → Set where
    empty     : IsOrdered []
    singleton : {x : A} → IsOrdered (x ∷ [])
    cons      : {x y : A} {ys : List A} → x ≤ y → IsOrdered (y ∷ ys) → IsOrdered (x ∷ (y ∷ ys))

  lemma₀ : (x y : A) (ys : List A) → y ≤ x → IsOrdered (y ∷ ys) → IsOrdered (y ∷ insert x ys)
  lemma₀ x y []       y≤x p = cons y≤x singleton
  lemma₀ x y (z ∷ ys) y≤x (cons y≤z q) with cmp x z
  ... | left  x≤z = cons y≤x (cons x≤z q)
  ... | right z≤x = cons y≤z (lemma₀ x z ys z≤x q)

  -- Given an ordered list "ys", "insert x ys" is the same as "ys", but with
  -- "x" inserted at the correct place to ensure that the resulting
  -- list is again sorted.
  lemma : (x : A) (ys : List A) → IsOrdered ys → IsOrdered (insert x ys)
  lemma x []       p = singleton
  lemma x (y ∷ ys) p with cmp x y
  ... | left  x≤y = cons x≤y p
  ... | right y≤x = lemma₀ x y ys y≤x p

  theorem : (xs : List A) → IsOrdered (sort xs)
  theorem []       = empty
  theorem (x ∷ xs) = lemma x (sort xs) (theorem xs)

  cheatsort : List A → List A
  cheatsort xs = []

  cheattheorem : (xs : List A) → IsOrdered (cheatsort xs)
  cheattheorem xs = empty

{-
  example-lemma : IsOrdered []
  example-lemma = empty

  example-lemma' : {a b c : A} → a ≤ b → b ≤ c → IsOrdered (a ∷ (b ∷ (c ∷ [])))
  example-lemma' p q = cons p (cons q singleton)
-}

module CorrectByConstruction
  {A : Set}
  (_≤_ : A → A → Set)    -- for values x, y : A, the type "x ≤ y" is the
                         -- type of witnesses that x is less than or equal to y
  (min : A) (min≤ : {x : A} → min ≤ x)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x))
  where

  -- "OList l" is the type of ordered lists of elements of A which are bounded from below by l
  -- (that is, all elements need to be ≥ l).
  data OList (l : A) : Set where
    nil  : OList l
    cons : (x : A) → l ≤ x → OList x → OList l

  insert : {l : A} → (x : A) → l ≤ x → OList l → OList l
  insert x l≤x nil             = cons x l≤x nil
  insert x l≤x (cons y l≤y ys) with cmp x y
  ... | left  x≤y = cons x l≤x (cons y x≤y ys)
  ... | right y≤x = cons y l≤y (insert x y≤x ys)

  sort : List A → OList min
  sort []       = nil
  sort (x ∷ xs) = insert x min≤ (sort xs)

  cheatsort : List A → OList min
  cheatsort xs = nil

{-
  toList : {l : A} → OList l → List A
  toList nil           = []
  toList (cons x p xs) = x ∷ toList xs
-}

