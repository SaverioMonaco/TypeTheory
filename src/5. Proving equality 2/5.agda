data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_+'_ : ℕ → ℕ → ℕ
a +' zero   = a
a +' succ b = succ (a +' b)


data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → (a ≡ a)   -- "reflexivity"
  -- bailout : {a b : ℕ} → (a ≡ b)

{-
theorem : zero ≡ succ zero
theorem = bailout
-}

-- (zero ≡ zero) is the type of witnesses that zero equals zero (this type
-- is inhabited).
-- (zero ≡ succ zero) is the type of witnesses that zero equals succ zero (this type
-- is empty).
lemma : zero ≡ zero    -- \==
lemma = refl

lemma' : (b : ℕ) → ((zero + b) ≡ b)
lemma' b = refl

{-
factorial : ℕ → ℕ
factorial zero = {!!}
factorial (succ n) = {!!}
-}

cong : {A B : Set} {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
cong f refl = refl

lemma-+-zero : (a : ℕ) → ((a + zero) ≡ a)
lemma-+-zero zero     = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)
-- (lemma-+-zero a) is a value of type ((a + zero) ≡ a).
-- What we need is a value of type (succ (a + zero) ≡ succ a).

lemma-+-succ : (a b : ℕ) → ((a + succ b) ≡ succ (a + b))
lemma-+-succ zero     b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

-- EXERCISE
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = {!!}

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative zero     b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b =
  trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))

-- LET'S RESUME AT 15:40 :-)

{-
  succ a + b = succ (a + b) = succ (b + a) = b + succ a
             ^              ^              ^
             |              |              |
            def    induction hypothesis    +---- symm (lemma-+-succ b a)
-}



data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

module _ {A : Set} (favorite-number : ℕ) (f : ℕ → ℕ) where
  -- the "snoc" operation ("backwards cons"),
  -- i.e. append an element at the end
  _∷ʳ_ : List A → A → List A
  []       ∷ʳ y = y ∷ []
  (x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

  -- for instance, "reverse (a ∷ b ∷ c ∷ [])" is "c ∷ b ∷ a ∷ []".
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

