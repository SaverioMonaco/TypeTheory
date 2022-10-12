{-# OPTIONS --allow-unsolved-metas #-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
_+_ = {!!}

infixl 5 _≡_
data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x


module Experiment where
  pred : ℕ → ℕ
  pred zero     = zero
  pred (succ n) = n

  pred' : ℕ → ℕ
  pred' = pred

  _ : pred ≡ pred'
  _ = refl

  pred'' : ℕ → ℕ
  pred'' zero     = zero
  pred'' (succ n) = n

  -- NOTE: Without using the funext postulate from below, there is no
  -- way of filling in this hole!
  _ : pred ≡ pred''
  _ = {!!}

  lemma : (n : ℕ) → pred n ≡ pred'' n
  lemma zero     = refl
  lemma (succ n) = refl

  -- Ordinary blackboard mathematics employs the following axiom:
  -- FUNCTION EXTENSIONALITY: Functions which are pointwise equal
  -- (i.e. functions which produce the same output on each input) are
  -- equal.

  postulate
    funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
                                      -- ^^^^^^^^^^^^^^^^^^^^^   ^^^^^
                                      -- f and g are pw. equal   f and g are equal

  theorem : pred ≡ pred''
  theorem = funext lemma

  -- In case you need function extensionality, you can just postulate it.
  -- However note that this will destroy canonicity:
  -- Canonicity is the property that every term of type ℕ reduces to a numeral
  -- (to a term of the form succ (succ (succ ... (zero)...))).
  -- More generally, canonicity is the property that every term of
  -- every inductively generated type reduces to a term which begins with
  -- one of the constructors.

  -- Without custom postulates, Agda does have the canonicity property.
  -- Hence any term of type x ≡ y reduces to refl. Not so "theorem" above.


module Fail where
  data ℤ : Set where
    inj : ℕ → ℤ   -- "inject", "injection"
    neg : ℕ → ℤ
  -- Values of ℤ:
  -- inj zero (0), inj (succ zero) (1), inj (succ (succ zero)) (2), ...
  -- neg zero (-1), neg (succ zero) (-2), neg (succ (succ zero)) (-3), ...

  add : ℤ → ℤ → ℤ
  add (inj x) (inj y) = inj (x + y)
  add (inj x) (neg y) = {!!}
  add (neg x) (inj y) = {!!}
  add (neg x) (neg y) = neg (succ (x + y))
  -- Informally:
  -- add (neg x) (neg y) = neg x + neg y = -1-x + -1-y = -1-(x+y+1)
  -- This approach is neither suited for definitions nor for verifying properties!


module Pre-Integers where
  open import Data.Product

  -- the type of "pre-integers" (representations of integers)
  Z = ℕ × ℕ
  -- for instance, (succ (succ zero) , succ zero) : Z;        this denotes 2-1 (so 1).
  -- for instance, (succ zero , succ (succ (succ zero))) : Z; this denotes 1-3 (so -2).
  -- Note: (zero , zero) and (succ zero , succ zero) and (n , n) all denote the same integer 0.

  add : Z → Z → Z
  add (a , b) (a' , b') = a + a' , b + b'
  -- Informally: (a-b) + (a'-b') = (a+a') - (b+b')

  -- "x ≈ y" should be the type of witnesses that the two pre-integers "x" and "y"
  -- denote the same integer.
  _≈_ : Z → Z → Set
  -- (a , b) ≈ (a' , b') = {!a-b ≡ a'-b'!}
  (a , b) ≈ (a' , b') = b' + a ≡ a' + b

  _ : (zero , zero) ≈ (succ (succ zero) , succ (succ zero))
  _ = refl

  -- The true type of integers would be the quotient of Z by the equivalence relation _≈_.
  -- So the values of the true type ℤ of integers would be equivalence classes [ x ]
  -- such that [ x ] ≡ [ y ] iff x ≈ y.

  -- ISSUE: In Agda, we don't have quotients.
  -- There is no keyword "quotient" like: ℤ = quotient Z _≈_
  -- The next module will postulate those!


-- Module to postulate quotients, as Agda doesn't have them
module Quotient (A : Set) (_~_ : A → A → Set) (isEquivalence : {!!}) where
  postulate
    Q     : Set
    [_]   : A → Q    -- intuitively, [ x ] should be the equivalence class of x
    eq    : {x y : A} → x ~ y → [ x ] ≡ [ y ]
    exact : {x y : A} → [ x ] ≡ [ y ] → x ~ y
    rec   : {B : Set} (f : A → B) → ((x y : A) → x ~ y → f x ≡ f y) → (Q → B)
    comp  : {B : Set} (f : A → B) → (ext : (x y : A) → x ~ y → f x ≡ f y) {x : A} → rec f ext ([ x ]) ≡ f x
    -- This is the recursor and its computation rule.
    -- We also need the induction principle and the computation rule for that (both not shown here).
    -- In fact, the induction principle and its computation rule render the recursor and its rule superfluous.


module Integers where
  open import Data.Product
  open Quotient Pre-Integers.Z Pre-Integers._≈_ {!!}

  ℤ : Set
  ℤ = Q

  integer-zero : ℤ
  integer-zero = [ (zero , zero) ]

  integer-minusone : ℤ
  integer-minusone = [ (zero , succ zero) ]


module RecordExample where
  String : Set
  String = ℕ

  record Person : Set where
    field
      name    : String
      address : String
      age     : ℕ

  ex : Person
  ex = record
    { name    = {!!}
    ; address = {!!}
    ; age     = {!!}
    }

  f : Person → ℕ
  f x = Person.age x + succ zero

  {-
    open Person
    g : Person → ℕ
    g x = age x + succ zero
  -}

  h = age + succ zero
    where
    open Person ex


record IsEquivalence {X : Set} (_~_ : X → X → Set) : Set where
  field
    reflexive  : {x : X} → x ~ x
    symmetric  : {x y : X} → x ~ y → y ~ x
    transitive : {x y z : X} → x ~ y → y ~ z → x ~ z

lemma-≈-is-equivalence-relation : IsEquivalence Pre-Integers._≈_
lemma-≈-is-equivalence-relation = record { reflexive = {!!} ; symmetric = {!!} ; transitive = {!!} }


-- Introduction to setoid hell :-)
module Setoids where
  -- A setoid is a type together with an equivalence relation on it.
  -- For instance, the type Z of pre-integers together with _≈_ is a setoid.

  -- Functions between setoids are by definitions functions between
  -- the underlying types which respect the given equivalence
  -- relations.

  record Setoid : Set₁ where
    field
      Carrier : Set
      _~_     : Carrier → Carrier → Set
      isEquiv : IsEquivalence _~_

  ℤ' : Setoid
  ℤ' = record { Carrier = Pre-Integers.Z ; _~_ = Pre-Integers._≈_ ; isEquiv = lemma-≈-is-equivalence-relation }

  record _⇒_ (X Y : Setoid) : Set where
    field
      fun   : Setoid.Carrier X → Setoid.Carrier Y
      track : {x x' : Setoid.Carrier X} → Setoid._~_ X x x' → Setoid._~_ Y (fun x) (fun x')

  open import Data.Product

  negation : ℤ' ⇒ ℤ'
  negation = record
    { fun = λ { (a , b) → (b , a) }
    ; track = {!!}
    }

