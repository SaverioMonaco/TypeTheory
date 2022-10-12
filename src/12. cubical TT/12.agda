{-# OPTIONS --cubical #-}
-- TODAY: CUBICAL AGDA \o/

{-
  A ROSETTA STONE between logic, type theory
  and homotopy theory

  How to think about types?

  (1) logic: types as (perhaps "witness-y") propositions
           e.g. (n : ℕ) → (0 + n ≡ n) is the proposition
                that for any number n, 0 + n ≡ n.

  (2) type theory: types as some kind of sets/collections/...
           e.g. (n : ℕ) → (0 + n ≡ n) is the collection of
                functions which map numbers n to witnesses that 0 + n ≡ n.

  (3) homotopy theory: types as animas

  An anima is a space considered up to homotopy equivalence.

  A dictionary:

    logic                      type theory     homotopy theory
    
    a proposition              a type          an anima
    a witness                  x : X           point of an anima
    contradiction              ⊥ (empty type)  empty anima
    statement that x ≡ y       (x ≡ y)         anima of paths from x to y
    trivial proof that x≡x     refl : x ≡ x    trivial path from x to x

  Advantages of cubical type theory over ordinary MLTT:
  * function extensionality: "if two functions agree on all inputs, they are the same"
  * quotients:               X/~, ℤ/n
  * higher inductive types:  ∥ X ∥ (truncation), S¹ (the circle)
  
  Advantages of cubical type theory over homotopy type theory:
  * univalence computes

  Advantages of cubical type theory over ordinary programming:
  * univalence theorem
  
  Advantages of cubical type theory and homotopy type theory over set theory as a foundation:
  * can do homotopy theory right away ("batteries included")
    without having to first define reals, topological spaces, homotopy, ...
  * new grip of identity
-}

open import Cubical.Core.Everything

data S¹ : Type where
  north : S¹
  loop  : north ≡ north
-- We automatically have refl : north ≡ north,
-- but loop is a distinct path from north to north.
-- loop · loop, loop · loop · loop, ...
-- sym loop, sym loop · sym loop, ...
-- In fact, the type (north ≡ north) is equivalent to ℤ.

-- *----*
data UnitInterval : Type where
  start : UnitInterval
  end   : UnitInterval
  seg   : start ≡ end


--   --
--  /  \           -------
-- *    *---------/       \
--  \                     /
--   ---------------------
data Diamond : Type where
  start : Diamond
  end   : Diamond
  upper : start ≡ end
  lower : start ≡ end

open import Data.Nat
data ℤ : Type where
  _⊖_  : ℕ → ℕ → ℤ  -- \ominus
  step : (a b : ℕ) → a ⊖ b ≡ suc a ⊖ suc b
-- 0ℤ = 0 ⊖ 0 = 5 ⊖ 5
-- 1ℤ = 1 ⊖ 0 = 6 ⊖ 5

data ℤ/3 : Type where
  zero : ℤ/3
  succ : ℤ/3 → ℤ/3
  pa   : zero ≡ succ (succ (succ zero))
-- *  *  *  *  *  *  *  *  *  *
--  \      /
--   ------
-- pa i0 : zero
-- pa i1 : succ (succ (succ zero))
-- pa 0.5

{-
wont-work : ℤ/3 → ℕ
wont-work zero     = zero
wont-work (succ x) = suc (wont-work x)
wont-work (pa i)   = {!!}
-}

add1 : ℤ → ℤ
add1 (a ⊖ b)      = suc a ⊖ b
add1 (step a b i) = step (suc a) b i
--    ^^^^^^^^      ^^^^^^^^^^^^^^
--    path from a ⊖ b to suc a ⊖ suc b
--
--                  path from suc a ⊖ b to suc (suc a) ⊖ suc b

symm' : {A : Type} {x y : A} → x ≡ y → y ≡ x
symm' p = λ i → p (~ i)
-- p (1 - 0) = p 1
-- p (1 - 1) = p 0

funext : {A B : Type} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funext h = λ i → λ x → h x i  
--               ^^^^^^^^^^^ whatever we write there, it should have the
--                           property that plugging in i0 yields f
--                           and           plugging in i1 yields g

{-
refl'' : {A : Type} {x : A} → x ≡ x
refl'' {A} {x} i0 = {!!}
refl'' {A} {x} i1 = {!!}
-}

{-
foo : Type → ℤ
foo ⊥ = {!!}
foo ℕ = {!!}
foo (A × B) = {!!}
foo (A → B) = {!!}
foo ...
-}

refl' : {A : Type} {x : A} → x ≡ x
refl' {A} {x} = λ i → x
-- In Cubical Agda/Cubical Type Theory,
-- (x ≡ y) is the type of functions γ from I to A
-- such that γ i0 is definitionally the same as x,
-- and  that γ i1 is definitionally the same as y.

-- The picture of I is the unit interval: *--------*
--                                        i0      i1
-- A path in A is a function γ : I → X.
-- The starting point of this path is γ(i0).
-- The end      point of this path is γ(i1).
-- For any other i, γ(i) is somewhere along the path from γ(i0) to γ(i1).

{-
  x = γ(i0)
  *
   \                    γ(0.9)
    \             /\     |
     \           /  \    v
      +---*-----+    +---*--*
          γ(0.5)            y = γ(i1)
-}

