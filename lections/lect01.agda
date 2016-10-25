module lect01 where

data Bool : Set where
  ⊤ : Bool
  ⊥ : Bool

not : Bool → Bool
not ⊤ = ⊥
not ⊥ = ⊤

infixl 7 _||_
_||_ : Bool → Bool → Bool
⊤ || _ = ⊤
⊥ || x = x



data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

infix 8 if_then_else_
if_then_else_ : Bool → ℕ → ℕ → ℕ
if ⊤ then x else _ = x
if ⊥ then _ else x = x

infix 5 _+_
_+_ : ℕ → ℕ → ℕ
Z + y = y
S x + y = S (x + y)

infix 6 _*_
_*_ : ℕ → ℕ → ℕ
Z * x = Z
S x * y = y + x * y

infix 5 _-_
_-_ : ℕ → ℕ → ℕ
Z - x = Z
S x - Z = S x
S x - S y = x - y

_<_ : ℕ → ℕ → Bool
Z < Z = ⊥
Z < S x = ⊥
S x < Z = ⊤
S x < S y = x < y


div' : ℕ → ℕ → ℕ → ℕ
div' Z _ _ = Z
div' (S c) x y = if x < y then Z else S (div' c (x - y) y)

div : ℕ → ℕ → ℕ
div x y = div' x x y


-- Π(a ∈ A)B
--∀ (A : Set) → B
id : ∀ (A : Set) → A → A
id A a = a

--implicit arguments
id' : {A : Set} → A → A
id' a = a

foo = id ℕ (S Z)
foo' = id _ (S Z)

foo'' = id' Z


data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Unit : Set where
  unit : Unit

data Empty : Set where

absurd : {A : Set} → Empty → A
absurd ()

--Prove that not (not x) == x
_==_ : Bool → Bool → Bool
⊤ == ⊤ = ⊤
⊤ == ⊥ = ⊥
⊥ == ⊤ = ⊥
⊥ == ⊥ = ⊤

T : Bool → Set
T ⊤ = Unit
T ⊥ = Empty

not-inv : (x : Bool) → T (not (not x) == x)
not-inv ⊤ = unit
not-inv ⊥ = unit
