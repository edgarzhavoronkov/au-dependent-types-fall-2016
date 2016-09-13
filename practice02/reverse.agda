module reverse where

data Bool : Set where
    true false : Bool

not : Bool → Bool
not true = false
not false = true

infix 7 _||_
_||_ : Bool → Bool → Bool
true || _ = true
false || x = x

infix 9 if_then_else_
if_then_else_ : {A : Set} → Bool → A → A → A
if true then y else _ = y
if false then _ else z = z

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
nil ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

reverse : {A : Set} → List A → List A
reverse nil = nil
reverse (cons x xs) = reverse xs ++ cons x nil

rev-acc : {A : Set} → List A → List A → List A
rev-acc acc nil = acc
rev-acc acc (cons x xs) = rev-acc (cons x acc) xs

rev : {A : Set} -> List A -> List A
rev = rev-acc nil

infix 3 _==_
_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc _ = false
suc _ == zero = false
suc x == suc y = x == y

infix 2 _&&_
_&&_ : Bool → Bool → Bool
true && true = true
_ && _ = false

_=='_ : List ℕ → List ℕ → Bool
nil ==' nil = true
cons x xs ==' nil = false
nil ==' cons x xs = false
cons x xs ==' cons y ys = x == y && xs ==' ys

data Empty : Set where

data Unit : Set where
  unit : Unit

T : Bool → Set
T true = Unit
T false = Empty

T-&& : (x y : Bool) → T x → T y → T (x && y)
T-&& true true x x₁ = unit
T-&& true false x()
T-&& false true()
T-&& false false()

ℕ-refl : (x : ℕ) → T (x == x)
ℕ-refl zero = unit
ℕ-refl (suc x) = ℕ-refl x

list-refl : (xs : List ℕ) → T (xs ==' xs)
list-refl nil = unit
list-refl (cons x xs) = T-&& (x == x) (xs ==' xs) (ℕ-refl x) (list-refl xs)

rev-rev-acc : (ys xs : List ℕ) → T (rev (rev-acc ys xs) ==' rev-acc xs ys)
rev-rev-acc ys nil = list-refl (rev ys)
rev-rev-acc ys (cons x xs) = rev-rev-acc (cons x ys) xs

rev-rev : (xs : List ℕ) → T (rev (rev xs) ==' xs)
rev-rev = rev-rev-acc nil
