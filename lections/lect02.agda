module lect02 where

open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.List renaming (length to len)

module X where
  foo'' : ℕ
  foo'' = 0

open X

-- qux = X.foo''
qux = foo''


module Sort {A : Set} (_<_ : A → A → Bool) where
  sort : List A → List A
  sort xs = xs

_<<_ : ℕ → ℕ → Bool
_ << _ = false

open Sort _<<_

ff = sort

-- instead of type LN = List ℕ
LN = List ℕ

-- Universes


-- Set equals to Set₀
-- Set₁ contains Set₀ are types that one can construct from Set₀ et cetera
f : Set₁ → Set₁
f X = X


-- Level polymorphism
data List' {l} (A : Set l) : Set l where
  nil : List' A
  cons : A → List' A → List' A

-- List of types
gg = cons ℕ (cons (ℕ → ℕ) nil)


-- Records
record Point : Set where
  constructor point
  field
    x : ℕ
    y : ℕ

-- without constructor
record Point' : Set where
  field
    x : ℕ
    y : ℕ

data Point'' : Set where
  point'' : ℕ → ℕ → Point''

origin = point 0 0

origin' : Point'
origin' = record { x = 0; y = 0 }

_==''_ : ℕ → ℕ → Bool
0 =='' 0 = true
0 =='' suc x = false
suc x =='' 0 = false
suc x =='' suc y = x =='' y

_=='_ : Point → Point → Bool
point x y ==' q = Point.x q =='' Point.y q

infix 3 _&&_
_&&_ : Bool → Bool → Bool
true && x = x
_ && false = false
false && _ = false

-- Eta-equivallence
_=='''_ : Point'' → Point'' → Bool
point'' x y ==''' point'' x' y' = (x =='' x') && (y =='' y')
