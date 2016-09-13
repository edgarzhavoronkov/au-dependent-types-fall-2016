module tasks02 where

open import Data.Bool
open import Data.List
open import Data.Nat hiding (_<_; _+_)
open import Data.Unit
open import Data.Empty

-- for 1 see ../practice01/tasks01.agda

-- 2. Определите запись Point, который может хранить элементы произвольных типов A и B произвольных уровней.
--    Определите равенство для такого типа Point.

record Point {l} (A B : Set l) : Set l where
  constructor point
  field
    x : A
    y : B

_==ₚ_ : ∀{l} → {A B : Set l} →
        (_==ₐ_ : A → A → Bool) →
        (_==♭_ : B → B → Bool) →
        Point A B → Point A B → Bool
_==ₚ_ (_==ₐ_) (_==♭_) (point x y) (point x₁ y₁) = x ==ₐ x₁ ∧ y ==♭ y₁



-- 3. Напишите функцию lookup, которая принимает список и натуральное число и возвращает элемент по заданому индексу.
--    В общем случае эту функцию определить невозможно, т.к. индекс может быть больше, чем число элементов в списке.
--    Поэтому эта функция должна дополнительно еще принимать доказательство того, что всё хорошо.

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

data Unit : Set where
  unit : Unit

data Empty : Set where

P : Bool → Set
P true = Unit
P false = Empty

lookup : ∀{l} → {A : Set l} → (xs : List A) → (i : ℕ) → P (i < length xs) → A
lookup (x ∷ xs) zero proof = x
lookup (x ∷ xs) (suc y) proof = lookup xs y proof
lookup [] zero()
lookup [] (suc x)()

-- 4. Докажите ассоциативность сложения для натуральных чисел.

infix 5 _+_
_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

infix 3 _==_
_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc _ = false
suc _ == zero = false
suc x == suc y = x == y

==refl : (x : ℕ) → P (x == x)
==refl zero = unit
==refl (suc x) = ==refl x

+assoc : (a b c : ℕ) → P ((a + b) + c == a + (b + c))
+assoc zero b c = ==refl (b + c)
+assoc (suc a) b c = +assoc a b c

-- 5. Обобщите алгоритм сортировки так, чтобы он работал для произвольных типов.
--    Используйте для этого модули.
--    Вызовите этот алгоритм на каком-нибудь списке натуральных чисел. Например, 3 ∷ 1 ∷ 2 ∷ []

module Sort {l}{A : Set l} (_<_ : A → A → Bool) where
  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ ys) = if (x < y) then (x ∷ y ∷ ys) else (y ∷ (insert x ys))

  sort : List A → List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

open Sort _<_

sorted = sort (3 ∷ 1 ∷ 2 ∷ [])
