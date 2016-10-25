module lect03 where

open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Product

-- 1. Определить Vec рекурсивно

Vec : Set → ℕ → Set
Vec A 0 = ⊤
Vec A (suc n) = A × Vec A n

list : Vec ℕ 3
list = 0 , 1 , 2 , tt

head : {A : Set} {n : ℕ} → Vec A (suc n) → A
head (x , _) = x

tail : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
tail (_ , xs) = xs

-- 2. Определить Vec индуктивно

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

-- data Vect₁ (A : Set) (n : ℕ) → Set where
--   nil : T (n ≡ 0) → Vect₁ A n
--   cons : {n' : ℕ} → T (n ≡ suc n') → A → Vect₁ A n' → Vect₁ A n

-- Индуктивное семейство. Заметим, что Vec и Vect изоморфны, можно написать простые функции перегоняющие один в другой
data Vect (A : Set) : ℕ → Set where
  nil : Vect A 0
  cons : {n : ℕ} → A → Vect A n → Vect A (suc n)

list₀ : Vect ℕ 0
list₀ = nil

list₁ : Vect ℕ 1
list₁ = cons 10 nil

list₂ : Vect ℕ 2
list₂ = cons 14 (cons 88 nil)

-- 3. head, tail, append

head' : {A : Set} {n : ℕ} → Vect A (suc n) → A
head' (cons x _) = x

tail' : {A : Set} {n : ℕ} → Vect A (suc n) → Vect A n
tail' (cons _ xs) = xs

-- Мораль в том, что плюс определен рекурсией по первому аргументу, поэтому здесь мы тоже паттерматчимся по первому списку
append' : {A : Set} {n m : ℕ} → Vect A n → Vect A m → Vect A (n + m)
append' nil ys = ys
append' (cons x xs) ys = cons x (append' xs ys)

-- 4. length для Vect

length : {A : Set} {n : ℕ} → Vect A n → ℕ
length {A} {n} _ = n


-- 5. Dot-patterns
data Vect₁ (A : Set) : ℕ → Set where
  nil : Vect₁ A 0
  cons : (n : ℕ) → A → Vect₁ A n → Vect₁ A (suc n)

-- Мораль в том, что если убрать точку, то агда выругается, что дважды связывается одна и та же переменная
-- Неявные аргументы лучше в том отношении, что они сами ставят точки
head₁ : {A : Set} (n : ℕ) → Vect₁ A (suc n) → A
head₁ .n (cons n x _) = x

tail₁ : {A : Set} {n : ℕ} → Vect₁ A (suc n) → Vect₁ A n
tail₁ (cons n _ xs) = xs

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

tail-fac : {A : Set} (n : ℕ) → Vect₁ A (suc (fac n)) → Vect₁ A (fac n)
tail-fac n (cons .(fac n) _ xs) = xs


-- 6. Стрельнем себе в ногу

-- Не пиши выражения, которые не являются корректными паттернами. То есть пиши конструкторы
data Foo : ℕ → Set where
  foo : (n : ℕ) → Foo (fac n)

-- Ошибка при паттерматчинге, агда не может проверить, что факториал равен сумме двух чисел
{-
baz : (n k : ℕ) → Foo (n + k) → ℕ
baz n k x = {! x  !}
-}

-- Если совсем хочется, то надо принимать доказательство, что все хорошо

_==_ : ℕ → ℕ → Bool
0 == 0 = true
0 == suc _ = false
suc _ == 0 = false
suc x == suc y = x == y

data Foo' (k : ℕ) : Set where
  foo : (n : ℕ) → T (k == fac n) → Foo' k

-- bar : (n k : ℕ) → Foo' (n + k) → ℕ
-- bar zero k (foo n₁ x) = {!   !}
-- bar (suc n) k (foo n₁ x) = {!   !}

-- 7. Fin, toℕ, index.
-- Fin n - множество натуральных чисел, меньших n

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

index : {A : Set} {n : ℕ} → Vect A n → (k : Fin n) → A
index (cons x xs) zero = x
index (cons x xs) (suc k) = index xs k

-- Вкладываем конечное множество в натуральные числа
toℕ : {n : ℕ} → Fin n → ℕ
toℕ zero = zero
toℕ (suc x) = suc (toℕ x)
