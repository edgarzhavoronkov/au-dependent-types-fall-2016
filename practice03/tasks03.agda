module tasks03 where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Bool

vec : Set → ℕ → Set
vec A 0 = ⊤
vec A (suc n) = A × vec A n

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- 1. Реализуйте аналоги функции map для vec и Vec.

map₁ : {A B : Set} {n : ℕ} → (A → B) → vec A n → vec B n
map₁ {n = zero} f tt = tt
map₁ {n = suc n} f (x , xs) = f x , map₁ {n = n} f xs

map₂ : {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
map₂ f nil = nil
map₂ f (cons x x₁) = cons (f x) (map₂ f x₁)

-- 2. Реализуйте аналоги функции zipWith для vec и Vec.

zipWith₁ : {A B C : Set} {n : ℕ} → (A → B → C) → vec A n → vec B n → vec C n
zipWith₁ {n = zero} f x y = tt
zipWith₁ {n = suc n} f (x , xs) (y , ys) = f x y , zipWith₁ f xs ys

zipWith₂ : {A B C : Set} {n : ℕ} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith₂ f nil nil = nil
zipWith₂ f (cons x xs) (cons x₁ ys) = cons (f x x₁) (zipWith₂ f xs ys)

-- 3. Функции Fin n → A соответствуют спискам элементов A длины n.
--    Функция, преобразующие Vec A n в Fin n → A была реализована на лекции.
--    Реализуйте обратную функцию.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)


index : {A : Set} {n : ℕ} → Vec A n → (k : Fin n) → A
index (cons x xs) zero = x
index (cons x xs) (suc k) = index xs k

coin : {A : Set} {n : ℕ} → (Fin n → A) → Vec A n
coin {n = zero} f = nil
coin {n = suc n} f = cons (f zero) (coin (λ n₁ → f (suc n₁)))

-- 4. Определите тип матриц и ряд функций над ними.

Mat : Set → ℕ → ℕ → Set
Mat A n m = Vec (Vec A m) n

-- Vec (Vec ℕ 3) 2
mat : Mat ℕ 2 3
mat = cons (cons 1 (cons 2 (cons 3 nil))) (cons (cons 4 (cons 5 (cons 6 nil))) nil)

-- диагональная матрица

diag : {A : Set} → A → A → {n : ℕ} → Mat A n n
diag a b {zero} = nil
diag a b {suc n} = cons (cons a (coin (λ _ → b))) (map₂ (λ r → cons b r) (diag a b {n}))

-- транспонирование матриц

transpose : {A : Set} {n m : ℕ} → Mat A n m → Mat A m n
transpose nil = coin (λ _ → nil)
transpose (cons m₁ m₂) = zipWith₂ cons m₁ (transpose m₂)

-- сложение матриц

add : {A : Set} (_+_ : A → A → A) → {n m : ℕ} → Mat A n m → Mat A n m → Mat A n m
add _+_ nil nil = nil
add _+_ (cons M M₁) (cons N N₁) = cons (zipWith₂ _+_ M N) (add _+_ M₁ N₁)

-- умножение матриц

sum : {A : Set} (_+_ : A → A → A) → (zro : A) → {n : ℕ} → Vec A n → A
sum _+_ zro {zero} nil = zro
sum _+_ zro {suc n} (cons x v) = x + (sum _+_ zro v)

-- scalar(or dot) product
scalar : {A : Set} {n : ℕ} → (_+_ _*_ : A → A → A) → (zro : A) → Vec A n → Vec A n → A
scalar _+_ _*_ zro x y = sum (_+_) zro (zipWith₂ (_*_) x y)

-- умножение матрицы на вектор
_**_ : {A : Set} (_+_ _*_ : A → A → A) → (zro : A) → {n m : ℕ} → Mat A n m → Vec A m → Vec A n
_**_ _+_ _*_ z m v = map₂ (λ r → scalar _+_ _*_ z r v) m


mul : {A : Set} (_+_ _*_ : A → A → A) → (zro : A) → {n m k : ℕ} → Mat A n m → Mat A m k → Mat A n k
mul _+_ _*_ zro x y = map₂ (λ r → _**_ _+_ _*_ zro (transpose y) r) x

-- 5. Определите при помощи индуктивных семейств тип CTree A n бинарных деревьев высоты ровно n с элементами во внутренних узлах.
--    Любое такое бинарное дерево будет полным.

toℕ : {n : ℕ} → Fin n → ℕ
toℕ zero = zero
toℕ (suc x) = suc (toℕ x)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

data CTree (A : Set) : ℕ → Set where
  leaf : A → CTree A 0
  branch : {n : ℕ} → A → CTree A n → CTree A n → CTree A (suc n)

-- 6. Определите при помощи индуктивных семейств тип Tree A n бинарных деревьев высоты не больше n с элементами во внутренних узлах.

-- data Tree (A : Set) : ℕ → Set where
--   leaf : {k : Fin 2} → A → Tree A (toℕ k)
--   branch : {n : ℕ} {k m : Fin n} → A → Tree A (toℕ k) → Tree A (toℕ m) → Tree A  (suc (toℕ m) ⊔ (toℕ k))
--   branch : {n : ℕ} {k : Fin n} → A → Tree A (toℕ k) → Tree A (toℕ k) → Tree A (toℕ (suc k))

data Tree (A : Set) : ℕ → Set where
  leaf : {n : ℕ} → A → Tree A n
  branch : {n : ℕ} →  A → Tree A n → Tree A n → Tree A (suc n)

-- определите функцию, возвращающую высоту дерева.

max : {n : ℕ} → Fin n → Fin n → Fin n
max zero zero = zero
max zero (suc b) = suc b
max (suc a) zero = suc a
max (suc a) (suc b) = suc (max a b)

height : {A : Set} (n : ℕ) → Tree A n → Fin (suc n)
height zero (leaf x) = zero
height (suc n) (leaf x) = zero
height (suc n) (branch x t t₁) = suc (max (height n t) (height n t₁))
