module tasks03 where

open import Data.Nat
open import Data.Unit
open import Data.Product

vec : Set → ℕ → Set
vec A 0 = ⊤
vec A (suc n) = A × vec A n

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

head : {A : Set} {n : ℕ} → Vec A (suc n) → A
head (cons x _) = x

tail : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
tail = {!   !}

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

-- диагональная матрица

diag : {A : Set} → A → A → {n : ℕ} → Mat A n n
diag z o {zero} = nil
diag z o {suc n} = cons (cons z (coin (λ _ → o))) (map₂ (λ l -> cons o l) (diag z o {n}))

-- транспонирование матриц

transpose : {A : Set} {n m : ℕ} → Mat A n m → Mat A m n
transpose nil = coin (λ _ → nil)
transpose (cons M M₁) = zipWith₂ cons M (transpose M₁)

mat : Mat ℕ 1 3
mat = cons (cons 1 (cons 2 (cons 3 nil))) nil

-- сложение матриц

add : {A : Set} (_+_ : A → A → A) → {n m : ℕ} → Mat A n m → Mat A n m → Mat A n m
add _+_ nil nil = nil
add _+_ (cons M M₁) (cons N N₁) = cons (zipWith₂ _+_ M N) (add _+_ M₁ N₁)

-- умножение матриц

sum : {A : Set} (_+_ : A → A → A) → {n : ℕ} → Vec A (suc n) → A
sum _+_ {zero} (cons x v) = x
sum _+_ {suc n} (cons x v) = x + (sum _+_ v)

-- scalar(or dot) product
scalar : {A : Set} {n : ℕ} → (_+_ _*_ : A → A → A) → Vec A (suc n) → Vec A (suc n) → A
scalar _+_ _*_ x y = sum (_+_) (zipWith₂ (_*_) x y)

-- сначала стобцы, потом строки!
-- Mat ℕ 3 2
-- [1,2,3]
-- [4,5,6]

-- умножение матрицы на вектор
_**_ : {A : Set} (_+_ _*_ : A → A → A) → {n m : ℕ} → Mat A (suc n) (suc m) → Vec A (suc m) → Vec A (suc n)
_**_ _+_ _*_ m v = map₂ (λ r → scalar _+_ _*_ r v) m

mul : {A : Set} (_+_ _*_ : A → A → A) → {n m k : ℕ} → Mat A (suc n) (suc m) → Mat A (suc m) (suc k) → Mat A (suc n) (suc k)
mul _+_ _*_ x y = map₂ (λ r → _**_ _+_ _*_ yt r) x
  where
    yt = transpose y

-- 5. Определите при помощи индуктивных семейств тип CTree A n бинарных деревьев высоты ровно n с элементами во внутренних узлах.
--    Любое такое бинарное дерево будет полным.

toℕ : {n : ℕ} → Fin n → ℕ
toℕ zero = zero
toℕ (suc x) = suc (toℕ x)

data CTree (A : Set) : ℕ → Set where
  leaf : A → CTree A 0
  branch : {n : ℕ} → A → CTree A n → CTree A n → CTree A (suc n)

-- 6. Определите при помощи индуктивных семейств тип Tree A n бинарных деревьев высоты не больше n с элементами во внутренних узлах.

data Tree (A : Set) : ℕ → Set where
  
-- определите функцию, возвращающую высоту дерева.

height : {A : Set} (n : ℕ) → Tree A n → Fin (suc n)
height zero t = {!   !}
height (suc n) t = {!   !}
