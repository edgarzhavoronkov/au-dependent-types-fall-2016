module lect07 where

open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat.Base hiding (_≤_; _<_; Ordering; compare)
open import Data.List hiding (zipWith)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum


-- 1. Тактики в Agda. Можно смотреть на них как на макросы в Лиспе(что?).
-- В том же Coq люди почти не пишут программы, а пишут тактики, которые генерируют программы
-- В агде вроде что-то завезли, есть некоторый рефлекшн, но вот документации к этому делу нет =(
-- Поэтому, если ты пишешь на агде и хочешь воспользоваться тактиками, то скорее всего ты выбрал не тот язык

-- 2. Коиндукция. Чуваки сами не знают, что с ней делать. Поэтому не очень подробно
-- Коиндуктивный тип - это те типы, которые мы объявляем с помощью data в хаскеле

-- тип бесконечных списков. Заметим, что он пустой, потому что есть некоторые проблемы с завершаемостью
data Stream (A : Set) : Set where
    cons : A → Stream A → Stream A

Stream-isEmpty : {A : Set} → Stream A → ⊥
Stream-isEmpty (cons x s) = Stream-isEmpty s

-- нормальный тип для бесконечного списка
-- у коиндуктивных типов есть деструктор, то есть он принимает какие-то элементы нашего типа и деструктурирует его
-- например коиндуктивный список можно деструктурировать на голову и хвост
record Stream' (A : Set) : Set where
    coinductive
    field
        head : A
        tail : Stream' A

-- копаттерны
record Point : Set where
    field
        getX : ℕ
        getY : ℕ

open Point

shift : Point → Point
shift p = record {getX = suc (Point.getX p); getY = suc (Point.getY p)}

-- диковатый синтаксис
shift' : Point → Point
getX (shift' p) = suc (getX p)
getY (shift' p) = suc (getY p)

open Stream'
-- то есть мы как бы пишем слева то, как выглядит результат
stream-map : {A B : Set} → (A → B) → Stream' A → Stream' B
head (stream-map f xs) = f (head xs)
tail (stream-map f xs) = stream-map f (tail xs)

{-
-- числа Фиббоначи, как бесконечный список
zipWith : {A B C : Set} → (A → B → C) → Stream' A → Stream' B → Stream' C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

-- и вот тут мы просядем, потому что терминейшн чекер не поймет, что последняя строчка завершается
fib : Stream' ℕ
head fib = 1
head (tail fib) = 1
tail (tail fib) = zipWith (_+_) fib (tail fib)
-}

-- 3. Индуктивное определение предикатов

-- равенство в логике - мощная штука, которая позволяет выразить через него много вещей
_<='_ : ℕ → ℕ → Set
n <=' k = Σ ℕ (λ x → n + x ≡ k)

-- заметим, что рекурсивное определение работает только для индуктивных типов данных
_<=_ : ℕ → ℕ → Bool
0 <= _ = true
suc _ <= 0 = false
suc n <= suc m = n <= m

-- теперь определим его индуктивно
data _≤_  : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → 0 ≤ n
    s≤s : {n k : ℕ} → n ≤ k → suc n ≤ suc k

-- и это не единственный способ!
data _≤'_  : ℕ → ℕ → Set where
    ≤'-refl : {n : ℕ} → n ≤' n
    ≤'-step : {n k : ℕ} → n ≤' k → n ≤' suc k

-- докажем, что они эквивалентны. В одну сторону. Примеры в лекции
z≤'n : {n : ℕ} → 0 ≤' n
z≤'n {zero} = ≤'-refl
z≤'n {suc n} = ≤'-step z≤'n

s≤'s : {n k : ℕ} → n ≤' k → suc n ≤' suc k
s≤'s ≤'-refl = ≤'-refl
s≤'s (≤'-step p) = ≤'-step (s≤'s p)

≤-≤' : {n k : ℕ} → n ≤ k → n ≤' k
≤-≤' z≤n = z≤'n
≤-≤' (s≤s p) = s≤'s (≤-≤' p)

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-step : {n k : ℕ} → n ≤ k → n ≤ suc k
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤'-≤ : {n k : ℕ} → n ≤' k → n ≤ k
≤'-≤ (≤'-refl) = ≤-refl
≤'-≤ (≤'-step p) = ≤-step (≤'-≤ p)

-- 2. Предикат ``домен функции''

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc n < suc k = n < k

-- div'' : ℕ → ℕ → ℕ
-- div'' n k = if n < k then 0 else suc (div'' (n ∸ k) k)

data div-dom (n k : ℕ) : Set where
  lt : T (n < k) → div-dom n k
  geq : ¬ (T (n < k)) → div-dom (n ∸ k) k → div-dom n k

div' : {n k : ℕ} → div-dom n k → ℕ
div' (lt x) = 0
div' (geq x p) = suc (div' p)

div-dom-pos : (n k : ℕ) → div-dom n k → ¬ (k ≡ 0)
div-dom-pos n zero (lt ())
div-dom-pos n (suc k) (lt x) = λ ()
div-dom-pos n k (geq x p) = div-dom-pos (n ∸ k) k p

{-
div-dom-desc : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
div-dom-desc _ zero p = ⊥-elim (p refl)
div-dom-desc zero (suc k) p = lt tt
div-dom-desc (suc n) (suc k) p with div-dom-desc n k {!!}
div-dom-desc (suc n) (suc k) p | lt x = lt x
div-dom-desc (suc n) (suc k) p | geq x r = geq x {!!}
-}

{-
div-dom-desc : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
div-dom-desc _ zero p = ⊥-elim (p refl)
div-dom-desc zero (suc k) p = lt tt
div-dom-desc (suc n) (suc k) p with div-dom-desc n (suc k) p
div-dom-desc (suc n) (suc k) p | lt x = {!!}
div-dom-desc (suc n) (suc k) p | geq x r = geq {!!} {!!}
-}

{-
<-Dec : (n k : ℕ) → Dec (T (n < k))
<-Dec n k = {!!}

div-dom-desc : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
div-dom-desc n k p with <-Dec n k
div-dom-desc n k p₁ | yes p = lt p
div-dom-desc n k p | no ¬p = geq ¬p {!!}
-}

-- 3. Принципы индукции.

{-
f : (x : ℕ) → P x
f 0 = ? : P 0
f (suc n) = ? : P n → P (suc n)
-}

ℕ-ind : (P : ℕ → Set) → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
ℕ-ind P z s 0 = z
ℕ-ind P z s (suc n) = s n (ℕ-ind P z s n)

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

fac' = ℕ-ind (λ _ → ℕ) 1 (λ n r → suc n * r)

ℕ-<-ind : (P : ℕ → Set) → ((n : ℕ) → ((k : ℕ) → T (k < n) → P k) → P n) → (n : ℕ) → P n
ℕ-<-ind P h n = {!!}

<-trans : (x y z : ℕ) → T (x < y) → T (y < z) → T (x < z)
<-trans zero zero zero () q
<-trans zero zero (suc z) () q
<-trans zero (suc y) zero p ()
<-trans zero (suc y) (suc z) p q = tt
<-trans (suc x) zero zero p ()
<-trans (suc x) zero (suc z) () q
<-trans (suc x) (suc y) zero p ()
<-trans (suc x) (suc y) (suc z) p q = <-trans x y z p q

<-step : (x : ℕ) → T (x < suc x)
<-step zero = tt
<-step (suc x) = <-step x

∸-lem' : (n k : ℕ) → T ((n ∸ k) < suc n)
∸-lem' zero zero = tt
∸-lem' zero (suc k) = tt
∸-lem' (suc n) zero = <-step n
∸-lem' (suc n) (suc k) = <-trans (n ∸ k) (suc n) (suc (suc n)) (∸-lem' n k) (<-step n)

∸-lem : (n k : ℕ) → ¬ k ≡ 0 → false ≡ (n < k) → T ((n ∸ k) < n)
∸-lem zero zero p q = p refl
∸-lem zero (suc k) p ()
∸-lem (suc n) zero p q = ⊥-elim (p refl)
∸-lem (suc n) (suc k) p q = ∸-lem' n k

div : ℕ → (k : ℕ) → ¬ (k ≡ 0) → ℕ
div n k p = ℕ-<-ind (λ _ → ℕ) (λ n' → div-lem n' (n' < k) refl) n
  where
    div-lem : (n' : ℕ) (b : Bool) → b ≡ (n' < k) → ((k : ℕ) → T (k < n') → ℕ) → ℕ
    div-lem n' true _ _ = 0
    div-lem n' false q h = suc (h (n' ∸ k) (∸-lem n' k p q))

-- 4. Sorted lists.

module Sorted (A : Set) (_≤_ : A → A → Set) where
  leqHead : A → List A → Set
  leqHead _ [] = ⊤
  leqHead x (y ∷ _) = x ≤ y

  isSorted : List A → Set
  isSorted [] = ⊤
  isSorted (x ∷ xs) = leqHead x xs × isSorted xs

  data isSorted' : List A → Set where
    nil : isSorted' []
    cons : (x : A) (xs : List A) → leqHead x xs → isSorted' xs → isSorted' (x ∷ xs)

  isSorted-isSorted' : (xs : List A) → isSorted xs → isSorted' xs
  isSorted-isSorted' xs p = {!!}

  isSorted'-isSorted : {xs : List A} → isSorted' xs → isSorted xs
  isSorted'-isSorted p = {!!}

data isPerm {A : Set} : List A → List A → Set where
  nil : isPerm [] []
  cons : (x : A) (xs ys ys₁ ys₂ : List A) → ys ≡ ys₁ ++ x ∷ ys₂ → isPerm xs (ys₁ ++ ys₂) → isPerm (x ∷ xs) ys

module Sort (A : Set) (_≤_ : A → A → Bool) (L : (x y : A) → T (x ≤ y) ⊎ T (y ≤ x)) where
  open Sorted A (λ x y → T (x ≤ y))

  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ ys) = if x ≤ y then x ∷ y ∷ ys else y ∷ insert x ys

  sort : List A → List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

  isSorted'-head : {x : A} {xs : List A} → isSorted' (x ∷ xs) → leqHead x xs
  isSorted'-head (cons _ _ p _) = p

  isSorted'-tail : {x : A} {xs : List A} → isSorted' (x ∷ xs) → isSorted' xs
  isSorted'-tail (cons _ _ _ p) = p

  insert-isSorted' : (x : A) (xs : List A) → isSorted' xs → isSorted' (insert x xs)
  insert-isSorted' x [] p = cons x [] tt nil
  insert-isSorted' x (x₁ ∷ xs) p = lem (x ≤ x₁) refl
    where
      lem'' : (x y : A) → false ≡ (x ≤ y) → T (y ≤ x)
      lem'' x y p with L x y
      ... | inj₁ q = ⊥-elim (subst T (sym p) q)
      ... | inj₂ q = q

      lem' : (x y : A) (xs : List A) → false ≡ (x ≤ y) → leqHead y xs → leqHead y (insert x xs)
      lem' x₂ y [] p₁ q = lem'' x₂ y p₁
      lem' x₂ y (x₃ ∷ xs₁) p₁ q with x₂ ≤ x₃
      ... | true = lem'' x₂ y p₁
      ... | false = q

      lem : (b : Bool) → b ≡ (x ≤ x₁) → isSorted' (if b then x ∷ x₁ ∷ xs else x₁ ∷ insert x xs)
      lem false p₁ = cons x₁ (insert x xs) (lem' x x₁ xs p₁ (isSorted'-head p)) (insert-isSorted' x xs (isSorted'-tail p))
      lem true p₁ = cons x (x₁ ∷ xs) (subst T p₁ tt) p

  sort-isSorted' : (xs : List A) → isSorted' (sort xs)
  sort-isSorted' [] = nil
  sort-isSorted' (x ∷ xs) = insert-isSorted' x (sort xs) (sort-isSorted' xs)

  sort-isPerm : (xs : List A) → isPerm xs (sort xs)
  sort-isPerm xs = {!!}

-- 5. Индукция-рекурсия, вселенные.

f : ℕ → ℕ
g : (x : ℕ) → f x ≡ f x → ℕ

f 0 = 0
f (suc n) = g n refl

g 0 _ = 0
g (suc n) _ = f (suc n)

mutual
  data U : Set where
    nat : U
    bool : U
    pi : (A : U) → (El A → U) → U
    sigma : (A : U) → (El A → U) → U

  El : U → Set
  El nat = ℕ
  El bool = Bool
  El (pi A B) = (a : El A) → El (B a)
  El (sigma A B) = Σ (El A) (λ a → El (B a))

id : (A : U) → El A → El A
id A x = x

-- 6. Тип сортированных списков.

module SortedList'' (A : Set) (_≤_ : A → A → Set) where
  mutual
    data SortedList : Set where
      nil : SortedList
      cons : (x : A) (xs : SortedList) → leqHead x xs → SortedList

    leqHead : A → SortedList → Set
    leqHead _ nil = ⊤
    leqHead x (cons y _ _) = x ≤ y

module SortedList' (A : Set) (_≤_ : A → A → Set) where
  mutual
    data SortedList : Set where
      nil : SortedList
      cons : (x : A) (xs : SortedList) → leqHead x xs → SortedList

    data leqHead (x : A) : SortedList → Set where
      nil : leqHead x nil
      cons : (y : A) (ys : SortedList) (p : leqHead y ys) → x ≤ y → leqHead x (cons y ys p)
