module tasks07 where

open import Data.Nat hiding (_≤_)
open import Data.List hiding (filter)
open import Data.Unit hiding (_≤_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum


-- 1. Определите тип бесконечных бинарных деревьев, реализуйте для них функции map и reflect, которая отражает дерево горизонтально.
record InfTree (A : Set) : Set where
    coinductive
    field
        node : A
        left : InfTree A
        right : InfTree A

open InfTree

tree-map : {A B : Set} → (A → B) → InfTree A → InfTree B
node (tree-map f t) = f (node t)
left (tree-map f t) = tree-map f (left t)
right (tree-map f t) = tree-map f (right t)

reflect : {A : Set} → InfTree A → InfTree A
node (reflect t) = node t
left (reflect t) = reflect (right t)
right (reflect t) = reflect (left t)

-- 2. Докажите эквивалентность <= и ≤.

_<=_ : ℕ → ℕ → Bool
0 <= _ = true
suc _ <= 0 = false
suc n <= suc k = n <= k

data _≤'_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → 0 ≤' n
  s≤s : {n k : ℕ} → n ≤' k → suc n ≤' suc k

<=-≤ : (n k : ℕ) → T (n <= k) → n ≤' k
<=-≤ zero zero tt = z≤n
<=-≤ zero (suc k) tt = z≤n
<=-≤ (suc n) zero ()
<=-≤ (suc n) (suc k) p = s≤s (<=-≤ n k p)

≤-<= : {n k : ℕ} → n ≤' k → T (n <= k)
≤-<= z≤n = tt
≤-<= (s≤s p) = ≤-<= p

-- 3. Докажите эквивалентность isSorted и isSorted'.

module Sorted₁ (A : Set) (_≤_ : A → A → Set) where
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
  isSorted-isSorted' [] tt = nil
  isSorted-isSorted' (x ∷ xs) (proj₁ , proj₂) = cons x xs proj₁ (isSorted-isSorted' xs proj₂)

  isSorted'-isSorted : {xs : List A} → isSorted' xs → isSorted xs
  isSorted'-isSorted nil = tt
  isSorted'-isSorted (cons x xs x₁ p) = x₁ , (isSorted'-isSorted p)

-- 4. Определите предикат принадлежности элемента списку.

data _∈_ {A : Set} (a : A) : List A → Set where
    x∈[x] : (xs : List A) → a ∈ (a ∷ xs)
    x∈xs : {y : A} → (ys : List A) → a ∈ ys → a ∈ (y ∷ ys)

-- 5. Определите индуктивно предикат xs ⊆ ys, означающий "список xs является подсписком ys".

data _⊆_ {A : Set} : List A → List A → Set where
    []⊆xs : {xs : List A} → [] ⊆ xs
    -- TODO
    ∷-⊆ : {x y : A} → {xs ys : List A} →


-- 6. Докажите, что filter xs ⊆ xs для любого списка xs.

-- 7*. Докажите следующее утверждение.

data div-dom (n k : ℕ) : Set where
  lt : n < k → div-dom n k
  geq : ¬ (n < k) → div-dom (n ∸ k) k → div-dom n k

pos-div-dom : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
pos-div-dom = {! !}

-- 8*. Докажите следующий принцип индукции.

ℕ-<-ind : (P : ℕ → Set) → ((n : ℕ) → ((k : ℕ) → k < n → P k) → P n) → (n : ℕ) → P n
ℕ-<-ind P h n = {!  !}

-- 9**. Докажите, что алгоритм сортировки, определенный ниже, корректен.
--      Возможно, вам понадобится добавить некоторые предположения о _≤_.

module Sorted₂ (A : Set) (_≤_ : A → A → Set) where
  leqHead : A → List A → Set
  leqHead _ [] = ⊤
  leqHead y (x ∷ _) = y ≤ x

  data isSorted : List A → Set where
    nil : isSorted []
    cons : {x : A} {xs : List A} → leqHead x xs → isSorted xs → isSorted (x ∷ xs)

module Perm (A : Set) where
  data isPerm : List A → List A → Set where
    nil : isPerm [] []
    cons : (x : A) (xs ys ys₁ ys₂ : List A) → isPerm xs (ys₁ ++ ys₂) → ys ≡ ys₁ ++ x ∷ ys₂ → isPerm (x ∷ xs) ys

  -- Вам, возможно, понадобятся эти леммы.
  isPerm-++-left : {xs ys : List A} → isPerm xs ys → (zs : List A) → isPerm (xs ++ zs) (ys ++ zs)
  isPerm-++-left p zs = {!  !}

  isPerm-++-right : {xs ys : List A} (zs : List A) → isPerm xs ys → isPerm (zs ++ xs) (zs ++ ys)
  isPerm-++-right zs p = {!  !}

  isPerm-trans : {xs ys zs : List A} → isPerm xs ys → isPerm ys zs → isPerm xs zs
  isPerm-trans p q = {!  !}

  isPerm-++ : {xs₁ xs₂ ys₁ ys₂ : List A} → isPerm xs₁ ys₁ → isPerm xs₂ ys₂ → isPerm (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  isPerm-++ {xs₁} {xs₂} {ys₁} {ys₂} p q = isPerm-trans (isPerm-++-left p xs₂) (isPerm-++-right ys₁ q)

module Sort (A : Set) (_≤_ : A → A → Bool) where
  open Sorted₂ A (λ x y → T (x ≤ y))
  open Perm A

  filter : (A → Bool) → List A → List A
  filter p [] = []
  filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

  sort : List A → ℕ → List A
  sort _ 0 = []
  sort [] _ = []
  sort (x ∷ xs) (suc n) = sort (filter (λ y → not (x ≤ y)) xs) n ++ x ∷ sort (filter (λ y → x ≤ y) xs) n

  sort-isPerm : (xs : List A) → isPerm xs (sort xs (length xs))
  sort-isPerm = {!  !}

  sort-isSorted : (xs : List A) → isSorted (sort xs (length xs))
  sort-isSorted = {!  !}

-- 10. Определите тип бинарных сортированных деревьев.
--    То есть таких деревьев, в которых для любого узла верно, что все элементы в левом поддереве меньше либо равны, чем значение в узле, которое меньше либо равно, чем все элементы в правом поддереве.
