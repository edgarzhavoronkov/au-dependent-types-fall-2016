module tasks06 where

open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.List hiding (filter)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty

-- 1. Реализуйте любой алгоритм сортировки, используя with для паттерн матчинга на результате сравнения элементов списка.
-- if (x < y) then (cons y (insert x ys)) else (cons x (cons y ys))

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc x < suc y = x < y

insert : ℕ → List ℕ → List ℕ
insert x [] = x ∷ []
insert x (y ∷ ys) with (x < y)
... | true = y ∷ (insert x ys)
... | false = x ∷ y ∷ ys

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

-- 2. Определите filter через if, а не через with.
--    Докажите для этой версии filter следующую лемму:

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ (filter p xs) else filter p xs

lem : {A : Set} (p : A → Bool) (xs : List A) → length (filter p xs) ≤ length xs
lem p [] = z≤n
lem p (x ∷ xs) with p x
... | true = s≤s (lem p xs)
... | false = ≤-step (lem p xs)

-- 3. Докажите, что если равенство элементов A разрешимо, то и равенство элементов List A тоже разрешимо.

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

foo : {A : Set} → (x y : A) → (xs ys : List A) → x ∷ xs ≡ y ∷ ys → x ≡ y
foo x .x xs .xs refl = refl

bar : {A : Set} → (x y : A) → (xs ys : List A) → x ∷ xs ≡ y ∷ ys → xs ≡ ys
bar x .x xs .xs refl = refl

List-Dec : {A : Set} → DecEq A → DecEq (List A)
List-Dec P [] [] = yes refl
List-Dec P [] (x ∷ xs) = no (λ ())
List-Dec P (x ∷ xs) [] = no (λ ())
List-Dec P (x ∷ xs) (y ∷ ys) with List-Dec P xs ys
List-Dec P (x ∷ xs) (y ∷ ys) | yes p with P x y
List-Dec P (x ∷ xs) (y ∷ ys) | yes p₁ | yes p = yes (cong₂ _∷_ p p₁)
List-Dec P (x ∷ xs) (y ∷ ys) | yes p | no q = no (λ x₁ → q (foo x y xs ys x₁))
List-Dec P (x ∷ xs) (y ∷ ys) | no q = no (λ x₁ → q (bar x y xs ys x₁))

-- 4. Докажите, что предикат isEven разрешим.

DecPred : {A : Set} → (A → Set) → Set
DecPred {A} P = (a : A) → Dec (P a)

isEven : ℕ → Set
isEven n = Σ ℕ (λ k → n ≡ k * 2)

suc≠ : (n m : ℕ) → suc (n * 2) ≡ (m * 2) → ⊥
suc≠ zero zero ()
suc≠ zero (suc m) ()
suc≠ (suc n) zero ()
suc≠ (suc n) (suc m) p = suc≠ n m (cong (λ x → pred (pred x)) p)

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even 0
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)

isEven-Dec : DecPred isEven
isEven-Dec n with parity n
isEven-Dec .(k * 2) | even k = yes (k , refl)
isEven-Dec .(suc (k * 2)) | odd k = no (λ x → suc≠ k (proj₁ x) (proj₂ x))

-- 5. Докажите, что если равенство элементов A разрешимо, то любой список элементов A либо пуст, либо состоит из повторений одного элемента, либо в A существует два различных элемента.

repeat : {A : Set} → ℕ → A → List A
repeat zero a = []
repeat (suc n) a = a ∷ repeat n a

data Result (A : Set) (xs : List A) : Set where
  empty : xs ≡ [] → Result A xs
  repeated : (n : ℕ) (a : A) → xs ≡ repeat n a → Result A xs
  A-is-not-trivial : (a a' : A) → ¬ (a ≡ a') → Result A xs

lemma : {A : Set} (xs : List A) → DecEq A → Result A xs
lemma [] P = empty refl
lemma (x ∷ xs) P with lemma xs P
lemma (x₁ ∷ .[]) P | empty refl = repeated 1 x₁ refl
lemma (x₁ ∷ .(repeat n a)) P | repeated n a refl with P x₁ a
lemma (x₁ ∷ .(repeat n a)) P | repeated n a refl | yes p = repeated (suc n) a (cong (λ x → x ∷ (repeat n a)) p)
lemma (x₁ ∷ .(repeat n a)) P | repeated n a refl | no q = A-is-not-trivial x₁ a q
lemma (x₁ ∷ xs) P | A-is-not-trivial a a' x with P x₁ a | P x₁ a'
lemma (x₁ ∷ xs) P | A-is-not-trivial a a' x | yes p | yes p₁ = A-is-not-trivial a a' x
lemma (x₁ ∷ xs) P | A-is-not-trivial a a' x | yes p | no q = A-is-not-trivial x₁ a' q
lemma (x₁ ∷ xs) P | A-is-not-trivial a a' x | no q | yes p = A-is-not-trivial x₁ a q
lemma (x₁ ∷ xs) P | A-is-not-trivial a a' x | no q | no q₁ = A-is-not-trivial a a' x

-- 6. Определите view, представляющий число в виде частного и остатка от деления его на произвольное (неотрицательное) число m.
--    Реализуйте функцию деления.

data ModView (m : ℕ) : ℕ → Set where
  quot-rem : ∀ q r → T (r < m) → ModView m (r + q * m)

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

mod-view : (m n : ℕ) → T (isPos m) → ModView m n
mod-view = {! !}

div : ℕ → (m : ℕ) → T (isPos m) → ℕ
div n m p = {! !}
