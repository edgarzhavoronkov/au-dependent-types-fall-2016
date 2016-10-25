module lect06 where

open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat.Base hiding (_<_; Ordering; compare)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.List hiding (filter; _++_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Vec
open import Data.Product

-- 1. with

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | false = filter p xs
... | true = x ∷ filter p xs

filter' : {A : Set} → (A → Bool) → List A → List A
filter' p [] = []
filter' {A} p (x ∷ xs) = helper (p x)
  where
    helper : Bool → List A
    helper false = filter' p xs
    helper true = x ∷ filter' p xs

-- 2. case в языках с зависимыми типами.

foo : {A : Set} (p : A → Bool) (a : A) → p a ≡ p a
foo p a = helper (p a)
  where
    helper : (b : Bool) → b ≡ b
    helper false = refl
    helper true = refl

foo' : {A : Set} (p : A → Bool) (a : A) → p a ≡ p a
foo' p a with p a
... | false = refl
... | true = refl

bar : {A : Set} (p : A → Bool) (a : A) → p a ≡ p a → p a ≡ p a
bar p a q with p a
... | b = q

lem : {A : Set} (p : A → Bool) (xs : List A) → length (filter p xs) ≤ length xs
lem p [] = z≤n
lem p (x ∷ xs) with p x
lem p (x ∷ xs) | false = ≤-step (lem p xs)
lem p (x ∷ xs) | true = s≤s (lem p xs)

-- filter p (x ∷ xs) = case p x of { ... }

-- length (case p x of { ... }) ≤ length (x ∷ xs)

-- 3. Одновременная абстракция.

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc x < suc y = x < y

-- data Ordering : Set where
--   LT GT EQ : Ordering
--
-- compare : ℕ → ℕ → Ordering
-- compare x y with x < y
-- ...         | false with y < x
-- ...                 | false = EQ
-- ...                 | true = GT
-- compare x y | true = LT
--
-- compare' : ℕ → ℕ → Ordering
-- compare' x y with x < y | y < x
-- compare' x y | false | false = EQ
-- compare' x y | false | true = GT
-- compare' x y | true | _ = LT

-- 4. rewrite

rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev [] = []
rev {A} {suc n} (x ∷ xs) = subst (Vec A) (+-comm n 1) (rev xs ++ x ∷ [])

-- через with
rev' : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev' [] = []
rev' {A} {suc n} (x ∷ xs) with n + 1 | +-comm n 1 | rev' xs ++ x ∷ []
rev' {A} {suc n} (x ∷ xs) | .(suc n) | refl | r = r

-- rev xs ++ x ∷ [] : Vec A (n + 1)

-- через helper
rev'' : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev'' [] = []
rev'' {A} {suc n} (x ∷ xs) = helper (n + 1) (+-comm n 1) (rev'' xs ++ x ∷ [])
  where
    helper : (m : ℕ) → m ≡ suc n → Vec A m → Vec A (suc n)
    helper _ refl r = r

rev'''' : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev'''' [] = []
rev'''' {A} {suc n} (x ∷ xs) with suc n | +-comm 1 n
rev'''' {A} {suc n} (x ∷ xs) | .(n + 1) | refl = rev'''' xs ++ x ∷ []

-- через rewrite
rev''' : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev''' [] = []
rev''' {A} {suc n} (x ∷ xs) rewrite +-comm 1 n = rev''' xs ++ x ∷ []

-- 5. Views.

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even 0
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)

div2 : ℕ → ℕ
div2 n with parity n
div2 .(k * 2) | even k = k
div2 .(suc (k * 2)) | odd k = k

-- 6. Разрешимые равенства и предикаты.

-- A → Set - неразрешимые
-- A → Bool - разрешимые

-- Множество разрешимых предикатов очевидно вкладывается во множество неразрешимых
DP-P : {A : Set} → (A → Bool) → A → Set
DP-P p a = T (p a)

-- Пример неразрешимого предиката
-- p : ℕ → Set
-- p n = "машина Тьюринга с номером n останавливается на входе 0"

isEven : ℕ → Set
isEven n = Σ ℕ (λ k → n ≡ k * 2)

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : (P → ⊥) → Dec P

DecPred : {A : Set} → (A → Set) → Set
DecPred {A} P = (a : A) → Dec (P a)

P-DP : {A : Set} (P : A → Set) → DecPred P → A → Bool
P-DP P d a with d a
P-DP P d a | yes x = true
P-DP P d a | no x = false

DP-Dec : {A : Set} (P : A → Bool) → DecPred (DP-P P)
DP-Dec P a with P a
DP-Dec P a | false = no (λ ())
DP-Dec P a | true = yes tt

DP-P-DP : {A : Set} (P : A → Bool) → (a : A) → P-DP (DP-P P) (DP-Dec P) a ≡ P a
DP-P-DP P a with DP-Dec P a
DP-P-DP P a | yes x with P a
DP-P-DP P a | yes () | false
DP-P-DP P a | yes x | true = refl
DP-P-DP P a | no x with P a
DP-P-DP P a | no x | false = refl
DP-P-DP P a | no x | true = ⊥-elim (x tt)

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

P-DP-P : {A : Set} (P : A → Set) (d : DecPred P) (a : A) → DP-P (P-DP P d) a ↔ P a
P-DP-P P d a = helper₁ , helper₂
  where
    helper₁ : DP-P (P-DP P d) a → P a
    helper₁ p with d a
    helper₁ p | yes x = x
    helper₁ () | no x

    helper₂ : P a → DP-P (P-DP P d) a
    helper₂ p with d a
    helper₂ p | yes _ = tt
    helper₂ p | no q = q p

isEven-Dec : (n : ℕ) → Dec (isEven n)
isEven-Dec n with parity n
isEven-Dec .(k * 2) | even k = yes (k , refl)
isEven-Dec .(suc (k * 2)) | odd k = no (λ x → {! !})

ℕ-Dec : (x y : ℕ) → Dec (x ≡ y)
ℕ-Dec zero zero = yes refl
ℕ-Dec zero (suc y) = no (λ ())
ℕ-Dec (suc x) zero = no (λ ())
ℕ-Dec (suc x) (suc y) with ℕ-Dec x y
ℕ-Dec (suc x) (suc .x) | yes refl = yes refl
ℕ-Dec (suc x) (suc y) | no p = no (λ q → p (cong pred q))
