{-# OPTIONS --without-K #-}

module tasks08 where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Relation.Nullary

-- 1. Определите функтор State.

postulate
  funExt : {A : Set} {B : A → Set} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B

    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) →
      fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

State : Set → Set → Set
State S A = S → S × A

State-Functor : (S : Set) → Functor (State S)
State-Functor S = record
    {
        fmap = λ f sa x → (proj₁ (sa x)) , f (proj₂ (sa x)) ;
        fmap-id = λ a → refl ;
        fmap-comp = λ f g a → refl
    }

-- 2. Пусть f : A → B и g : B → C ─ некоторые функции.
--    Докажите, что если f и g инъективны, то g ∘ f также инъективна.
--    Докажите, что если g ∘ f инъективна, то f также инъективна.

isInj : {A B : Set} → (A → B) → Set
isInj {A} {B} f = (x x' : A) → f x ≡ f x' → x ≡ x'

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

∘-inj : {A B C : Set} (f : A → B) (g : B → C) → isInj f → isInj g → isInj (g ∘ f)
∘-inj f g p q = λ x x' z → p x x' (q (f x) (f x') z)

∘-inj' : {A B C : Set} (f : A → B) (g : B → C) → isInj (g ∘ f) → isInj f
∘-inj' f g p = λ x x' x₁ → p x x' (cong g x₁)

-- 3. Определите предикат "делится на 3 или на 5" так, чтобы он возвращал утверждения.
--    Докажите, что MultipleOf3Or5 вкладывается в ℕ.

isProp : Set → Set
isProp A = (x y : A) → x ≡ y

isMultipleOf3 : ℕ → Bool
isMultipleOf3 0 = true
isMultipleOf3 1 = false
isMultipleOf3 2 = false
isMultipleOf3 (suc (suc (suc n))) = isMultipleOf3 n

isMultipleOf5 : ℕ → Bool
isMultipleOf5 0 = true
isMultipleOf5 1 = false
isMultipleOf5 2 = false
isMultipleOf5 3 = false
isMultipleOf5 4 = false
isMultipleOf5 (suc (suc (suc (suc (suc n))))) = isMultipleOf5 n

isMultipleOf3Or5 : ℕ → Set
isMultipleOf3Or5 n = T ((isMultipleOf3 n) ∨ (isMultipleOf5 n))

-- 5. Докажите, что T является утверждением.

T-isProp : (x : Bool) → isProp (T x)
T-isProp true x y = refl
T-isProp false x ()

isMultipleOf3Or5-isProp : (n : ℕ) → isProp (isMultipleOf3Or5 n)
isMultipleOf3Or5-isProp n = T-isProp ((isMultipleOf3 n) ∨ (isMultipleOf5 n))

record MultipleOf3Or5 : Set where
    constructor ismult
    field
        number : ℕ
        proof : isMultipleOf3Or5 number

MultipleOf3Or5-inj : isInj MultipleOf3Or5.number
MultipleOf3Or5-inj (ismult number proof) (ismult .number proof₁) refl = cong (ismult number) (isMultipleOf3Or5-isProp number proof proof₁)

-- 4. Мы будем говорить, что тип A тривиален, если существует элемент в A, такой что любой другой элемент в A равен ему.
--    Докажите, что тип A тривиален тогда и только тогда, когда A является утверждением и A населен.

isTriv : Set → Set
isTriv A = Σ A (λ x → (y : A) → x ≡ y)

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (Q → P)

isTriv→isProp : {A : Set} → isTriv A → (isProp A) × A
isTriv→isProp (proj₁ , proj₂) = (λ x y → trans (sym (proj₂ x)) (proj₂ y)) , proj₁

isProp→isTriv : {A : Set} → (isProp A) × A → isTriv A
isProp→isTriv (proj₁ , proj₂) = proj₂ , (proj₁ proj₂)

isTriv-lem : (A : Set) → isTriv A ↔ (isProp A × A)
isTriv-lem A = isTriv→isProp , isProp→isTriv

-- 6. Докажите, что ≤ является предикатом.

≤-isProp : {n m : ℕ} → isProp (n ≤ m)
≤-isProp z≤n z≤n = refl
≤-isProp (s≤s p) (s≤s q) = cong s≤s (≤-isProp p q)

-- 7. Докажите, что <=' не является предикатом.

data _<='_ : ℕ → ℕ → Set where
  z<='n : {n : ℕ} → 0 <=' n
  <='refl : {n : ℕ} → n <=' n
  s<='s : {n m : ℕ} → n <=' m → suc n <=' suc m

<='-refl : ((n m : ℕ) → isProp (n <=' m)) → ⊥
<='-refl p = lem (p zero zero z<='n <='refl)
    where
        lem : z<='n ≡ <='refl → ⊥
        lem ()

-- 8. Докажите, что если тип A вкладывается в тип B и B является утверждением, то и A является утверждением.

sub-isProp : {A B : Set} (f : A → B) → isInj f → isProp B → isProp A
sub-isProp = λ {A} {B} f z z₁ x y → z x y (z₁ (f x) (f y))

-- 9. Докажите, что рекурсивно определенное равенство списков является предикатом.

record hProp : Set₁ where
  field
    A : Set
    prop : isProp A

eq : {A : Set} (_==_ : A → A → hProp) → List A → List A → Set
eq _ [] [] = ⊤
eq _ [] (_ ∷ _) = ⊥
eq _ (_ ∷ _) [] = ⊥
eq _==_ (x ∷ xs) (y ∷ ys) = hProp.A (x == y) × eq _==_ xs ys

eq-isProp : {A : Set} (_==_ : A → A → hProp) (xs ys : List A) → isProp (eq _==_ xs ys)
eq-isProp _==_ xs ys x y = {!   !}

eq-Prop : {A : Set} (_==_ : A → A → hProp) → List A → List A → hProp
eq-Prop _==_ xs ys = record { A = eq _==_ xs ys ; prop = eq-isProp _==_ xs ys }

-- 10. Докажите, что Σ не является утверждением в общем случае.

∃-isProp : ({A : Set} {B : A → hProp} → isProp (Σ A (λ x → hProp.A (B x)))) → ⊥
∃-isProp = {!  !}

-- 11. Докажите, что если для всех x : A верно, что B x является множеством, то (x : A) → B x также является множеством.

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

Π-isSet : {A : Set} {B : A → Set} → ((x : A) → isSet (B x)) → isSet ((x : A) → (B x))
Π-isSet = {!  !}

-- 12. Докажите, что Σ сохраняет множества.

Σ-isSet : {A : Set} {B : A → Set} → isSet A → ((x : A) → isSet (B x)) → isSet (Σ A B)
Σ-isSet = {!  !}

-- 13. Докажите, что ⊎ сохраняет множества.

⊎-isSet : {A B : Set} → isSet A → isSet B → isSet (A ⊎ B)
⊎-isSet = {!  !}

-- 14. Определите по аналогии с Prop тип типов, являющихся множествами.

-- 15. Закончите доказательство того, что ℕ является множеством.
--     Докажите более общее утверждение, что если равенство элементов типа A разрешимо, то A является множеством.
--     Для доказательства используйте лемму, приведенную ниже (саму лемму доказывать не нужно).

isSet-lem : {A : Set} (R : A → A → hProp) →
  ((x y : A) → x ≡ y → hProp.A (R x y)) →
  ((x y : A) → hProp.A (R x y) → x ≡ y) →
  isSet A
isSet-lem = {!  !}

_==_ : ℕ → ℕ → Bool
0 == 0 = true
0 == suc _ = false
suc _ == 0 = false
suc n == suc m = n == m

==-≡ : (n m : ℕ) → T (n == m) → n ≡ m
==-≡ zero zero p = refl
==-≡ zero (suc m) ()
==-≡ (suc n) zero ()
==-≡ (suc n) (suc m) p = cong suc (==-≡ n m p)

≡-== : (n m : ℕ) → n ≡ m → T (n == m)
≡-== zero zero p = tt
≡-== zero (suc m) ()
≡-== (suc n) zero ()
≡-== (suc n) (suc m) p = ≡-== n m (cong pred p)

ℕ-isSet : isSet ℕ
ℕ-isSet = isSet-lem (λ x y → record { A = T (x == y) ; prop = {!  !} }) ≡-== ==-≡

Hedberg : {A : Set} → ((x y : A) → Dec (x ≡ y)) → isSet A
Hedberg = {!  !}
