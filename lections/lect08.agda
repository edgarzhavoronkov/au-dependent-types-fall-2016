module lect08 where

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum

-- Менее очевидные вещи, которые мы возможно видели, но никто не обращал внимания

-- 1. Типы-равенства. Существует типы, для которых естесственное определение равенства не совпадает с равенством, которые
-- получается из наших выкладок

_=='_ : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → Set
_=='_ {A} f g = {x : A} → f x ≡ g x

-- Внезапно, такое определение не эквивалентно ≡. Мы просто не сможем доказать, что такие определения равны
≡-==' : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → f ≡ g → f ==' g
≡-==' f .f refl = refl

-- 2. Есть ключевое слово postulate - аксиома. То есть мы можем постулировать некоторые утверждения, например функциональную экстенсиональность
-- Заметим, что аксиомы ломают вычислимость, так как мы можем вызвать эту функцию без ее определения =(

postulate
    funExt : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → f ==' g → f ≡ g

-- 3. Аксиомы, вычислительность.

-- 4. Моноид функций.

record Monoid (A : Set) : Set where
  field
    id : A
    _&_ : A → A → A
    assoc : (x y z : A) → (x & y) & z ≡ x & (y & z)
    id-left : (x : A) → id & x ≡ x
    id-right : (x : A) → x & id ≡ x

fun-Monoid : {A B : Set} → Monoid B → Monoid (A → B)
fun-Monoid m = let open Monoid m in record
                 { id = λ x → id ;
                   _&_ = λ f g x → f x & g x ;
                   assoc = λ f g h → funExt
                                     (λ x → (f x & g x) & h x)
                                     (λ x → f x & (g x & h x))
                                     (λ x → assoc (f x) (g x) (h x)) ;
                   id-left = λ f → funExt (λ x → id & f x) f (λ x → id-left (f x)) ;
                   id-right = λ f → funExt (λ x → f x & id) f (λ x → id-right (f x)) }

-- 5. Подмножества, инъективные функции.

{-
0 : Even
suc (suc 0) : Even
suc (suc (suc (suc 0))) : Even
-}

isEven : ℕ → Bool
isEven 0 = true
isEven 1 = false
isEven (suc (suc n)) = isEven n

-- { n : ℕ | T (isEven n) }
-- Σ (n : ℕ) (T (isEven n))
-- { n : ℕ | P n }

record Even : Set where
  constructor even
  field
    number : ℕ
    proof : T (isEven number)

Even-inc : Even → ℕ
Even-inc = Even.number

isInj : {A B : Set} → (A → B) → Set
isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y

Even-inc-isInj : isInj Even-inc
Even-inc-isInj (even number proof) (even .number proof₁) refl = {!!}

mod3 : ℕ → ℕ
mod3 0 = 0
mod3 1 = 1
mod3 2 = 2
mod3 (suc (suc (suc n))) = mod3 n

mod5 : ℕ → ℕ
mod5 0 = 0
mod5 1 = 1
mod5 2 = 2
mod5 3 = 3
mod5 4 = 4
mod5 (suc (suc (suc (suc (suc n))))) = mod5 n

record MultipleOf3Or5 : Set where
  constructor mul
  field
    number : ℕ
    proof : mod3 number ≡ 0 ⊎ mod5 number ≡ 0

Mul-inc : MultipleOf3Or5 → ℕ
Mul-inc = MultipleOf3Or5.number

Mul-inc-isInj : isInj Mul-inc
Mul-inc-isInj (mul number proof) (mul .number proof₁) refl = {!!}

-- 6. Утверждения

isProp : Set → Set
isProp A = (x y : A) → x ≡ y

Bool-is-not-Prop : isProp Bool → ⊥
Bool-is-not-Prop p = subst T (p true false) tt

-- 7. Какие предикаты являются настоящими предикатами (то есть возвращают утверждения)?
--    ⊤, ⊥, ∧, ∨, →, ∀, ∃, ≡, рекурсвиные предикаты, индуктивные предикаты.

-- ⊤
⊤-isProp : isProp ⊤
⊤-isProp = λ x y → refl

-- ⊥
⊥-isProp : isProp ⊥
⊥-isProp = λ x ()

_==_ : ℕ → ℕ → Bool
0 == 0 = true
0 == suc _ = false
suc _ == 0 = false
suc n == suc m = n == m

==-isProp : (n m : ℕ) → isProp (T (n == m))
==-isProp zero zero = ⊤-isProp
==-isProp zero (suc m) = ⊥-isProp
==-isProp (suc n) zero = ⊥-isProp
==-isProp (suc n) (suc m) = ==-isProp n m

_==''_ : ℕ → ℕ → Set
0 =='' 0 = ⊤
0 =='' suc _ = ⊥
suc _ =='' 0 = ⊥
suc n =='' suc m = n =='' m

data _<=_ : ℕ → ℕ → Set where
  z<=n : {n : ℕ} → 0 <= n
  s<=s : {n m : ℕ} → n <= m → suc n <= suc m

<=-isProp : {n m : ℕ} → isProp (n <= m)
<=-isProp z<=n z<=n = refl
<=-isProp (s<=s p) (s<=s q) = cong s<=s (<=-isProp p q)

data _<='_ : ℕ → ℕ → Set where
  z<='n : {n : ℕ} → 0 <=' n
  foo : {n : ℕ} → n <=' n
  s<='s : {n m : ℕ} → n <=' m → suc n <=' suc m

record Prop : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

∀-isProp : {A : Set} {B : A → Prop} → isProp ((x : A) → Prop.A (B x))
∀-isProp {A} {B} f g = funExt f g (λ x → Prop.proof (B x) (f x) (g x))

×-isProp : {A B : Set} → isProp A → isProp B → isProp (A × B)
×-isProp p q (a , b) (a' , b') = cong₂ _,_ (p a a') (q b b')

⊎-isProp : ({A B : Set} → isProp A → isProp B → isProp (A ⊎ B)) → ⊥
⊎-isProp p = lem (p ⊤-isProp ⊤-isProp (inj₁ tt) (inj₂ tt))
  where
    lem : {A B : Set} {a : A} {b : B} → inj₁ a ≡ inj₂ b → ⊥
    lem ()

-- ∃-isProp : {A : Set} {B : A → Prop} → isProp (Σ A (λ x → Prop.A (B x)))
-- ∃-isProp = {!!}

-- bar : (f : ℕ → ℕ) → f 0 ≡ f 1 → ℕ
-- bar f p = {!p!}

-- bar : (f : ℕ → ℕ) (x : ℕ) → f x ≡ x → ℕ
-- bar f x p = {!p!}

-- bar : {A : Set} (f : ℕ → A) (n : ℕ) → f n ≡ f n → ℕ
-- bar f n refl = 0

≡-isProp : {A : Set} (x y : A) → isProp (x ≡ y)
≡-isProp x .x refl q = {!!}

-- 6. Множества

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

⊥-isSet : isSet ⊥
⊥-isSet () y p q

-- ⊤-isSet : isSet ⊤
-- ⊤-isSet x .x refl q = {!!}

-- Пока без доказательства
isSet-lem : {A : Set} (R : A → A → Prop) →
  ((x y : A) → x ≡ y → Prop.A (R x y)) →
  ((x y : A) → Prop.A (R x y) → x ≡ y) →
  isSet A
isSet-lem R f g = {!!}

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
ℕ-isSet = isSet-lem (λ n m → prop (T (n == m)) {!!}) ≡-== ==-≡
