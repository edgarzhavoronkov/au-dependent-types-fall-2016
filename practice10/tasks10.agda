{-# OPTIONS --without-K #-}

module tasks10 where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_)
open import lect10

-- 1. Докажите, что (n + m)-элементное множество равно размеченному объединению n- и m-элементного.

f : (n m : ℕ) → Fin (n + m) → Fin n ⊎ Fin m
f zero m x = inj₂ x
f (suc n) m zero = inj₁ zero
f (suc n) m (suc x) with f n m x
f (suc n) m (suc x₁) | inj₁ x = inj₁ (suc x)
f (suc n) m (suc x) | inj₂ y = inj₂ y

g : (n m : ℕ) → Fin n ⊎ Fin m → Fin (n + m)
g n m (inj₁ x) = inject+ m x
g n m (inj₂ y) = raise n y

Fin-sum : (n m : ℕ) → Fin (n + m) ≡ (Fin n ⊎ Fin m)
Fin-sum n m = SetExt (f n m , g n m , proof₁ n m , proof₂ n m)
    where
        proof₁ : (n m : ℕ) → (x : Fin (n + m)) → g n m (f n m x) ≡ x
        proof₁ zero m x = refl
        proof₁ (suc n) m zero = refl
        proof₁ (suc n) m (suc x) with {!   !}
        proof₁ (suc n) m (suc x) | res = {!   !}

        proof₂ : (n m : ℕ) → (y : Fin n ⊎ Fin m) → f n m (g n m y) ≡ y
        proof₂ n m (inj₁ x) = {!   !}
        proof₂ n m (inj₂ y) = {!   !}

-- 2. Докажите, что тип равенств между множествами хоть и не является утверждением, но является множеством.

-- postulate
--     SmallTypesAreSets : (A : Set) → isSet A -- просто, чтобы чуть упростить конструкции.

Set-isGpd : (A B : Set) → isSet (A ≡ B)
Set-isGpd A B = subst isSet (sym strong-SetExt) (lm {!   !})
    where
        Sa : isSet A
        Sa = SmallTypesAreSets A

        Sb : isSet B
        Sb = SmallTypesAreSets B

        lm : isSet (Bij A B) → isSet (Lift (Bij A B))
        lm Sbij = {!   !}

-- 3. Докажите, что аксиома K не выполняется для множеств.

K : ∀ {l} → Set l → Set l
K A = (a : A) (p : a ≡ a) → p ≡ refl

K-is-false : K Set → ⊥
K-is-false k = {! !}

-- 4. Докажите, что inv является обратным к **.

inv-left : {A : Set} {x y : A} (p : x ≡ y) → inv p ** p ≡ idp
inv-left refl = refl

inv-right : {A : Set} {x y : A} (p : x ≡ y) → p ** inv p ≡ idp
inv-right refl = refl

-- 5. Для любого группоида A постройте группу автоморфизмов его элемента a : A.

record Group (A : Set) : Set where
  field
    set : isSet A
    id : A
    _&_ : A → A → A
    ginv : A → A
    assoc : {x y z : A} → (x & y) & z ≡ x & (y & z)
    id-left : {x : A} → id & x ≡ x
    id-right : {x : A} → x & id ≡ x
    ginv-left : {x : A} → ginv x & x ≡ id
    ginv-right : {x : A} → x & ginv x ≡ id

aut : {A : Set} → isGpd A → (a : A) → Group (a ≡ a)
aut Ga a = record
        { set = Ga a a
        ; id = idp
        ; _&_ = _**_
        ; ginv = inv
        ; assoc = λ {x} {y} {z} → **-assoc x y z
        ; id-left = idp-left _
        ; id-right = idp-right _
        ; ginv-left = λ {x} → inv-left x
        ; ginv-right = λ {x} → inv-right x
        }

-- 6. Докажите, что множество автоморфизмов 2-х элементного множества состоит из двух элементов.

data Bool₁ : Set₁ where
  true false : Bool₁

from : (Bool ≡ Bool) → Bool₁
from p = if (≡-fun p true) then true else false

to : Bool₁ → Bool ≡ Bool
to true = refl
to false = SetExt (not , (not , (not-not , not-not)))

aut-Bool : (Bool ≡ Bool) ≡ Bool₁
aut-Bool = SetExt (from , to , to-from , from-to)
    where
        to-from : (x : Bool ≡ Bool) → to (from x) ≡ x
        to-from x with from x
        to-from x | true =  {!  !}
        to-from x | false = {!   !}

        from-to : (x : Bool₁) → from (to x) ≡ x
        from-to true = refl
        from-to false = {!   !}

-- 7. Докажите, что группа автоморфизмов в общем случае не коммутативна.

_**'_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p **' refl = p

aut-is-not-comm : ((A : Set) (p q : A ≡ A) → p **' q ≡ q **' p) → ⊥
aut-is-not-comm = {!  !}

-- 8. Докажите, что isProp является предикатом.

isProp-isProp : {A : Set} → isProp (isProp A)
isProp-isProp = {!  !}
