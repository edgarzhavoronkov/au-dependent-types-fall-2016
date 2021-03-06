{-# OPTIONS --without-K #-}

module tasks10 where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_)
open import lect10

-- 1. Докажите, что (n + m)-элементное множество равно размеченному объединению n- и m-элементного.

f-helper : (n m : ℕ) → Fin n ⊎ Fin m → Fin (suc n) ⊎ Fin m
f-helper n m (inj₁ x) = inj₁ (suc x)
f-helper n m (inj₂ y) = inj₂ y

f : (n m : ℕ) → Fin (n + m) → Fin n ⊎ Fin m
f zero m x = inj₂ x
f (suc n) m zero = inj₁ zero
f (suc n) m (suc x) = f-helper n m (f n m x)

g : (n m : ℕ) → Fin n ⊎ Fin m → Fin (n + m)
g n m (inj₁ x) = inject+ m x
g n m (inj₂ y) = raise n y

Fin-sum : (n m : ℕ) → Fin (n + m) ≡ (Fin n ⊎ Fin m)
Fin-sum n m = SetExt (f n m , g n m , proof₁ n m , proof₂ n m)
    where
        proof₁ : (n m : ℕ) → (x : Fin (n + m)) → g n m (f n m x) ≡ x
        proof₁ zero m x = refl
        proof₁ (suc n) m zero = refl
        proof₁ (suc n) m (suc x) = helper (f n m x) refl
            where
                helper : (y : Fin n ⊎ Fin m) → y ≡ f n m x → g (suc n) m (f-helper n m y) ≡ suc x
                helper (inj₁ x₁) p =
                    let t = proof₁ n m x
                    in cong suc (trans (cong (g n m) p) t)
                helper (inj₂ y) p =
                    let t = proof₁ n m x
                    in cong suc (trans (cong (g n m) p) t)

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

D' : Bool → Set
D' true = ⊥
D' false = ⊤


K-is-false : K Set → ⊥
K-is-false k =
    let
        p = SetExt (not , not , not-not , not-not)
        t = k Bool p
        f = not
        g = ≡-fun {A = Bool} refl
        wtf = cong-app {A = Bool} {B = λ _ → Bool} {f = f} {g = g} {!   !} true
    in subst D' wtf tt

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
  true₁ false₁ : Bool₁

from : (Bool ≡ Bool) → Bool₁
from p with ≡-fun p true
from p | true = true₁
from p | false = false₁

to : Bool₁ → Bool ≡ Bool
to true₁ = refl
to false₁ = SetExt (not , not , not-not , not-not)


aut-Bool : (Bool ≡ Bool) ≡ Bool₁
aut-Bool = SetExt (from , to , to-from , from-to)
    where
        to-from : (x : Bool ≡ Bool) → to (from x) ≡ x
        to-from x = {!   !}

        from-to : (x : Bool₁) → from (to x) ≡ x
        from-to true₁ = refl
        from-to false₁ = {!   !}

-- 7. Докажите, что группа автоморфизмов в общем случае не коммутативна.

_**'_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p **' refl = p

data Three : Set where
  one : Three
  two : Three
  three : Three

p : Three → Three
p one = two
p two = three
p three = one

p-inv : Three → Three
p-inv one = three
p-inv two = one
p-inv three = two

q : Three → Three
q one = one
q two = three
q three = two

q-inv : Three → Three
q-inv one = one
q-inv two = three
q-inv three = two

p-pinv : (t : Three) → p (p-inv t) ≡ t
p-pinv one = refl
p-pinv two = refl
p-pinv three = refl

pinv-p : (t : Three) → p-inv (p t) ≡ t
pinv-p one = refl
pinv-p two = refl
pinv-p three = refl

q-qinv : (t : Three) → q (q-inv t) ≡ t
q-qinv one = refl
q-qinv two = refl
q-qinv three = refl

qinv-q : (t : Three) → q-inv (q t) ≡ t
qinv-q one = refl
qinv-q two = refl
qinv-q three = refl

p-Bij : Bij Three Three
p-Bij = p , p-inv , pinv-p , p-pinv

q-Bij : Bij Three Three
q-Bij = q , q-inv , qinv-q , q-qinv

p-eq : Three ≡ Three
p-eq = SetExt p-Bij

q-eq : Three ≡ Three
q-eq = SetExt q-Bij

-- cong-app (cong ≡-fun p) one : ≡-fun (p-eq **' q-eq) one ≡ ≡-fun (q-eq **' p-eq) one
confuse : (p-eq **' q-eq ≡ q-eq **' p-eq) → (x : Three) → (≡-fun (p-eq **' q-eq) x ≡ ≡-fun (q-eq **' p-eq) x)
confuse p = cong-app (cong ≡-fun p)

confuse' : (x : Three) → ≡-fun (p-eq **' q-eq) x ≡ p (q x)
confuse' one = {!   !}
confuse' two = {!   !}
confuse' three = {!   !}

confuse'' : (x : Three) → ≡-fun (q-eq **' p-eq) x ≡ q (p x)
confuse'' one = {!   !}
confuse'' two = {!   !}
confuse'' three = {!   !}

D : Three → Set
D one = ⊤
D two = ⊤
D three = ⊥

aut-is-not-comm : ((A : Set) (p q : A ≡ A) → p **' q ≡ q **' p) → ⊥
aut-is-not-comm p =
    let
        t = p Three p-eq q-eq
        t' = confuse t one
        t'' = trans (trans (sym (confuse' one)) t') (confuse'' one)
    in subst D t'' tt

-- 8. Докажите, что isProp является предикатом.

isProp-isProp : {A : Set} → isProp (isProp A)
isProp-isProp = {!  !}
