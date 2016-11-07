{-# OPTIONS --without-K #-}

module lect10 where

open import Data.Nat
open import Data.Sum
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
import Level

-- 1. Равенство типов.

-- _≡_

-- A ⊎ B

ℕ-⊎ : ℕ → ℕ ⊎ ℕ
ℕ-⊎ zero = inj₁ 0
ℕ-⊎ (suc x) with ℕ-⊎ x
... | inj₁ y = inj₂ y
... | inj₂ y = inj₁ (suc y)

-- 2 * x     |-> inj₁ x
-- 2 * x + 1 |-> inj₂ x

⊎-ℕ : ℕ ⊎ ℕ → ℕ
⊎-ℕ (inj₁ x) = x * 2
⊎-ℕ (inj₂ y) = suc (y * 2)

⊎-ℕ-⊎ : (x : ℕ) → ⊎-ℕ (ℕ-⊎ x) ≡ x
⊎-ℕ-⊎ zero = refl
⊎-ℕ-⊎ (suc x) with ℕ-⊎ x | ⊎-ℕ-⊎ x
... | inj₁ y | p = cong suc p
... | inj₂ y | p = cong suc p

ℕ-⊎-ℕ : (x : ℕ ⊎ ℕ) → ℕ-⊎ (⊎-ℕ x) ≡ x
ℕ-⊎-ℕ (inj₁ zero) = refl
ℕ-⊎-ℕ (inj₁ (suc x)) with ℕ-⊎ (x * 2) | ℕ-⊎-ℕ (inj₁ x)
ℕ-⊎-ℕ (inj₁ (suc x)) | inj₁ .x | refl = refl
ℕ-⊎-ℕ (inj₁ (suc x)) | inj₂ y | ()
ℕ-⊎-ℕ (inj₂ zero) = refl
ℕ-⊎-ℕ (inj₂ (suc y)) with ℕ-⊎ (y * 2) | ℕ-⊎-ℕ (inj₂ y)
ℕ-⊎-ℕ (inj₂ (suc y)) | inj₁ .y | refl = refl
ℕ-⊎-ℕ (inj₂ (suc y)) | inj₂ y₁ | ()

Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

isBij : ∀ {l k} {A : Set l} {B : Set k} → (A → B) → Set (l Level.⊔ k)
isBij {_} {_} {A} {B} f = Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))

Bij : ∀ {l k} → Set l → Set k → Set (l Level.⊔ k)
Bij A B = Σ[ f ∶ (A → B) ] (isBij f)

isProp : ∀ {l} → Set l → Set l
isProp A = (x y : A) → x ≡ y

isSet : ∀ {l} → Set l → Set l
isSet A = (x y : A) → isProp (x ≡ y)

postulate
  SmallTypesAreSets : (A : Set) → isSet A -- просто, чтобы чуть упростить конструкции.

-- hSet = Σ[ A ∶ Set ] (isSet A)

≡-fun : ∀ {l} {A B : Set l} → A ≡ B → A → B
≡-fun refl x = x

≡-fun-isBij : ∀ {l} {A B : Set l} (p : A ≡ B) → isBij (≡-fun p)
≡-fun-isBij refl = (λ x → x) , (λ x → refl) , (λ x → refl)

-- theorem : f ≡ g → ((x : A) → f x ≡ g x)
-- axiom   : ((x : A) → f x ≡ g x) → f ≡ g

postulate
  funExt : {A : Set} {B : A → Set} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g

{-
postulate
  SetExt : {A B : Set} → Bij A B → A ≡ B

strong-funExt : {A : Set} {B : A → Set} → ((x : A) → isSet (B x)) →
  (f g : (x : A) → B x) → (f ≡ g) ≡ ((x : A) → f x ≡ g x)
strong-funExt Bs f g = SetExt ((λ p x → cong (λ h → h x) p) ,
  (funExt f g) ,
  (λ x → {!!}) ,
  (λ y → funExt _ _ (λ x → Bs _ _ _ _ _)))
-}

≡-Bij : ∀ {l} {A B : Set l} → A ≡ B → Bij A B
≡-Bij p = ≡-fun p , ≡-fun-isBij p

postulate
  SetUni : ∀ {l} {A B : Set l} → isBij (≡-Bij {l} {A} {B})

SetExt : ∀ {l} {A B : Set l} → Bij A B → A ≡ B
SetExt = proj₁ SetUni

-- A : Set₀
-- B : Set₁
-- A ≡ B

record Lift (A : Set₀) : Set₁ where
  constructor lift
  field
   unlift : A

open Lift

strong-SetExt : {A B : Set} → (A ≡ B) ≡ Lift (Bij A B)
strong-SetExt = SetExt ((λ p → lift (≡-Bij p)) ,
  ((λ p → SetExt (unlift p)) ,
  (proj₁ (proj₂ SetUni)) ,
  (λ y → cong lift (proj₂ (proj₂ SetUni) (unlift y)))))
  -- SetExt (≡-Bij , SetUni)

-- 2. Пример использования SetUni.

-- sort₁, sort₂, isSort sort₁ → isSort sort₂

sort₁ : ℕ → ℕ
sort₁ x = x

sort₂ : ℕ → ℕ
sort₂ x = x

proof' : (x : ℕ) → sort₁ x ≡ sort₂ x
proof' _ = refl

isSort : (ℕ → ℕ) → Set
isSort _ = ⊤

sort₁-isSort : isSort sort₁
sort₁-isSort = tt

sort₂-isSort : isSort sort₂
sort₂-isSort = subst isSort (funExt _ _ proof') sort₁-isSort

-- (x : A) → f x ≡ g x
-- f ≡ g

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

ℕ-DecEq : DecEq ℕ
ℕ-DecEq zero zero = yes refl
ℕ-DecEq zero (suc y) = no (λ())
ℕ-DecEq (suc x) zero = no (λ())
ℕ-DecEq (suc x) (suc y) with ℕ-DecEq x y
... | yes p = yes (cong suc p)
... | no p = no (λ x → p (cong pred x))

ℕ⊎ℕ-DecEq : DecEq (ℕ ⊎ ℕ)
ℕ⊎ℕ-DecEq = subst DecEq (SetExt (ℕ-⊎ , ⊎-ℕ , ⊎-ℕ-⊎ , ℕ-⊎-ℕ)) ℕ-DecEq

lemma : {A B : Set} → Bij A B → DecEq A → DecEq B
lemma (f , g , gf , fg) d x y with d (g x) (g y)
... | yes p = yes (trans (sym (fg x)) (trans (cong f p) (fg y)))
... | no p = no (λ q → p (cong g q))

-- lemma' : (P : Set → Set) {A B : Set} → Bij A B → P A → P B

-- 3. Set не является множеством.

isInj : ∀ {l k} {A : Set l} {B : Set k} → (A → B) → Set (l Level.⊔ k)
isInj {A = A} f = (x y : A) → f x ≡ f y → x ≡ y

isBij-isInj : ∀ {l k} → {A : Set l} {B : Set k} (f : A → B) → isBij f → isInj f
isBij-isInj f (g , p , _) x x' q = trans (sym (p x)) (trans (cong g q) (p x'))

not-not : (x : Bool) → not (not x) ≡ x
not-not true = refl
not-not false = refl

Set-is-not-a-set : isSet Set → ⊥
Set-is-not-a-set f =
  let t₀ = f Bool Bool (SetExt (≡-fun refl , ≡-fun-isBij refl)) (SetExt (not , not , not-not , not-not))
      t₁ = isBij-isInj SetExt (≡-Bij , proj₂ (proj₂ SetUni) , proj₁ (proj₂ SetUni)) _ _ t₀
      t₂ = cong (λ f → f true) (cong proj₁ t₁)
  in subst T t₂ tt

-- 4. Аксиома K.

-- K : {A : Set} (p : A ≡ A) → p ≡ refl
-- K = ?

{-
not≡id : not ≡ (λ x → x)
not≡id =
  let t = K (SetExt (not , not , not-not , not-not))
  in {!!}
-}

-- 5. Группоиды.

-- isProp : Set → Set
-- isProp A = (x y : A) → x ≡ y

-- isSet : Set → Set
-- isSet A = (x y : A) → isProp (x ≡ y)

isGpd : Set → Set
isGpd A = (x y : A) → isSet (x ≡ y)

is-n-Type : ℕ → Set → Set
is-n-Type 0 A = isSet A
is-n-Type (suc n) A = (x y : A) → is-n-Type n (x ≡ y)

idp : {G : Set} {x : G} → x ≡ x
idp = refl

_**_ : {G : Set} {x y z : G} → x ≡ y → y ≡ z → x ≡ z
p ** refl = p

inv : {A : Set} {x y : A} → x ≡ y → y ≡ x
inv refl = refl

idp-left : {A : Set} {x y : A} (p : x ≡ y) → idp ** p ≡ p
idp-left refl = refl

idp-left-gr : {A : Set} {x : A} (p : x ≡ x) → idp ** p ≡ p
idp-left-gr = idp-left

idp-right : {A : Set} {x y : A} (p : x ≡ y) → p ** idp ≡ p
idp-right refl = refl

**-assoc : {A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ** q) ** r ≡ p ** (q ** r)
**-assoc p q refl = refl

-- 6. Группа автоморфизмов элемента группоида.

-- 7. Автоморфизмы конечных множеств, разница между ℕ и FinSet.
