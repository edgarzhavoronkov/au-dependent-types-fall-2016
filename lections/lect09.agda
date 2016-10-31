{-# OPTIONS --without-K #-}

module lect09 where

open import Data.Sum
open import Data.Product hiding (∃)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Nat
open import Data.Unit

open import Trunc

-- 1. Пропозициональное обрезание.

data Tr (A : Set) : Set where
  tr : A → Tr A

{-
Tr-rec : {A : Set} {B : Set} → (A → B) → Tr A → B
Tr-rec f (tr a) = f a

ff : Tr A → B
-- ff (tr a) = b
ff = Tr-rec (λ a → b)
-}

{-
Tr-f : {A : Set} → A → Tr A
Tr-f = tr

Tr-g : {A B : Set} → isProp B → (A → B) → Tr A → B
Tr-g p f (tr a) = f a
-}

-- ∥_∥ : Set → Set
-- ∣_∣ : {A : Set} → A → ∥ A ∥
-- trunc : {A : Set} → isProp (∥ A ∥)
-- Trunc-rec : {A B : Set} → isProp B → (A → B) → ∥ A ∥ → B

_∨_ : Set → Set → Set
A ∨ B = ∥ A ⊎ B ∥

∨-isProp : (A B : Set) → isProp (A ∨ B)
∨-isProp A B = trunc

inl : {A B : Set} → A → A ∨ B
inl a = ∣ inj₁ a ∣

inr : {A B : Set} → B → A ∨ B
inr b = ∣ inj₂ b ∣

∨-elim : {A B C : Set} → isProp C → (A → C) → (B → C) → A ∨ B → C
∨-elim {A} {B} {C} Cp f g = Trunc-rec Cp h
  where
    h : A ⊎ B → C
    h (inj₁ a) = f a
    h (inj₂ b) = g b
{-
∨-elim Cp f g (∣ inj₁ a ∣) = f a
∨-elim Cp f g (∣ inj₂ b ∣) = g b
-}

∃ : (A : Set) (B : A → Set) → Set
∃ A B = ∥ Σ A B ∥

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

∃-isProp : (A : Set) (B : A → Set) → isProp (∃ A B)
∃-isProp A B = trunc

∃-intro : {A : Set} {B : A → Set} → (a : A) → B a → ∃[ x ∶ A ] (B x)
∃-intro = {!!}

∃-elim : {A : Set} {B : A → Set} {C : Set} → isProp C → ((a : A) → B a → C) → ∃[ x ∶ A ] (B x) → C
∃-elim = {!!}

-- 2. Предикат "множество не пусто".

inh : Set → Set
inh A = ∃[ x ∶ A ] ⊤

inh-Trunc : {A : Set} → inh A → ∥ A ∥
inh-Trunc = ∃-elim trunc (λ a _ → ∣ a ∣)

Trunc-inh : {A : Set} → ∥ A ∥ → inh A
Trunc-inh = Trunc-rec trunc (λ a → ∣ a , tt ∣)

-- 3. Сюръективные функции.

isInj : {A B : Set} → (A → B) → Set
isInj {A} {B} f = (x x' : A) → f x ≡ f x' → x ≡ x'

isSur : {A B : Set} → (A → B) → Set
isSur {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)

sigmaExt : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'}
  (p : a ≡ a') →
  subst B p b ≡ b' →
  _≡_ {A = Σ A B} (a , b) (a' , b')
sigmaExt refl refl = refl

-- { x ∈ A | B } → A

emb-isInj : {A : Set} {B : A → Set} → ((x : A) → isProp (B x)) → isInj {Σ A B} proj₁
emb-isInj p t t' q = sigmaExt q (p _ _ _)

factor-lem : {A B : Set} (f : A → B) →
  Σ[ C ∶ Set ]
  Σ[ g ∶ (A → C) ]
  Σ[ h ∶ (C → B) ]
  (isSur g × isInj h × ((λ x → h (g x)) ≡ f))
factor-lem {A} {B} f =
  (Σ[ y ∶ B ] ∃[ x ∶ A ] (f x ≡ y)) ,
  (λ x → f x , ∣ x , refl ∣) ,
  proj₁ ,
  lem ,
  (emb-isInj (λ _ → trunc)) ,
  refl
  where
    lem : isSur {A} {Σ[ y ∶ B ] ∃[ x ∶ A ] (f x ≡ y)} (λ x → f x , ∣ x , refl ∣)
    lem (y , p) = Trunc-rec trunc (λ p' → ∣ proj₁ p' , (sigmaExt (proj₂ p') (trunc _ _)) ∣) p

-- Trunc-rec : {A B : Set} → isProp B → (A → B) → ∥ A ∥ → B

-- 4. Фактор множества через HIT.

-- 5. Фактор множества.

record EqRel (A : Set) : Set₁ where
  constructor eqrel
  field
    R : A → A → Set
    R-isProp : (x y : A) → isProp (R x y)
    R-refl : (x : A) → R x x
    R-sym : (x y : A) → R x y → R y x
    R-trans : (x y z : A) → R x y → R y z → R x z

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

_/_ : (A : Set) → EqRel A → Set₁
A / e = let open EqRel e in Σ[ P ∶ (A → hProp) ] ((∃[ x ∶ A ] (hProp.A (P x))) × ((x y : A) → R x y → hProp.A (P x) → hProp.A (P y)))

[_] : {A : Set} {e : EqRel A} → A → A / e
[_] {A} {e} a = let open EqRel e in
  (λ a' → prop (R a a') (R-isProp a a')) ,
  ∣ a , R-refl a ∣ ,
  (λ x y p q → R-trans a x y q p)
