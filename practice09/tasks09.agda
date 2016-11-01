{-# OPTIONS --without-K #-}

module tasks09 where

open import Data.Product hiding (∃)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Unit

open import Trunc

-- 1. Докажите следующие правила, характеризующие квантор существования.

∃ : (A : Set) (B : A → Set) → Set
∃ A B = ∥ Σ A B ∥

∃-intro : {A : Set} {B : A → Set} → (a : A) → B a → ∃[ x ∶ A ] (B x)
∃-intro a Ba = ∣ a , Ba ∣

∃-elim : {A : Set} {B : A → Set} {C : Set} → isProp C → ((a : A) → B a → C) → ∃ A B → C
∃-elim {A} {B} {C} Cp f = Trunc-rec Cp h
    where
        h : Σ A B → C
        h (proj₁ , proj₂) = f proj₁ proj₂

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

-- 2. Определите утверждение "натуральные числа существуют".

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

natural-numbers-exist : hProp
natural-numbers-exist = prop (∥ ℕ ∥) trunc

-- 3. Докажите, что функция pred сюръективна.

isSur : {A B : Set} → (A → B) → Set
isSur {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)


pred-is-sur : isSur pred
pred-is-sur y = ∣ suc y , refl ∣

-- 4. Докажите, что функция suc не сюръективна.

absurd : {x : ℕ} → (suc x ≡ 0) → ⊥
absurd ()

suc-is-not-sur : isSur suc → ⊥
suc-is-not-sur p = absurd {1} (∃-elim (λ x → λ ()) (λ a → λ ()) (p 0))

-- 5. Пусть f : A → B и g : B → C ─ некоторые функции.
--    Докажите, что если f и g сюръективны, то g ∘ f также сюръективна.
--    Докажите, что если g ∘ f сюръективна, то g также сюръективна.

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

∘-sur : {A B C : Set} (f : A → B) (g : B → C) → isSur f → isSur g → isSur (g ∘ f)
∘-sur f g Fs Gs = λ c → ∃-elim trunc (λ b x → ∃-elim trunc (λ a x₁ → ∣ a , (subst (λ x₂ → (g x₂) ≡ c) (sym x₁) x) ∣) (Fs b)) (Gs c)

∘-sur' : {A B C : Set} (f : A → B) (g : B → C) → isSur (g ∘ f) → isSur g
∘-sur' f g GFs = λ c → ∃-elim trunc (λ a x → ∣ f a , x ∣) (GFs c)

-- 6. Докажите, что функция является биекцией тогда и только тогда, когда она является инъекцией и сюръекцией.

isInj : {A B : Set} → (A → B) → Set
isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y

isBij : {A B : Set} → (A → B) → Set
isBij {A} {B} f = Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))

isBij-isInj : {A B : Set} (f : A → B) → isBij f → isInj f
isBij-isInj f (g , proj₁ , proj₂) = λ x₁ x₂ p → trans (sym (proj₁ x₁)) (trans (cong g p) (proj₁ x₂))

isBij-isSur : {A B : Set} (f : A → B) → isBij f → isSur f
isBij-isSur f (g , proj₁ , proj₂) = λ y → ∣ g y  , proj₂ y ∣

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

-- Эта лемма вам может пригодится
sigmaExt : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'} (p : a ≡ a') → subst B p b ≡ b' → _≡_ {A = Σ A B} (a , b) (a' , b')
sigmaExt refl q = cong (_,_ _) q


isInj-isSur-isBij : {A B : Set} → isSet B → (f : A → B) → isInj f → isSur f → isBij f
isInj-isSur-isBij {A} Bs f fi fs =
  (λ b → proj₁ (isInj-isSur-isBij' Bs f fi fs b)) ,
  (λ a → lemma a) ,
  (λ b → proj₂ (isInj-isSur-isBij' Bs f fi fs b))
  where
    isInj-isSur-isBij' : {A B : Set} → isSet B → (f : A → B) → isInj f → isSur f → (y : B) → Σ[ x ∶ A ] (f x ≡ y)
    isInj-isSur-isBij' {A} {B} Bs f fi fs y = proj₁ (Trunc-rec Σ-isProp (λ z → z) (fs y)) , proj₂ (Trunc-rec Σ-isProp (λ z → z) (fs y))
        where
            Σ-isProp : isProp (Σ[ x ∶ A ] (f x ≡ y))
            Σ-isProp (proj₁ , proj₂) (proj₃ , proj₄) with fi proj₁ proj₃ (trans proj₂ (sym proj₄))
            Σ-isProp (proj₁ , proj₂) (.proj₁ , proj₄) | refl with Bs (f proj₁) y proj₂ proj₄
            Σ-isProp (proj₁ , proj₂) (.proj₁ , .proj₂) | refl | refl = refl

    lemma : (a : A) → proj₁ (isInj-isSur-isBij' Bs f fi fs (f a)) ≡ a
    lemma a with isInj-isSur-isBij' Bs f fi fs (f a)
    lemma a | proj₁ , proj₂ = fi proj₁ a proj₂


-- isSur {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)
-- isSet A = (x y : A) → isProp (x ≡ y)
-- isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y
-- ∥_∥ : Set → Set
-- ∣_∣ : {A : Set} → A → ∥ A ∥
-- trunc : {A : Set} → isProp (∥ A ∥)
-- Trunc-rec : {A B : Set} → isProp B → (A → B) → ∥ A ∥ → B
-- ∃-elim : {A : Set} {B : A → Set} {C : Set} → isProp C → ((a : A) → B a → C) → ∃ A B → C

-- 7. Докажите, что isBij является утверждением.

isBij-isProp : {A B : Set} → isSet A → isSet B → (f : A → B) → isProp (isBij f)
isBij-isProp As Bs f = {!   !}

-- 8. См. Cantor.agda.
