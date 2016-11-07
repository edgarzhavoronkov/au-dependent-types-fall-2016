{-# OPTIONS --without-K #-}

module Cantor where

open import Data.Product hiding (∃)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
import Level

open import Trunc

∃ : ∀ {i} {j} (A : Set i) (B : A → Set j) → Set (i Level.⊔ j)
∃ A B = ∥ Σ A B ∥

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

isSur : ∀ {i} {j} {A : Set i} {B : Set j} → (A → B) → Set (i Level.⊔ j)
isSur {i} {j} {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)

isInj : ∀ {i} {j} {A : Set i} {B : Set j} → (A → B) → Set (i Level.⊔ j)
isInj {i} {j} {A} {B} f = (x x' : A) → f x ≡ f x' → x ≡ x'

isSet : ∀ {i} → Set i → Set i
isSet A = (x y : A) → isProp (x ≡ y)


-- Теорема Кантора говорит, что для любого множества A мощность множества его подмножеств строго больше, чем мощность A.

-- Множество подмножеств можно определить следующим образом:

Subs : Set → Set₁
Subs A = A → hProp

-- Формально утверждение теоремы Кантора состоит из двух частей:
-- "существует инъекция из A в Subs A" и "не существует сюръекции из A в Subs A".

Cantor₁ = (A : Set) → isSet A → Σ[ f ∶ (A → Subs A) ] (isInj f)
Cantor₂ = (A : Set) (f : A → Subs A) → isSur f → ⊥

-- Докажите теорему Кантора.

coe : {A B : Set} → A ≡ B → A → B
coe refl x = x

cantor₁ : Cantor₁
cantor₁ A Sa = f , pr
    where
        f : A → A → hProp
        f x y = prop (x ≡ y) (Sa x y)

        pr : isInj f
        pr x y p =
            let t = cong (λ f → f x) p
                t' = cong hProp.A t
            in sym (coe t' refl)

cantor₂ : Cantor₂
cantor₂ A f f-sur =
    let t = f-sur (λ x → prop (hProp.A (f x x) → ⊥) (λ x₁ y → {!   !}))
    in Trunc-rec (λ x → λ ()) (λ x → {!   !}) t
