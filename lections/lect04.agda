module lect04 where

open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding (subst; sym; trans; cong)

-- 1. Равенство в логике, равенство для различных типов.

eq : (ℕ → ℕ) → (ℕ → ℕ) → Bool
eq f g = {! !}

-- 2. Рефлексивность, симметричность, транзитивность, конгруэнтность, принцип Лейбница.

-- 3. Определение через индуктивные семейства.

{-
infix 1 _≡_
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a
-}

-- 4. Симметричность, транзитивность, конгруэнтность, принцип Лейбница.

subst : {A : Set} (B : A → Set) {a a' : A} → a ≡ a' → B a → B a'
subst B refl b = b

sym : {A : Set} {a a' : A} → a ≡ a' → a' ≡ a
sym {a = a} p = subst (λ x → x ≡ a) p refl

trans : {A : Set} {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans {a = a} p q = subst (λ x → a ≡ x) q p

cong : {A B : Set} (f : A → B) {a a' : A} → a ≡ a' → f a ≡ f a'
cong f {a} p = subst (λ x → f a ≡ f x) p refl

-- 5. Пример доказательства.

infix 1 _==_
_==_ : ℕ → ℕ → Bool
0 == 0 = true
0 == suc _ = false
suc _ == 0 = false
suc x == suc y = x == y

+-assoc : (x y z : ℕ) → T ((x + y) + z == x + (y + z))
+-assoc zero y z = {! !}
+-assoc (suc x) y z = +-assoc x y z

+-assoc' : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc' zero y z = refl
+-assoc' (suc x) y z = cong suc (+-assoc' x y z)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y))
  (trans (cong suc (+-comm y x)) (+-comm (suc x) y)))

open ≡-Reasoning

+-comm' : (x y : ℕ) → x + y ≡ y + x
+-comm' zero zero = refl
+-comm' zero (suc y) = cong suc (+-comm' zero y)
+-comm' (suc x) zero = cong suc (+-comm' x zero)
+-comm' (suc x) (suc y) = cong suc
  (begin
    x + suc y
  ≡⟨ +-comm' x (suc y) ⟩
    suc y + x
  ≡⟨ refl ⟩
    suc (y + x)
  ≡⟨ cong suc (sym (+-comm' x y)) ⟩
    suc (x + y)
  ≡⟨ +-comm' (suc x) y ⟩
    y + suc x
  ∎)

rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev [] = []
rev {A} {suc n} (x ∷ xs) = subst (Vec A) (+-comm n 1) (rev xs ++ x ∷ [])

-- rev xs ++ x ∷ [] : Vec A (n + 1)
-- ?                : Vec A (1 + n)

++-assoc : {A : Set} {n m k : ℕ} (xs : Vec A n) (ys : Vec A m) (zs : Vec A k) →
  subst (Vec A) (+-assoc' n m k) ((xs ++ ys) ++ zs) ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc {A} {suc n} {m} {k} (x ∷ xs) ys zs =
  trans (lemma x (+-assoc' n m k) ((xs ++ ys) ++ zs)) (cong (_∷_ x) (++-assoc xs ys zs))
  where
    lemma : (x : A) {n m : ℕ} (p : n ≡ m) (xs : Vec A n) →
      subst (Vec A) (cong suc p) (x ∷ xs) ≡ x ∷ subst (Vec A) p xs
    lemma x₁ refl xs₁ = refl

-- 6. Доказательства неравенств.

==-≡ : (x y : ℕ) → T (x == y) → x ≡ y
==-≡ zero zero p = refl
==-≡ zero (suc y) ()
==-≡ (suc x) zero ()
==-≡ (suc x) (suc y) p = cong suc (==-≡ x y p)

D : ℕ → Set
D zero = ⊥
D (suc _) = ⊤

≡-== : (x y : ℕ) → x ≡ y → T (x == y)
≡-== zero zero p = tt
≡-== zero (suc y) ()
≡-== (suc x) zero p = subst D p tt
≡-== (suc x) (suc y) p = ≡-== x y (cong pred p)
