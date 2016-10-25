module lect05 where

open import Data.Nat
open import Data.Nat.Show renaming (show to parse)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Char
open import Data.String hiding (_++_)
open import Data.List
open import Data.Product

-- 1. Dependent records

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

-- сигма-тип Σ (x : A) B

-- record Σ (A : Set) (B : A → Set) : Set where
--   constructor _,_
--   field
--     a : A
--     b : B a

-- Тогда Σ (x : A) B == Σ A (λ x → B)


record Posℕ : Set where
  field
    num : ℕ
    even : T (isPos num)

div : ℕ → Posℕ → ℕ
div zero k = zero
div (suc n) k = {!   !}

-- 2. Monoid
record Monoid : Set₁ where
  field
    A : Set
    id : A
    _#_ : A → A → A
    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

-- Example Monoid

xor-left : (x : Bool) → x xor false ≡ x
xor-left true = refl
xor-left false = refl

xor-assoc : (x y z : Bool) → (x xor y) xor z ≡ x xor (y xor z)
xor-assoc true true true = refl
xor-assoc true true false = refl
xor-assoc true false true = refl
xor-assoc true false false = refl
xor-assoc false true true = refl
xor-assoc false true false = refl
xor-assoc false false true = refl
xor-assoc false false false = refl

Bool-Monoid : Monoid
Bool-Monoid = record
                { A = Bool
                ; id = false
                ; _#_ = _xor_
                ; assoc = xor-assoc
                ; id-left = λ x → refl
                ; id-right = xor-left
                }

-- 3. Functor

_∘_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
_∘_ f g x = g (f x)

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) → (g : B → C) → (x : F A) → fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x

-- 4. sprintf. Байка про то, что количество аргументов зависит от аргумента

data FmtData : Set where
  num : FmtData
  char : Char → FmtData

Fmt : List FmtData → Set
Fmt [] = List Char
Fmt (num  ∷  xs) = ℕ → Fmt xs
Fmt (char _ ∷ xs) = Fmt xs

toString : ℕ → List Char
toString x = primStringToList (parse x)

sprintf' : (acc : List Char) → (xs : List FmtData) → Fmt xs
sprintf' acc [] = acc
sprintf' acc (num ∷ xs) = λ x → sprintf' (acc ++ toString x) xs
sprintf' acc (char x ∷ xs) = sprintf' (acc ++ x ∷ []) xs

string-toFmtData : List Char → List FmtData
string-toFmtData [] = []
string-toFmtData ('%' ∷ 'd' ∷ xs) = num ∷ string-toFmtData xs
string-toFmtData (x ∷ xs) = char x ∷ string-toFmtData xs

sprintf : (xs : List Char) → Fmt (string-toFmtData xs)
sprintf xs = sprintf' [] (string-toFmtData xs)

string : List Char
string = sprintf (primStringToList "abc%defg%dgh") 37 56

-- sprintf = sprintf' []
