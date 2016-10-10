module tasks05 where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Char
open import Data.Unit
open import Data.Empty
open import Data.String hiding (_++_)
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- 1. Используя тип List, определите тип данных (через зависимые записи) списков длины n (число должно быть параметром записи).
--    Реализуйте для такого типа функции head и tail.

record List' (A : Set) (n : ℕ) : Set where
  constructor list'
  field
    l : List A
    p : length l ≡ n

head' : {A : Set} → {n : ℕ} → List' A (suc n) → A
head' (list' [] ())
head' (list' (x ∷ l) p) = x

tail' : {A : Set} → {n : ℕ} → List' A (suc n) → List' A n
tail' (list' [] ())
tail' (list' (x ∷ l) p) = list' l (cong pred p)

-- 2. Определите тип (через зависимые записи) четных натуральных чисел.
--    Определите функцию деления на 2.

isEven : ℕ → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc x)) = isEven x

record Evenℕ : Set where
  constructor even
  field
    num : ℕ
    p : T (isEven num)

div2 : Evenℕ → ℕ
div2 (even zero p) = zero
div2 (even (suc zero) ())
div2 (even (suc (suc num)) p) = suc (div2 (even num p))

-- 3. Постройте структуру моноида на типе натуральных чисел (т.е. нужно сконструировать элемент соответствующей записи).
-- Подхаченный моноид, чтобы не писать второй свой

record Monoid (A : Set) : Set₁ where
  field
    id : A
    _#_ : A → A → A
    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

+-assoc : (x : ℕ) {y z : ℕ} → (x + y) + z ≡ x + (y + z)
+-assoc 0 = refl
+-assoc (suc x) = cong suc (+-assoc x)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y)) (trans (cong suc (sym (+-comm x y))) (+-comm (suc x) y)))

ℕ-Monoid : Monoid ℕ
ℕ-Monoid = record
            { id = 0
            ; _#_ = _+_
            ; assoc = λ x y z → +-assoc x
            ; id-left = λ x → refl
            ; id-right = λ x → +-comm x 0
            }

-- 4. Напишите тип монады (через зависимые записи).
--    Элементы этого типа должны удовлетворять всем законом монад.

record Monad (M : Set → Set) : Set₁ where
  field
    return : {A : Set} → A → M A
    _>>=_ : {A B : Set} → M A → (A → M B) → M B

    left-id : {A B : Set} {a : A} {b : B} (f : A → M B) → (return a) >>= f ≡ f a
    right-id : {A : Set} {a : A} (m : M A) → m >>= return ≡ m
    assoc : {A B C : Set} {a : A} {b : B} (m : M A) (f : A → M B) (g : B → M C) → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)


-- 5. Определите тип данных Maybe, сконструируйте структуру функтора и монады на этом типе.

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) → fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

fmap-helper : {A B : Set} → (A → B) → Maybe A → Maybe B
fmap-helper f (just x) = just (f x)
fmap-helper f nothing = nothing

fmap-id-proof : {A : Set} (a : Maybe A) → fmap-helper (λ x → x) a ≡ a
fmap-id-proof (just x) = refl
fmap-id-proof nothing = refl

fmap-comp-proof : {A B C : Set} (f : A → B) → (g : B → C) → (a : Maybe A) → fmap-helper (λ x → g (f x)) a ≡ fmap-helper g (fmap-helper f a)
fmap-comp-proof f g (just x) = refl
fmap-comp-proof f g nothing = refl

Maybe-Functor : Functor Maybe
Maybe-Functor = record
                { fmap = fmap-helper
                ; fmap-id = fmap-id-proof
                ; fmap-comp = fmap-comp-proof
                }

maybe-binder : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
maybe-binder (just x) f = f x
maybe-binder nothing f = nothing

maybe-right-id : {A : Set} {a : A} (m : Maybe A) → maybe-binder m just ≡ m
maybe-right-id (just x) = refl
maybe-right-id nothing = refl

maybe-assoc : {A B C : Set} {a : A} {b : B} (m : Maybe A) (f : A → Maybe B) (g : B → Maybe C) →
                maybe-binder (maybe-binder m f) g ≡ maybe-binder m (λ x → maybe-binder (f x) g)
maybe-assoc (just x) f g = refl
maybe-assoc nothing f g = refl


Maybe-Monad : Monad Maybe
Maybe-Monad = record
              { return = just
              ; _>>=_ = λ {A} {B} m k → maybe-binder {A} {B} m k
              ; left-id = λ f → refl
              ; right-id = λ {A} {a} m → maybe-right-id {A} {a} m
              ; assoc = λ {A} {B} {C} {a} {b} m f g → maybe-assoc {A} {B} {C} {a} {b} m f g
              }

-- 6. Реализуйте sscanf.
-- %b - формат для булов

maybeToBool : {A : Set} → Maybe A → Bool
maybeToBool (just x) = true
maybeToBool nothing = false

charToInt : Char → Maybe ℕ
charToInt '1' = just 1
charToInt '2' = just 2
charToInt '3' = just 3
charToInt '4' = just 4
charToInt '5' = just 5
charToInt '6' = just 6
charToInt '7' = just 7
charToInt '8' = just 8
charToInt '9' = just 9
charToInt _ = nothing

charToBool : Char → Maybe Bool
charToBool '0' = just false
charToBool '1' = just true
charToBool _ = nothing

split : List Char → List Char × List Char
split xs = split-helper xs []
  where
  split-helper : List Char → List Char → List Char × List Char
  split-helper (' ' ∷ xs) acc = (acc , xs)
  split-helper [] acc = (acc , [])
  split-helper (x ∷ xs) acc = split-helper xs (acc ++ x ∷ [])


maybe-app : {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
maybe-app (just f) (just x) = just (f x)
maybe-app (just f) nothing = nothing
maybe-app nothing (just x) = nothing
maybe-app nothing nothing = nothing

exp : ℕ → ℕ → ℕ
exp x 0 = 1
exp x (suc n) = x * (exp x n)

parseInt : List Char → Maybe ℕ
parseInt [] = just 0
parseInt (x ∷ xs) = maybe-app (fmap-helper (λ x y → x * (exp 10 (length xs)) + y) (charToInt x)) (parseInt xs)


data FmtData : Set where
  num : FmtData
  bool : FmtData

FmtRes : Maybe (List FmtData) → Set
FmtRes (just []) = ⊤
FmtRes (just (num ∷ xs)) = ℕ × (FmtRes (just xs))
FmtRes (just (bool ∷ xs)) = Bool × (FmtRes (just xs))
FmtRes nothing = ⊥

stringToFmtData : List Char → Maybe (List FmtData)
stringToFmtData [] = just []
stringToFmtData ('%' ∷ 'd' ∷ xs) = fmap-helper (_∷_ num) (stringToFmtData xs)
stringToFmtData ('%' ∷ 'b' ∷ xs) = fmap-helper (_∷_ bool) (stringToFmtData xs)
stringToFmtData (' ' ∷ xs) = stringToFmtData xs
stringToFmtData _ = nothing

sscanf' : (fmt : Maybe (List FmtData)) → (xs : List Char) → Maybe (FmtRes fmt)
sscanf' nothing xs = nothing
sscanf' (just []) xs = just tt
sscanf' (just rs) [] = nothing
sscanf' (just (bool ∷ rs)) (x ∷ xs) = maybe-app (fmap-helper (λ x y → x , y) (charToBool x)) (sscanf' (just rs) xs)
sscanf' (just (num ∷ rs)) xs = maybe-app (fmap-helper (λ x y → x , y) (parseInt (proj₁ (split xs)))) (sscanf' (just rs) (proj₂ (split xs)))

sscanf : (fmt : List Char) → (xs : List Char) → Maybe (FmtRes (stringToFmtData fmt))
sscanf [] xs = just tt
sscanf fmt xs = sscanf' (stringToFmtData fmt) xs


-- 7. Напишите монаду Writer.

open Monoid

data Writer (W : Set) {m : Monoid W} (A : Set) : Set where
  runWriter : A × W → Writer W A

writer-binder-helper : {W A : Set} {m : Monoid W} → Writer W {m} A → W → Writer W {m} A
writer-binder-helper {m = m} (runWriter (a , w)) w' = runWriter (a , (_#_ m) w' w)

writer-binder : {W A B : Set} {m : Monoid W} → Writer W {m} A → (A → Writer W {m} B) → Writer W {m} B
writer-binder {W = W} {B = B} {m = m} (runWriter (a , w)) k = writer-binder-helper (k a) w

writer-left-id : {W B : Set} {m : Monoid W} (b : Writer W {m} B) → writer-binder-helper b (id m) ≡ b
writer-left-id {W} {B} {m} (runWriter (a , w)) = cong (λ x → runWriter (a , x)) (id-left m w)

writer-right-id : {W A : Set} {m : Monoid W} (w : Writer W {m} A) → writer-binder w (λ x → runWriter (x , id m)) ≡ w
writer-right-id {W} {A} {m} (runWriter (a , w)) = cong (λ x → runWriter (a , x)) (id-right m w)

writer-assoc : {W A B C : Set} {m : Monoid W} {a : A} {b : B} (wa : Writer W {m} A) (f : A → Writer W {m} B) (g : B → Writer W {m} C) →
                writer-binder (writer-binder wa f) g ≡ writer-binder wa (λ x → writer-binder (f x) g)
writer-assoc {W} {A} {B} {C} {m} {a} {b} (runWriter (a' , w)) f g = writer-assoc-helper {W} {A} {B} {C} {m} {a} {b} (f a') g
  where
    writer-assoc-helper : {W A B C : Set} {m : Monoid W} {a : A} {b : B} {w : W} (wb : Writer W {m} B) (g : B → Writer W {m} C) →
                          writer-binder (writer-binder-helper wb w) g ≡ writer-binder-helper (writer-binder wb g) w
    writer-assoc-helper {W} {A} {B} {C} {m} {a} {b} {w} (runWriter (b' , w')) g = writer-assoc-helper-helper {W} {A} {B} {C} {m} {a} {b} {w} (g b')
      where
        writer-assoc-helper-helper : {W A B C : Set} {m : Monoid W} {a : A} {b : B} {w w' : W} → (wc : Writer W {m} C) →
                                      writer-binder-helper wc ((m # w) w') ≡ writer-binder-helper (writer-binder-helper wc w') w
        writer-assoc-helper-helper {m = m} {w = w} {w' = w'} (runWriter (c , w'')) = cong (λ x → runWriter (c , x)) (assoc m w w' w'')

Writer-Monad : {W : Set} {m : Monoid W} → Monad (Writer W {m})
Writer-Monad {W} {m} = record
                      { return = λ {A} x → runWriter (x , (id m))
                      ; _>>=_ = λ {A} {B} w k → writer-binder {W} {A} {B} {m} w k
                      ; left-id = λ {W} {B} {a} f → writer-left-id (f a)
                      ; right-id = writer-right-id
                      ; assoc = λ {A} {B} {C} {a} {b} → writer-assoc {W} {A} {B} {C} {m} {a} {b}
                      }
