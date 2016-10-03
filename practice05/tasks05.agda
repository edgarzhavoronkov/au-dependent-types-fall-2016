module tasks05 where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Char
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

record Monoid : Set₁ where
  field
    A : Set
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

ℕ-Monoid : Monoid
ℕ-Monoid = record
            { A = ℕ
            ; id = 0
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

    left-id : {A B : Set} (a : A) (f : A → M B) → (return a) >>= f ≡ f a
    right-id : {A : Set} (m : M A) → m >>= return ≡ m
    assoc : {A B C : Set} (m : M A) (f : A → M B) (g : B → M C) → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)


-- 5. Определите тип данных Maybe, сконструируйте структуру функтора и монады на этом типе.

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) → fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

fmap_helper : {A B : Set} → (A → B) → Maybe A → Maybe B
fmap_helper f (just x) = just (f x)
fmap_helper f nothing = nothing

fmap_id_proof : {A : Set} (a : Maybe A) → fmap_helper (λ x → x) a ≡ a
fmap_id_proof (just x) = refl
fmap_id_proof nothing = refl

fmap_comp_proof : {A B C : Set} (f : A → B) → (g : B → C) → (a : Maybe A) → fmap_helper (λ x → g (f x)) a ≡ fmap_helper g (fmap_helper f a)
fmap_comp_proof f g (just x) = refl
fmap_comp_proof f g nothing = refl

Maybe-Functor : Functor Maybe
Maybe-Functor = record
                { fmap = fmap_helper
                ; fmap-id = fmap_id_proof
                ; fmap-comp = fmap_comp_proof
                }

return_helper : {A : Set} → A → Maybe A
return_helper x = just x

binder_helper : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
binder_helper (just x) f = f x
binder_helper nothing f = nothing

left_id_proof : {A B : Set} (a : A) (f : A → Maybe B) → binder_helper (return_helper a) f ≡ f a
left_id_proof a f = refl

right_id_proof : {A : Set} (m : Maybe A) → binder_helper m return_helper ≡ m
right_id_proof (just x) = refl
right_id_proof nothing = refl

assoc-proof : {A B C : Set} (m : Maybe A) (f : A → Maybe B) (g : B → Maybe C) → binder_helper (binder_helper m f) g ≡ binder_helper m (λ x → binder_helper (f x) g)
assoc-proof (just x) f g = refl
assoc-proof nothing f g = refl

Maybe-Monad : Monad Maybe
Maybe-Monad = record
                { return = λ x → just x
                ; _>>=_ = binder_helper
                ; left-id = left_id_proof
                ; right-id = right_id_proof
                ; assoc = assoc-proof
                }

-- 6. Реализуйте sscanf. Берет две строчки, форматную и из которой мы читаем и возвращает тип, зависящий от форматной строки
-- %b - формат для булов

data FmtData : Set where
  num : FmtData
  bool : FmtData
  char : Char → FmtData

Fmt : List FmtData → Set
Fmt [] = List Char
Fmt (num ∷ xs) = ℕ → Fmt xs
Fmt (bool ∷ xs) = Bool → Fmt xs
Fmt (char _ ∷ xs) = Fmt xs

string-toFmtData : List Char → List FmtData
string-toFmtData [] = []
string-toFmtData ('%' ∷ 'd' ∷ xs) = num ∷ string-toFmtData xs
string-toFmtData ('%' ∷ 'b' ∷ xs) = bool ∷ string-toFmtData xs
string-toFmtData (x ∷ xs) = char x ∷ string-toFmtData xs

sscanf : (xs : List Char) → List Char → Maybe (Fmt (string-toFmtData xs))
sscanf = {!   !}

-- 7. Напишите монаду Writer.

record Monoid' (A : Set) : Set where
  field
    id : A
    _#_ : A → A → A
    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

record Writer (W : Set) (A : Set) : Set where
  constructor wrtr
  field
    log : W
    val : A

writer : {A W : Set} → (A × W) → Writer W A
writer (a , w) = wrtr w a

runWriter : {A W : Set} → Writer W A → (A × W)
runWriter (wrtr log val) = val , log

execWriter : {A W : Set} → Writer W A → W
execWriter (wrtr log val) = log

writer-return : {A X : Set} → {W : Monoid' X} → A → Writer X A
writer-return {W = W} a = writer (a , Monoid'.id W)

writer-binder : {A B X : Set} → {W : Monoid' X} → Writer X A → (A → Writer X B) → Writer X B
writer-binder {W = W} m k = writer (y , ((Monoid'._#_ W) u v))
  where
    x : _
    x = proj₁ (runWriter m)
    u : _
    u = proj₂ (runWriter m)
    y : _
    y = proj₁ (runWriter (k x))
    v : _
    v = proj₂ (runWriter (k x))

writer-left-id : {A B X : Set} {W : Monoid' X} (a : A) (f : A → Writer X B) → writer-binder {W = W} (writer-return {W = W} a) f ≡ f a
writer-left-id a f = {!   !}

writer-right-id : {A X : Set} {W : Monoid' X} (m : Writer X A) → writer-binder {W = W} m (writer-return {W = W}) ≡ m
writer-right-id (wrtr log val) = {!   !}

writer-assoc : {A B C X : Set} {W : Monoid' X} (m : Writer X A) (f : A → Writer X B) (g : B → Writer X C) → writer-binder {W = W} (writer-binder {W = W} m f) g ≡ writer-binder {W = W} m (λ x → writer-binder {W = W} (f x) g)
writer-assoc {W = W} m f g = {!   !}

Writer-Monad : {A B X : Set} → {W : Monoid' X} → Monad (Writer X)
Writer-Monad {A = A} {B = B} {X = X} {W = W} = record
              { return = writer-return {W = W}
              ; _>>=_ = writer-binder {W = W}
              ; left-id = writer-left-id {W = W}
              ; right-id = writer-right-id {W = W}
              ; assoc = writer-assoc {W = W}
              }
