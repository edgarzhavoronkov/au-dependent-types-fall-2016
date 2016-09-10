module tasks01 where

-- 0. Определить flip, const

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

const : {A B : Set} → A → B → A
const a b = a

-- 1. Определить миксфикссный if_then_else_ полиморфный по возвращаемому значению

data Bool : Set where
    true false : Bool

not : Bool → Bool
not true = false
not false = true

infix 7 _||_
_||_ : Bool → Bool → Bool
true || _ = true
false || x = x

if_then_else_ : {A : Set} →  Bool → A → A → A
if true then x else _ = x
if false then _ else x = x

-- 2. Определить возведение в степень и факториал для натуральных чисел

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

infix 5 _+_
_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

infix 6 _*_
_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + x * y

_^_ : ℕ → ℕ → ℕ
x ^ zero = suc zero
x ^ (suc y) = x * (x ^ y)

fac : ℕ → ℕ
fac zero = suc zero
fac (suc x) = (suc x) * (fac x)

-- 3. Определите mod и gcd

_-_ : ℕ → ℕ → ℕ
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

-- div : ℕ → ℕ → ℕ
-- div x y = if (x < y) then zero else suc (div (x - y) y)

div' : ℕ → ℕ → ℕ → ℕ
div' zero x y = zero
div' (suc c) x y = if (x < y) then zero else suc (div' c (x - y) y)

div : ℕ → ℕ → ℕ
div x y = div' x x y

mod : ℕ → ℕ → ℕ
mod x y = x - y * (div x y)

gcd' : ℕ → ℕ → ℕ → ℕ
gcd' zero x y = x
gcd' (suc c) x y = gcd' c y (mod x y)

gcd : ℕ → ℕ → ℕ
gcd x y = gcd' y x y

-- 4. Определить (полиморфный) reverse для списков

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
nil ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

reverse' : {A : Set} → List A → List A → List A
reverse' l nil = l
reverse' l (cons x xs) = reverse' (cons x l) xs

reverse : {A : Set} → List A → List A
reverse = reverse' nil

-- 5. Реализовать любой алгоритм сортировки

insert : ℕ → List ℕ → List ℕ
insert x nil = cons x nil
insert x (cons y ys) = if (x < y) then (cons y (insert x ys)) else (cons x (cons y ys))

sort : List ℕ → List ℕ
sort nil = nil
sort (cons x xs) = insert x (sort xs)

-- 6. Докажите ассоциативность ||

data Unit : Set where
  unit : Unit

data Empty : Set where

absurd : {A : Set} → Empty → A
absurd ()

T : Bool → Set
T true = Unit
T false = Empty

infix 3 _==_
_==_ : Bool → Bool → Bool
true == true = true
true == false = false
false == true = false
false == false = true

||-assoc : (x y z : Bool) → T ((x || y) || z == x || (y || z))
||-assoc true true true = unit
||-assoc true true false = unit
||-assoc true false true = unit
||-assoc true false false = unit
||-assoc false true true = unit
||-assoc false true false = unit
||-assoc false false true = unit
||-assoc false false false = unit

-- 7. Докажите, что fac 3 равен 6 и что fac 2 не равен 3.

infix 3 _=='_
_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' suc _ = false
suc _ ==' zero = false
suc x ==' suc y = x ==' y

fac3=6 : T (fac (suc (suc (suc zero))) ==' suc (suc (suc (suc (suc (suc zero))))))
fac3=6 = unit

fac2≠3 : T (fac (suc (suc zero)) ==' suc (suc (suc zero))) → Empty
fac2≠3 ()

-- 8. Определите равенство для списков натуральных чисел; докажите, что для любого xs : List ℕ верно, что reverse (reverse xs) равно xs

infix 3 _&&_
_&&_ : Bool → Bool → Bool
true && x = x
_ && false = false
false && _ = false

infix 3 _===_
_===_ : List ℕ → List ℕ → Bool
nil === nil = true
nil === cons _ _ = false
cons _ _ === nil = false
(cons x xs) === (cons y ys) = (x ==' y) && (xs === ys)

one = suc zero
two = suc one
three = suc two

l = cons one (cons two (cons three nil))
l' = reverse l

reverse-inv : (xs : List ℕ) → T (reverse (reverse xs) === xs)
reverse-inv nil = unit
reverse-inv (cons x xs) = {!!}


