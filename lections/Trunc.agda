{-# OPTIONS --without-K #-}

module Trunc where

open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

isProp : ∀ {i} → Set i → Set i
isProp A = (x y : A) → x ≡ y

data Phantom {i} {A : Set i} (a : A) : Set₀ where
  phantom : Phantom a

module _ {i} where

  private
    data #Trunc-aux (A : Set i) : Set i where
      #∣_∣ : A → #Trunc-aux A

    data #Trunc (A : Set i) : Set i where
      #trunc : #Trunc-aux A → (⊤ → ⊤) → #Trunc A

  ∥_∥ = #Trunc

  ∣_∣ : {A : Set i} → A → ∥ A ∥
  ∣ a ∣ = #trunc #∣ a ∣ _

  postulate
    trunc : {A : Set i} → isProp (∥ A ∥)

  module TruncElim {A : Set i} {j}
    (P : ∥ A ∥ → Set j)
    (p : (a : ∥ A ∥) → isProp (P a))
    (d : (a : A) → P ∣ a ∣) where

    f : (a : ∥ A ∥) → P a
    f = f-aux phantom  where

      f-aux : Phantom p → (a : ∥ A ∥) → P a
      f-aux phantom (#trunc #∣ a ∣ _) = d a

open TruncElim public renaming (f to Trunc-elim)

module TruncRec {i j} {A : Set i} {B : Set j} (p : (x y : B) → x ≡ y) (d : A → B) where

  private
    module M = TruncElim _ (λ x → p) d

  f : ∥ A ∥ → B
  f = M.f

open TruncRec public renaming (f to Trunc-rec)
