
open import Agda.Builtin.Nat

module Patch_Theory.agda_lib.Vector where

  data Vec (A : Set) : Nat → Set where
    []   : Vec A 0
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

  recVec : {A : Set} → (C : Set) → 
         C → 
         ({m : Nat} → (x : A) → (xs : Vec A m) → C → C) → 
         ({n : Nat} → (xs : Vec A n) → C)
  recVec C cnil ccons [] = cnil
  recVec C cnil ccons (x :: xs) = ccons x xs (recVec C cnil ccons xs)

  indVec : {A : Set} → (C : {n : Nat} → Vec A n → Set) → 
         C [] → 
         ({m : Nat} → (x : A) → (xs : Vec A m) → C xs → C (x :: xs)) → 
         ({n : Nat} → (xs : Vec A n) → C xs)
  indVec C cnil ccons [] = cnil
  indVec C cnil ccons (x :: xs) = ccons x xs (indVec C cnil ccons xs)
