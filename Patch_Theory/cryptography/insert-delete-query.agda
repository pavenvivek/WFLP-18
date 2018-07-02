{-# OPTIONS --type-in-type --without-K #-}

open import Data.List
open import Agda.Builtin.Nat
open import Patch_Theory.agda_lib.Utils
open import Patch_Theory.agda_lib.Vector
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

module Patch_Theory.cryptography.insert-delete-query where

insert-first : (value : Nat) → List Int → List Int
insert-first value vec = (value ∷ vec)

{--
insert-first-2cols : {n : Nat} → (value : Nat × Nat) → Vec Int n × Vec Int n → Vec Int (suc n) × Vec Int (suc n)
insert-first-2cols (value1 , value2) (vec1 , vec2) = (value1 :: vec1) , (value2 :: vec2)
--}

insert : (value : Nat) → (i : Nat) → List Int → List Int
insert value zero [] = value ∷ []
insert value (suc i) [] = [] 
insert value zero (x ∷ vec) = (value ∷ (x ∷ vec))
insert value (suc i) (x ∷ vec) = x ∷ insert value i vec

{--
insert-2cols : {n : Nat} → (value : Nat × Nat) → (i : Fin n) → Vec Int n × Vec Int n → Vec Int (suc n) × Vec Int (suc n)
insert-2cols (value1 , value2) () ([] , [])
insert-2cols (value1 , value2) zero ((x1 :: vec1) , (x2 :: vec2)) = (value1 :: (x1 :: vec1)) , (value2 :: (x2 :: vec2))
insert-2cols (value1 , value2) (suc i) ((x1 :: vec1) , (x2 :: vec2)) = (x1 :: insert value1 i vec1) , (x2 :: insert value2 i vec2)
--}

delete : (i : Nat) → List Int → List Int
delete zero [] = []
delete zero (x ∷ vec) = vec
delete (suc i) [] = []
delete (suc i) (x ∷ vec) = x ∷ (delete i vec)

{--
delete-2cols : {n : Nat} → (i : Fin (suc n)) → Vec Int (suc n) × Vec Int (suc n) → Vec Int n × Vec Int n
delete-2cols {0} zero ((x1 :: []) , (x2 :: [])) = [] , []
delete-2cols {(suc n)} zero ((x1 :: vec1) , (x2 :: vec2)) = vec1 , vec2
delete-2cols {0} (suc i) ((x1 :: vec1) , (x2 :: vec2)) = vec1 , vec2
delete-2cols {(suc n)} (suc i) ((x1 :: vec1) , (x2 :: vec2)) = (x1 :: (delete {n} i vec1) , x2 :: (delete {n} i vec2))
--}
