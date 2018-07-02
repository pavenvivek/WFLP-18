{-# OPTIONS --type-in-type --without-K #-}

open import Function renaming (_∘_ to _○_)
-- open import CryptDB_HoTT.agda_lib.Nat
open import Data.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Patch_Theory.agda_lib.Utils
open import Patch_Theory.agda_lib.Vector
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Patch_Theory.agda_lib.Equiv
open import Patch_Theory.cryptography.Paillier-Cryptosystem

module Patch_Theory.cryptography.encrypted-increment where

-- Encrypted increment query

crypt-increment-100 : (p q : Nat) → (i : Nat) → List Int → List Int
crypt-increment-100 p q i [] = []
crypt-increment-100 p q zero (x ∷ xs) = (x * (paillier-encrypt'' p q 100)) ∷ xs
crypt-increment-100 p q (suc i) (x ∷ xs) = x ∷ (crypt-increment-100 p q i xs)

{--
crypt-increment-100-2cols : {l : Nat} → (p q : Nat) → (i : Fin l) → Vec Int l × Vec Int l → Vec Int l × Vec Int l
crypt-increment-100-2cols p q () ([] , [])
crypt-increment-100-2cols p q zero ((x1 :: xs1) , (x2 :: xs2)) = ((x1 * (paillier-encrypt'' p q 100)) :: xs1) , ((x2 * (paillier-encrypt'' p q 100)) :: xs2)
crypt-increment-100-2cols p q (suc i) ((x1 :: xs1) , (x2 :: xs2)) = (x1 :: (crypt-increment-100 p q i xs1)) , (x2 :: (crypt-increment-100 p q i xs2))
--}

crypt-decrement-100 : (p q : Nat) → (i : Nat) → List Int → List Int
crypt-decrement-100 p q i [] = []
crypt-decrement-100 p q zero (x ∷ xs) = (div x (paillier-encrypt'' p q 100)) ∷ xs
crypt-decrement-100 p q (suc i) (x ∷ xs) = x ∷ (crypt-decrement-100 p q i xs)

{--
crypt-decrement-100-2cols : {l : Nat} → (p q : Nat) → (i : Fin l) → Vec Int l × Vec Int l → Vec Int l × Vec Int l
crypt-decrement-100-2cols p q () ([] , [])
crypt-decrement-100-2cols p q zero ((x1 :: xs1) , (x2 :: xs2)) = ((div x1 (paillier-encrypt'' p q 100)) :: xs1) , ((div x2 (paillier-encrypt'' p q 100)) :: xs2)
crypt-decrement-100-2cols p q (suc i) ((x1 :: xs1) , (x2 :: xs2)) = (x1 :: (crypt-decrement-100 p q i xs1)) , (x2 :: (crypt-decrement-100 p q i xs2))
--}

postulate
  crypt-inc-dec-inv : {p q : Nat} → (i : Nat) → (vec : List Int) → (crypt-increment-100 p q i (crypt-decrement-100 p q i vec)) ≡ vec
  crypt-dec-inc-inv : {p q : Nat} → (i : Nat) → (vec : List Int) → (crypt-decrement-100 p q i (crypt-increment-100 p q i vec)) ≡ vec

f∘g' : {p q : Nat} → (i : Nat) → List Int → List Int
f∘g' {p} {q} i = (crypt-increment-100 p q i) ○ (crypt-decrement-100 p q i)

α' : {p q : Nat} → (i : Nat) → (vec : List Int) → (f∘g' {p} {q} i vec) ≡ vec
α' {p} {q} i [] = begin
                    f∘g' {p} {q} zero [] ≡⟨ refl ⟩
                    ((crypt-increment-100 p q i) ○ (crypt-decrement-100 p q i)) [] ≡⟨ refl ⟩
                    (crypt-increment-100 p q i (crypt-decrement-100 p q i [])) ≡⟨ crypt-inc-dec-inv {p} {q} i [] ⟩
                    [] ∎
α' {p} {q} zero (x ∷ xs) = begin
                             f∘g' {p} {q} zero (x ∷ xs) ≡⟨ refl ⟩
                             ((crypt-increment-100 p q zero) ○ (crypt-decrement-100 p q zero)) (x ∷ xs) ≡⟨ refl ⟩
                             (crypt-increment-100 p q zero (crypt-decrement-100 p q zero (x ∷ xs))) ≡⟨ crypt-inc-dec-inv {p} {q} zero (x ∷ xs) ⟩
                             (x ∷ xs ∎) 
α' {p} {q} (suc i) (x ∷ xs) = ap (λ xs' → x ∷ xs') (α' i xs)

g∘f' : {p q : Nat} → (i : Nat) → List Int → List Int
g∘f' {p} {q} i = (crypt-decrement-100 p q i) ○ (crypt-increment-100 p q i)

β' : {p q : Nat} → (i : Nat) → (vec : List Int) → (g∘f' {p} {q} i vec) ≡ vec
β' {p} {q} i [] = begin
                    g∘f' {p} {q} i [] ≡⟨ refl ⟩
                    ((crypt-decrement-100 p q i) ○ (crypt-increment-100 p q i)) [] ≡⟨ refl ⟩
                    (crypt-decrement-100 p q i (crypt-increment-100 p q i [])) ≡⟨ crypt-dec-inc-inv {p} {q} i [] ⟩
                    [] ∎
β' {p} {q} zero (x ∷ xs) = begin
                              g∘f' {p} {q} zero (x ∷ xs) ≡⟨ refl ⟩
                              ((crypt-decrement-100 p q zero) ○ (crypt-increment-100 p q zero)) (x ∷ xs) ≡⟨ refl ⟩
                              (crypt-decrement-100 p q zero (crypt-increment-100 p q zero (x ∷ xs))) ≡⟨ crypt-dec-inc-inv {p} {q} zero (x ∷ xs) ⟩
                              (x ∷ xs ∎)
β' {p} {q} (suc i) (x ∷ xs) = ap (λ xs' → x ∷ xs') (β' i xs)


crypt-inc-equiv≃ : {p q : Nat} → (i : Nat) → (List Int ≃ List Int)
crypt-inc-equiv≃ {p} {q} i = crypt-increment-100 p q i , equiv₁ (mkqinv (crypt-decrement-100 p q i) (α' i) (β' i))

crypt-inc-path : {p q : Nat} → (i : Nat) → (List Int ≡ List Int)
crypt-inc-path {p} {q} i with univalence 
... | (_ , eq) = isequiv.g eq (crypt-inc-equiv≃ {p} {q} i)
