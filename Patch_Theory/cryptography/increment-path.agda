{-# OPTIONS --type-in-type --without-K #-}

open import Function renaming (_∘_ to _○_)
open import Data.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Patch_Theory.agda_lib.Utils
open import Patch_Theory.agda_lib.Vector
open import Patch_Theory.agda_lib.Equiv
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

module Patch_Theory.cryptography.increment-path where

--  increments the given vector by 100

increment-100 : (i : Nat) → List Int → List Int
increment-100 i [] = []
increment-100 zero (x ∷ xs) = (x + 100) ∷ xs
increment-100 (suc i) (x ∷ xs) = x ∷ (increment-100 i xs)

{--
increment-100-2cols : (i : Nat) → List Int × List Int → List Int × List Int
increment-100-2cols zero ((x1 ∷ xs1) , (x2 ∷ xs2)) = ((x1 + 100) ∷ xs1) , ((x2 + 100) ∷ xs2)
increment-100-2cols (suc i) ((x1 ∷ xs1) , (x2 ∷ xs2)) = (x1 ∷ (increment-100 i xs1)) , (x2 ∷ (increment-100 i xs2))
increment-100-2cols i (x , y) = (x , y)
--}

decrement-100 : (i : Nat) → List Int → List Int
decrement-100 i [] = []
decrement-100 zero (x ∷ xs) = (x - 100) ∷ xs
decrement-100 (suc i) (x ∷ xs) = x ∷ (decrement-100 i xs)

{--
decrement-100-2cols : (i : Nat) → List Int × List Int → List Int × List Int
decrement-100-2cols zero ((x1 ∷ xs1) , (x2 ∷ xs2)) = ((x1 - 100) ∷ xs1) , ((x2 - 100) ∷ xs2)
decrement-100-2cols (suc i) ((x1 ∷ xs1) , (x2 ∷ xs2)) = (x1 ∷ (decrement-100 i xs1)) , (x2 ∷ (decrement-100 i xs2))
decrement-100-2cols i (x , y) = ([] , [])
--}

postulate
  sub-add-assoc : (x y : Nat) → ((x - y) + y) ≡ (x + (y - y))
  add-sub-assoc : (x y : Nat) → ((x + y) - y) ≡ (x + (y - y))
  sub-0 : (x : Nat) → x - 0 ≡ x
  sub-n : (x : Nat) → x - x ≡ 0

add-0 : (x : Nat) → x + 0 ≡ x
add-0 = indNat (λ x → (x + 0) ≡ x)
               refl
               (λ x p → ap suc p)


add-sub-n : (y x : Nat) → ((x - y) + y) ≡ x
add-sub-n = indNat (λ y → (x : Nat) → ((x - y) +  y) ≡ x)
                    (λ x → (begin
                              x - 0 + 0 ≡⟨ ap (λ x1 → x1 + 0) (sub-0 x) ⟩
                              x + 0 ≡⟨ add-0 x ⟩
                              x ∎))
                    (λ y p x → (begin
                                  x - suc y + suc y ≡⟨ sub-add-assoc x (suc y) ⟩
                                  x + (suc y - suc y) ≡⟨ ap (λ y1 → x + y1) (sub-n (suc y)) ⟩
                                  x + 0 ≡⟨ add-0 x ⟩
                                  x ∎))


inc-dec-inv : (i : Nat) → (vec : List Int) → (increment-100 i (decrement-100 i vec) ≡ vec)
inc-dec-inv i [] = (begin
                      (increment-100 i (decrement-100 i [])) ≡⟨ refl ⟩
                      (increment-100 i []) ≡⟨ refl ⟩
                      [] ∎)
inc-dec-inv zero (x ∷ xs) = (begin
                               (increment-100 zero (decrement-100 zero (x ∷ xs))) ≡⟨ refl ⟩
                               (increment-100 zero ((x - 100) ∷ xs)) ≡⟨ refl ⟩
                               (x - 100 + 100) ∷ xs ≡⟨ ap (λ x1 → x1 ∷ xs) (add-sub-n 100 x) ⟩
                               (x ∷ xs) ∎)
inc-dec-inv (suc i) (x ∷ xs) = ap (λ xs' → x ∷ xs') (inc-dec-inv i xs)

dec-inc-inv : (i : Nat) → (vec : List Int) → (decrement-100 i (increment-100 i vec) ≡ vec)
dec-inc-inv i [] = (begin
                      (decrement-100 i (increment-100 i [])) ≡⟨ refl ⟩
                      (decrement-100 i []) ≡⟨ refl ⟩
                      [] ∎)
dec-inc-inv zero (x ∷ xs) = (begin
                               (decrement-100 zero (increment-100 zero (x ∷ xs))) ≡⟨ refl ⟩
                               (decrement-100 zero ((x + 100) ∷ xs)) ≡⟨ refl ⟩
                               (x + 100 - 100) ∷ xs ≡⟨ ap (λ x1 → x1 ∷ xs) (add-sub-assoc x 100) ⟩
                               (x + (100 - 100)) ∷ xs ≡⟨ refl ⟩
                               (x + 0) ∷ xs ≡⟨ ap (λ x1 → x1 ∷ xs) (add-0 x) ⟩
                               (x ∷ xs) ∎)
dec-inc-inv (suc i) (x ∷ xs) = ap (λ xs' → x ∷ xs') (dec-inc-inv i xs)

f∘g : (i : Nat) → List Int → List Int
f∘g i = (increment-100 i) ○ (decrement-100 i)

α : (i : Nat) → (vec : List Int) → (f∘g i vec) ≡ vec
α i [] = begin
           f∘g i [] ≡⟨ refl ⟩
           ((increment-100 i) ○ (decrement-100 i)) [] ≡⟨ refl ⟩
           (increment-100 i (decrement-100 i [])) ≡⟨ inc-dec-inv i [] ⟩
           [] ∎
α zero (x ∷ xs) = begin
                     f∘g zero (x ∷ xs) ≡⟨ refl ⟩
                     ((increment-100 zero) ○ (decrement-100 zero)) (x ∷ xs) ≡⟨ refl ⟩
                     (increment-100 zero (decrement-100 zero (x ∷ xs))) ≡⟨ inc-dec-inv zero (x ∷ xs) ⟩
                     (x ∷ xs ∎) 
α (suc i) (x ∷ xs) = ap (λ xs' → x ∷ xs') (α i xs)

g∘f : (i : Nat) → List Int → List Int
g∘f i = (decrement-100 i) ○ (increment-100 i)

β : (i : Nat) → (vec : List Int) → (g∘f i vec) ≡ vec
β i [] = begin
           g∘f i [] ≡⟨ refl ⟩
           ((decrement-100 i) ○ (increment-100 i)) [] ≡⟨ refl ⟩
           (decrement-100 i (increment-100 i [])) ≡⟨ dec-inc-inv i [] ⟩
           [] ∎
β zero (x ∷ xs) = begin
                     g∘f zero (x ∷ xs) ≡⟨ refl ⟩
                     ((decrement-100 zero) ○ (increment-100 zero)) (x ∷ xs) ≡⟨ refl ⟩
                     (decrement-100 zero (increment-100 zero (x ∷ xs))) ≡⟨ dec-inc-inv zero (x ∷ xs) ⟩
                     (x ∷ xs ∎)
β (suc i) (x ∷ xs) = ap (λ xs' → x ∷ xs') (β i xs)

inc-equiv≃ : (i : Nat) → (List Int ≃ List Int)
inc-equiv≃ i = increment-100 i , equiv₁ (mkqinv (decrement-100 i) (α i) (β i))

inc-path : (i : Nat) → (List Int ≡ List Int)
inc-path i with univalence 
... | (_ , eq) = isequiv.g eq (inc-equiv≃ i)

