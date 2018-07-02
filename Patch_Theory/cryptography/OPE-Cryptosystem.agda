{-# OPTIONS --type-in-type --without-K --no-termination-check #-}

open import Function renaming (_∘_ to _○_)

open import Data.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Patch_Theory.agda_lib.Utils
open import Patch_Theory.agda_lib.Vector
open import Patch_Theory.agda_lib.Equiv

open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

module Patch_Theory.cryptography.OPE-Cryptosystem where

-- Order-Preserving Encryption (OPE)

ope-keygen-symmetric : Nat
ope-keygen-symmetric = 23

ope-encrypt' : (plain-text : Int) → Int
ope-encrypt' 0 = ope-keygen-symmetric
ope-encrypt' (suc n) = (ope-encrypt' n) + suc n

ope-encrypt : (plain-text : List Int) → List Int
ope-encrypt plain-text = loop {Int} ope-encrypt' plain-text

ope-encrypt-2cols : (plain-text : List Int × List Int) → List Int × List Int
ope-encrypt-2cols (plain-text-col1 , plain-text-col2) = loop {Int} ope-encrypt' plain-text-col1 , loop {Int} ope-encrypt' plain-text-col2

ope-decrypt' : {sub-val : Int} → (cipher-text : Int) → Int
ope-decrypt' {sub-val} 0 = (sub-val - 1)
ope-decrypt' {sub-val} (suc n) = ope-decrypt' {(sub-val + 1)} ((suc n) - sub-val)

ope-decrypt'' : (cipher-text : Int) → Int
ope-decrypt'' cipher-text = ope-decrypt' {1} (cipher-text - ope-keygen-symmetric)

ope-decrypt : (cipher-text : List Int) → List Int
ope-decrypt cipher-text = loop {Int} ope-decrypt'' cipher-text

ope-decrypt-2cols : (cipher-text : List Int × List Int) → List Int × List Int
ope-decrypt-2cols (cipher-text-col1 , cipher-text-col2) = loop {Int} ope-decrypt'' cipher-text-col1 , loop {Int} ope-decrypt'' cipher-text-col2

postulate
  ope-dec-enc-inv : (message : List Int) → (ope-decrypt (ope-encrypt message)) ≡ message
  ope-enc-dec-inv : (cipher : List Int) → (ope-encrypt (ope-decrypt cipher)) ≡ cipher

f∘g[ope] : List Int → List Int
f∘g[ope] = ope-encrypt ○ ope-decrypt

α-ope : f∘g[ope] ∼ id
α-ope = indList {Int} (λ v → f∘g[ope] v ≡ v)
                       refl
                       (λ x xs p1 → indNat (λ x1 → f∘g[ope] (x1 ∷ xs) ≡ x1 ∷ xs)
                                      (begin
                                       f∘g[ope] (0 ∷ xs) ≡⟨ refl ⟩
                                       (ope-encrypt ○ ope-decrypt) (0 ∷ xs) ≡⟨ refl ⟩
                                       ope-encrypt (ope-decrypt (0 ∷ xs)) ≡⟨ ope-enc-dec-inv (0 ∷ xs) ⟩
                                       (0 ∷ xs ∎))
                                      (λ n pn →
                                         begin
                                         f∘g[ope] (suc n ∷ xs) ≡⟨ refl ⟩
                                         (ope-encrypt ○ ope-decrypt) (suc n ∷ xs) ≡⟨ refl ⟩
                                         ope-encrypt (ope-decrypt (suc n ∷ xs)) ≡⟨ ope-enc-dec-inv (suc n ∷ xs) ⟩
                                         (suc n ∷ xs ∎))
                                      x)


g∘f[ope] : List Int → List Int
g∘f[ope] = ope-decrypt ○ ope-encrypt

β-ope : g∘f[ope] ∼ id
β-ope = indList {Int} (λ v → g∘f[ope] v ≡ v)
                           refl
                           (λ x xs p1 → indNat (λ x₁ → g∘f[ope] (x₁ ∷ xs) ≡ x₁ ∷ xs)
                                          (begin
                                           g∘f[ope] (0 ∷ xs) ≡⟨ refl ⟩
                                           (ope-decrypt ○ ope-encrypt) (0 ∷ xs) ≡⟨ refl ⟩
                                           ope-decrypt (ope-encrypt (0 ∷ xs)) ≡⟨ ope-dec-enc-inv (0 ∷ xs) ⟩
                                           (0 ∷ xs ∎))
                                          (λ n pn →
                                             begin
                                             g∘f[ope] (suc n ∷ xs) ≡⟨ refl ⟩
                                             (ope-decrypt ○ ope-encrypt) (suc n ∷ xs) ≡⟨ refl ⟩
                                             ope-decrypt (ope-encrypt (suc n ∷ xs)) ≡⟨ ope-dec-enc-inv (suc n ∷ xs) ⟩
                                             (suc n ∷ xs ∎))
                                          x)


ope-equiv≃ : (List Int ≃ List Int)
ope-equiv≃ = ope-encrypt , equiv₁ (mkqinv ope-decrypt α-ope β-ope)

ope-path : List Int ≡ List Int
ope-path with univalence 
... | (_ , eq) = isequiv.g eq ope-equiv≃
