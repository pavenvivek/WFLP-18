{-# OPTIONS --type-in-type --without-K #-}

open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Patch_Theory.agda_lib.Utils
open import Patch_Theory.agda_lib.Vector
open import Patch_Theory.agda_lib.Equiv

module Patch_Theory.cryptography.RSA-Cryptosystem where

-- RSA Crypto-system

rsa-keygen-public : (p : Nat) → (q : Nat) → (Nat × Nat)
rsa-keygen-public p q = let euler-totient : Nat
                            euler-totient = (p - 1) * (q - 1)

                            n : Nat
                            n = p * q
                            
                        in coprime euler-totient , n


rsa-keygen-private : (p : Nat) → (q : Nat) → (Nat × Nat)
rsa-keygen-private p q =  let e : Nat
                              e = (proj₁ (rsa-keygen-public p q))

                              n : Nat
                              n = p * q

                              euler-totient : Nat
                              euler-totient = (p - 1) * (q - 1)
                              
                          in mod*-inv e euler-totient ,  p * q


rsa-encrypt' : (plain-text : Int) → (public-key : Nat × Nat) → Int
rsa-encrypt' plain-text (e , n) = mod (plain-text ^ e) n

rsa-encrypt'' : Nat → Nat → (plain-text : Int) → Int
rsa-encrypt'' p q plain-text = let public-key : Nat × Nat
                                   public-key = (rsa-keygen-public p q)
                               in (rsa-encrypt' plain-text public-key)
    
rsa-encrypt : Nat → Nat → (plain-text : List Int) → List Int
rsa-encrypt p q plain-text = loop {Int} (rsa-encrypt'' p q) plain-text

rsa-encrypt-2cols : Nat → Nat → (plain-text : List Int × List Int) → List Int × List Int
rsa-encrypt-2cols p q (plain-text-col1 , plain-text-col2) = loop {Int} (rsa-encrypt'' p q) plain-text-col1 , loop {Int} (rsa-encrypt'' p q) plain-text-col2

rsa-decrypt' : (cipher-text : Int) → (private-key : Nat × Nat) → Int
rsa-decrypt' cipher-text (d , n) = mod (cipher-text ^ d) n

rsa-decrypt'' : Nat → Nat → (cipher-text : Int) → Int
rsa-decrypt'' p q cipher-text = let private-key : Nat × Nat
                                    private-key = (rsa-keygen-private p q)
                                in (rsa-decrypt' cipher-text private-key) 

rsa-decrypt : Nat → Nat → (cipher-text : List Int) → List Int
rsa-decrypt p q cipher-text = loop {Int} (rsa-decrypt'' p q) cipher-text

rsa-decrypt-2cols : Nat → Nat → (cipher-text : List Int × List Int) → List Int × List Int
rsa-decrypt-2cols p q (cipher-text-col1 , cipher-text-col2) = loop {Int} (rsa-decrypt'' p q) cipher-text-col1 , loop {Int} (rsa-decrypt'' p q) cipher-text-col2

postulate
  rsa-dec-enc-inv : {p q : Nat} → (message : List Int) → (rsa-decrypt p q (rsa-encrypt p q message)) ≡ message
  rsa-enc-dec-inv : {p q : Nat} → (cipher : List Int) → (rsa-encrypt p q (rsa-decrypt p q cipher)) ≡ cipher

f∘g[rsa] : {p q : Nat} → List Int → List Int
f∘g[rsa] {p} {q} = (rsa-encrypt p q) ○ (rsa-decrypt p q)


α-rsa : {p q : Nat} → f∘g[rsa] {p} {q} ∼ id
α-rsa {p} {q} = indList (λ v → f∘g[rsa] {p} {q} v ≡ v)
                       refl
                       (λ x xs p1 → indNat (λ x1 → f∘g[rsa] {p} {q} (x1 ∷ xs) ≡ x1 ∷ xs)
                                      (begin
                                       f∘g[rsa] {p} {q} (0 ∷ xs) ≡⟨ refl ⟩
                                       (rsa-encrypt p q ○ rsa-decrypt p q) (0 ∷ xs) ≡⟨ refl ⟩
                                       rsa-encrypt p q (rsa-decrypt p q (0 ∷ xs)) ≡⟨
                                       rsa-enc-dec-inv {p} {q} (0 ∷ xs) ⟩ (0 ∷ xs ∎))
                                      (λ n pn →
                                         begin
                                         f∘g[rsa] {p} {q} (suc n ∷ xs) ≡⟨ refl ⟩
                                         (rsa-encrypt p q ○ rsa-decrypt p q) (suc n ∷ xs) ≡⟨ refl ⟩
                                         rsa-encrypt p q (rsa-decrypt p q (suc n ∷ xs)) ≡⟨
                                         rsa-enc-dec-inv {p} {q} (suc n ∷ xs) ⟩ (suc n ∷ xs ∎))
                                      x)

g∘f[rsa] : {p q : Nat} → List Int → List Int
g∘f[rsa] {p} {q} = (rsa-decrypt p q) ○ (rsa-encrypt p q)

β-rsa : {p q : Nat} → g∘f[rsa] {p} {q} ∼ id
β-rsa {p} {q} = indList (λ v → g∘f[rsa] {p} {q} v ≡ v)
                           refl
                           (λ x xs p1 → indNat (λ x₁ → g∘f[rsa] {p} {q} (x₁ ∷ xs) ≡ x₁ ∷ xs)
                                          (begin
                                           g∘f[rsa] {p} {q} (0 ∷ xs) ≡⟨ refl ⟩
                                           (rsa-decrypt p q ○ rsa-encrypt p q) (0 ∷ xs) ≡⟨ refl ⟩
                                           rsa-decrypt p q (rsa-encrypt p q (0 ∷ xs)) ≡⟨
                                           rsa-dec-enc-inv {p} {q} (0 ∷ xs) ⟩ (0 ∷ xs ∎))
                                          (λ n pn →
                                             begin
                                             g∘f[rsa] {p} {q} (suc n ∷ xs) ≡⟨ refl ⟩
                                             (rsa-decrypt p q ○ rsa-encrypt p q) (suc n ∷ xs) ≡⟨ refl ⟩
                                             rsa-decrypt p q (rsa-encrypt p q (suc n ∷ xs)) ≡⟨
                                             rsa-dec-enc-inv {p} {q} (suc n ∷ xs) ⟩ (suc n ∷ xs ∎))
                                          x)


rsa-equiv≃ : {p q : Nat} → (List Int ≃ List Int)
rsa-equiv≃ {p} {q} = rsa-encrypt p q , equiv₁ (mkqinv (rsa-decrypt p q) (α-rsa {p} {q}) (β-rsa {p} {q}))

rsa-path : {p q : Nat} → (List Int ≡ List Int)
rsa-path {p} {q} with univalence 
... | (_ , eq) = isequiv.g eq (rsa-equiv≃ {p} {q})
