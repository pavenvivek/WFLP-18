{-# OPTIONS --type-in-type --without-K #-}

open import Data.Bool
open import Data.List
open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Patch_Theory.agda_lib.Utils
open import Patch_Theory.agda_lib.Vector
open import Patch_Theory.agda_lib.Equiv

open import Patch_Theory.cryptography.OPE-Cryptosystem

module Patch_Theory.cryptography.ElGamal-Cryptosystem where

-- ElGamal Crypto-system

ElGamal-keygen : (p : Nat) → (Nat × (Nat × Nat)) × Nat
ElGamal-keygen p = let g : Nat
                       g = (getRand p)

                       x : Nat
                       x = (getRand p)

                   in (((mod (g ^ x) p) , (p , g)) , x)

ElGamal-keygen-public : (p : Nat) → (Nat × (Nat × Nat))
ElGamal-keygen-public p = proj₁ (ElGamal-keygen p)

ElGamal-keygen-private : (p : Nat) → Nat
ElGamal-keygen-private p = proj₂ (ElGamal-keygen p)

ElGamal-secret-message : (p : Nat) → (plain-text : Nat) → Nat × Nat
ElGamal-secret-message p plain-text = (mod plain-text p , plain-text)

ElGamal-encrypt' : (plain-text : Nat) → (public-key : Nat × (Nat × Nat)) → (Nat × Nat) × Nat
ElGamal-encrypt' plain-text (h , (p , g)) = let y : Nat
                                                y = getRand p
                                            in (((mod (g ^ y) p) , (mod ((h ^ y) * (proj₁ (ElGamal-secret-message p plain-text))) p)) ,
                                               (ope-encrypt' (proj₂ (ElGamal-secret-message p plain-text))))

ElGamal-encrypt'' : (p : Nat) → (plain-text : Int) → (Int × Int) × Int
ElGamal-encrypt'' p plain-text = let public-key : Nat × (Nat × Nat)
                                     public-key = (ElGamal-keygen-public p)
                                 in (ElGamal-encrypt' plain-text public-key)

ElGamal-encrypt : (p : Nat) → (plain-text : List Int) → List ((Int × Int) × Int)
ElGamal-encrypt p plain-text = loop {Int} (ElGamal-encrypt'' p) plain-text

ElGamal-encrypt-2cols : (p : Nat) → (plain-text : List Int × List Int) → (List ((Int × Int) × Int)) × (List ((Int × Int) × Int))
ElGamal-encrypt-2cols p (plain-text-col1 , plain-text-col2) = loop {Int} (ElGamal-encrypt'' p) plain-text-col1 , loop {Int} (ElGamal-encrypt'' p) plain-text-col2

ElGamal-decrypt' : (cipher-text : (Int × Int) × Int) → (p : Nat) → (private-key : Nat) → Int
ElGamal-decrypt' ((c1 , c2) , cm) p x = let m' : Nat
                                            m' = mod ((c1 ^ ((p - 1) - x)) * c2) p

                                            m : Nat
                                            m = ope-decrypt'' cm
                                            
                                        in (if ((mod m p) == m') then m else (abort failed))
                                          
ElGamal-decrypt'' : (p : Nat) → (cipher-text : (Int × Int) × Int) → Int
ElGamal-decrypt'' p cipher-text = let private-key : Nat
                                      private-key = (ElGamal-keygen-private p)
                                  in (ElGamal-decrypt' cipher-text p private-key)

ElGamal-decrypt : (p : Nat) → (cipher-text : List ((Int × Int) × Int)) → List Int
ElGamal-decrypt p cipher-text = loop {(Int × Int) × Int} {Int} (ElGamal-decrypt'' p) cipher-text

ElGamal-decrypt-2cols : (p : Nat) → (cipher-text : (List ((Int × Int) × Int)) × (List ((Int × Int) × Int))) → List Int × List Int
ElGamal-decrypt-2cols p (cipher-text-col1 , cipher-text-col2) = loop {(Int × Int) × Int} {Int} (ElGamal-decrypt'' p) cipher-text-col1 ,
                                                                    loop {(Int × Int) × Int} {Int} (ElGamal-decrypt'' p) cipher-text-col2


ElGamal-encrypt2' : (ct : (Int × Int) × Int) → Int
ElGamal-encrypt2' ct = let c1 : Nat
                           c1 = proj₁ (proj₁ ct) 

                           c2 : Nat
                           c2 = proj₂ (proj₁ ct)

                           x : Nat
                           x = proj₂ ct

                       in (((c1 * 100) + c2) * 1000000000) + x

ElGamal-encrypt2 : (p : Nat) → (ct : List ((Int × Int) × Int)) → List Int
ElGamal-encrypt2 p ct = loop {(Int × Int) × Int} {Int} ElGamal-encrypt2' ct

ElGamal-encrypt2-2cols : (p : Nat) → (List ((Int × Int) × Int)) × (List ((Int × Int) × Int)) → List Int × List Int
ElGamal-encrypt2-2cols p (ct1 , ct2) = loop {(Int × Int) × Int} {Int} ElGamal-encrypt2' ct1 , loop {(Int × Int) × Int} {Int} ElGamal-encrypt2' ct2

ElGamal-decrypt2' : Int → (Int × Int) × Int
ElGamal-decrypt2' enc-int = let c1 : Nat
                                c1 = div enc-int 100000000000
                                       
                                c2 : Nat
                                c2 = mod (div enc-int 1000000000) 100
                                       
                                x : Nat
                                x = mod enc-int 1000000000
                                       
                            in (c1 , c2) , x

ElGamal-decrypt2 : (p : Nat) → List Int → List ((Int × Int) × Int)
ElGamal-decrypt2 p enc-int = loop {Int} ElGamal-decrypt2' enc-int

ElGamal-decrypt2-2cols : (p : Nat) → List Int × List Int → (List ((Int × Int) × Int)) × (List ((Int × Int) × Int))
ElGamal-decrypt2-2cols p (p1 , p2) = loop {Int} ElGamal-decrypt2' p1 , loop {Int} ElGamal-decrypt2' p2

postulate
  ElGamal-dec-enc-inv : {p : Nat} → (message : List Int) → (ElGamal-decrypt p (ElGamal-encrypt p message)) ≡ message
  ElGamal-enc-dec-inv : {p : Nat} → (cipher : List ((Int × Int) × Int)) → (ElGamal-encrypt p (ElGamal-decrypt p cipher)) ≡ cipher

f∘g[ElGamal] : {p : Nat} → List ((Int × Int) × Int) → List ((Int × Int) × Int)
f∘g[ElGamal] {p} = (ElGamal-encrypt p) ○ (ElGamal-decrypt p)


α-ElGamal : {p : Nat} → f∘g[ElGamal] {p} ∼ id
α-ElGamal {p} = indList (λ v → f∘g[ElGamal] {p} v ≡ v)
                       refl
                       (λ x xs p1 → ind× (λ x1 → f∘g[ElGamal] {p} (x1 ∷ xs) ≡ x1 ∷ xs)
                                          (λ a b → (begin
                                                       f∘g[ElGamal] {p} ((a , b) ∷ xs) ≡⟨ refl ⟩
                                                       ((ElGamal-encrypt p) ○ (ElGamal-decrypt p)) ((a , b) ∷ xs) ≡⟨ refl ⟩
                                                       (ElGamal-encrypt p (ElGamal-decrypt p ((a , b) ∷ xs))) ≡⟨ (ElGamal-enc-dec-inv {p} ((a , b) ∷ xs)) ⟩
                                                       ((a , b) ∷ xs) ∎))
                                          x )

g∘f[ElGamal] : {p : Nat} → List Int → List Int
g∘f[ElGamal] {p} = (ElGamal-decrypt p) ○ (ElGamal-encrypt p)

β-ElGamal : {p : Nat} → g∘f[ElGamal] {p} ∼ id
β-ElGamal {p} = indList (λ v → g∘f[ElGamal] {p} v ≡ v)
                           refl
                           (λ x xs p1 → indNat (λ x₁ → g∘f[ElGamal] {p} (x₁ ∷ xs) ≡ x₁ ∷ xs)
                                          (begin
                                           g∘f[ElGamal] {p} (0 ∷ xs) ≡⟨ refl ⟩
                                           (ElGamal-decrypt p ○ ElGamal-encrypt p) (0 ∷ xs) ≡⟨ refl ⟩
                                           ElGamal-decrypt p (ElGamal-encrypt p (0 ∷ xs)) ≡⟨ ElGamal-dec-enc-inv {p} (0 ∷ xs) ⟩
                                           (0 ∷ xs ∎))
                                          (λ n pn →
                                             begin
                                             g∘f[ElGamal] {p} (suc n ∷ xs) ≡⟨ refl ⟩
                                             (ElGamal-decrypt p ○ ElGamal-encrypt p) (suc n ∷ xs) ≡⟨ refl ⟩
                                             ElGamal-decrypt p (ElGamal-encrypt p (suc n ∷ xs)) ≡⟨ ElGamal-dec-enc-inv {p} (suc n ∷ xs) ⟩
                                             (suc n ∷ xs ∎))
                                          x)

ElGamal-equiv≃ : {p : Nat} → (List Int ≃ List ((Int × Int) × Int))
ElGamal-equiv≃ {p} = ElGamal-encrypt p , equiv₁ (mkqinv (ElGamal-decrypt p) (α-ElGamal {p}) (β-ElGamal {p}))

ElGamal-path : {p : Nat} → (List Int ≡ List ((Int × Int) × Int))
ElGamal-path {p} with univalence 
... | (_ , eq) = isequiv.g eq (ElGamal-equiv≃ {p})

