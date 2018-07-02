{-# OPTIONS --type-in-type #-}

open import Function renaming (_∘_ to _○_)
open import Agda.Builtin.Equality

module Automation.utils.pathUtils where

infixr 8  _∘_     -- path composition
-- infix  4  _≡_     -- propositional equality
infix  4  _∼_     -- homotopy between two functions 
infix  4  _≃_     -- type of equivalences

-- Equational Reasoning

infix  2  begin_
infix  4  _∎  
infixr 3  _≡⟨_⟩_

------------------------------------------------------------------------------
-- A few HoTT primitives

-- data _≡_ {A : Set} : (a b : A) → Set where
--   refl : (a : A) → (a ≡ a)

Path : {A : Set} → A → A → Set
Path a b = (a ≡ b)

pathInd : {A : Set} → 
          (C : {x y : A} → x ≡ y → Set) → 
          (c : {x : A} → C {x} {x} refl) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c refl = c

basePathInd : {A : Set} → {a : A} →  
          (C : {x : A} → a ≡ x → Set) → 
          (c : C {a} refl) → 
          ({x : A} (p : a ≡ x) → C p)
basePathInd C c refl = c


cong : {A : Set} {B : Set}
       (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

--

! : {A : Set} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

_∘_ : {A : Set} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {A} {x} {y} {z} p q = 
  pathInd
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ {x} z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

--

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl) 
unitTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ p ∘ refl) 
    (λ {x} → refl) -- (refl x))
    {x} {y} p 

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl ∘ p) 
unitTransL {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ refl ∘ p)
    (λ {x} → refl) -- (refl x))
    {x} {y} p 

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl)
invTransL {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ! p ∘ p ≡ refl)
    (λ {x} → refl) -- (refl x))
    {x} {y} p

invTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ∘ ! p ≡ refl)
invTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ∘ ! p ≡ refl)
    (λ {x} → refl) -- (refl x))
    {x} {y} p

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd 
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ {x} → refl) -- (refl x))
    {x} {y} p

assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP {A} {x} {y} {z} {w} p q r =
  pathInd
    (λ {x} {y} p → (z : A) → (w : A) → (q : y ≡ z) → (r : z ≡ w) → 
      p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
    (λ {x} z w q r → 
      pathInd
        (λ {x} {z} q → (w : A) → (r : z ≡ w) → 
          refl ∘ (q ∘ r) ≡ (refl ∘ q) ∘ r)
        (λ {x} w r → 
          pathInd
            (λ {x} {w} r → 
              refl ∘ (refl ∘ r) ≡ 
              (refl ∘ refl) ∘ r)
            (λ {x} → refl) -- (refl x)))
            {x} {w} r)
        {x} {z} q w r)
    {x} {y} p z w q r

invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → 
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp {A} {x} {y} {z} p q = 
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p)
    (λ {x} z q → 
      pathInd 
        (λ {x} {z} q → ! (refl ∘ q) ≡ ! q ∘ ! refl)
        (λ {x} → refl) 
        {x} {z} q)
    {x} {y} p z q

-- Equational Reasoning operators

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin_ p1 = p1

_≡⟨_⟩_ : {A : Set} → (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p1 ⟩ p2 = p1 ∘ p2

_∎ : {A : Set} → (a : A) → a ≡ a
_∎ a = refl

--

ap : {A : Set} {B : Set } {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → f x ≡ f y) 
    (λ {x} → refl) -- (f x))
    {x} {y} p

apfTrans : {A B : Set} {x y z : A} → 
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans {A} {B} {x} {y} {z} f p q = 
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → 
      ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q))
    (λ {x} z q → 
      pathInd
        (λ {x} {z} q → 
          ap f (refl ∘ q) ≡ (ap f refl) ∘ (ap f q))
        (λ {x} → refl) -- (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

apfInv : {A B : Set} {x y : A} → (f : A → B) → (p : x ≡ y) → 
         ap f (! p) ≡ ! (ap f p) 
apfInv {A} {B} {x} {y} f p =
  pathInd
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ {x} → refl) -- (ap f (refl x)))
    {x} {y} p

apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ○ f) p 
apfComp {A} {B} {C} {x} {y} f g p =
  pathInd 
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ○ f) p)
    (λ {x} → refl) -- (ap g (ap f (refl x))))
    {x} {y} p

apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ap id p ≡ p)
    (λ {x} → refl) -- (refl x))
    {x} {y} p

--

transport : {A : Set } {x y : A} → 
  (P : A → Set) → (p : x ≡ y) → P x → P y
transport {A} {x} {y} P p = 
  pathInd -- on p
    (λ {x} {y} p → (P x → P y))
    (λ {_} → id)
    {x} {y} p

apd : {A : Set} {B : A → Set} {x y : A} → (f : (a : A) → B a) → 
  (p : x ≡ y) → (transport B p (f x) ≡ f y)
apd {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → transport B p (f x) ≡ f y)
    (λ {x} → refl) -- (f x))
    {x} {y} p

ap' : {A : Set} {B : A → Set} {C : A → Set} →
  {x y : A} → {u : B x} → {v : B y} → (g : {a : A} → B a → C a) → {p : x ≡ y} →
  (transport B p u ≡ v) → transport C p (g u) ≡ (g v)
ap' g {refl} q = ap g q

Π : (A : Set) (B : A → Set) → Set
Π A B = (x : A) → B x

apd-∘' : {A : Set} {B : A → Set} {C : A → Set} → {x y : A} →
         (g : {a : A} → B a → C a) → (f : (a : A) → B a) → (p : x ≡ y) → (apd (g ○ f) p) ≡ (ap' g {p} (apd f p))
apd-∘' g f refl = refl

-- Homotopies and equivalences

_∼_ : {A : Set} {P : A → Set} → 
      (f g : (x : A) → P x) → Set
_∼_ {A} {P} f g = (x : A) → f x ≡ g x

record qinv {A : Set} {B : Set} (f : A → B) : 
  Set where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

record isequiv {A : Set} {B : Set} (f : A → B) : 
  Set where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : {A : Set} {B : Set} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ

record Σe (A : Set) (B : A -> Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst
open Σe public

_≃_ : (A : Set) (B : Set) → Set
A ≃ B = Σe (A → B) isequiv

postulate 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)
  ua : {A B : Set} → A ≃ B → A ≡ B

pair= : {A : Set} {B : A → Set}
  {a a' : A} → (p : a ≡ a') → {b : B a} → {b' : B a'} →
  (q : transport B p b ≡ b') → (a , b) ≡ (a' , b')
pair= refl q = ap (λ x → _ , _) q

apd' : {A : Set} {B : A → Set} {C : {a : A} → B a → Set} →
  {x y : A} → {u : B x} → {v : B y} → (f : {a : A} → (b : B a) → C {a} b) → {p : x ≡ y} →
  (q : transport B p u ≡ v) → transport (λ xy → C {fst xy} (snd xy)) (pair= p q) (f u) ≡ (f v)
apd' f {refl} refl = refl

transportId : {A B : Set} {y z : A} → (f g : A → B) → 
  (p : y ≡ z) → (q : f y ≡ g y) → 
  transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ (q ∘ (ap g p))
transportId {A} {B} {y} {z} f g p q = 
            pathInd -- on p 
              (λ {y} {z} p → (q : f y ≡ g y) → 
                transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ (q ∘ (ap g p)))
              (λ {p} q →  transport (λ x → f x ≡ g x) refl q   ≡⟨ refl ⟩
                        q                                        ≡⟨ unitTransR q ⟩
                        q ∘ (ap g refl)                      ≡⟨ unitTransL (q ∘ (ap g refl)) ⟩ 
                        (ap f refl) ∘ q ∘ (ap g refl)    ≡⟨ refl ⟩
                        ! (ap f refl) ∘ (q ∘ (ap g refl)) ∎)
              p q

-- Identity type Transport theorem 
transport' : {A B : Set} {a y z : A} → (f : A → B) → (p : y ≡ z) → (q : f a ≡ f y) → transport (λ x → f a ≡ f x) p q ≡ (q ∘ (ap f p))
transport' {A} {B} {a} {y} {z} f p q = pathInd (λ {y} {z} p → (q : f a ≡ f y) → transport (λ x → f a ≡ f x) p q ≡ (q ∘ (ap f p)))
                                                    (λ {p} q →  transport (λ x → f a ≡ f x) refl q ≡⟨ refl ⟩
                                                                 q ≡⟨ unitTransR q ⟩
                                                                (q ∘ (ap f refl)) ∎)
                                                    p q

coe-biject : {A B : Set} → (A ≡ B) → (A ≃ B)
coe-biject path with univalence 
... | (f , eq) = f path

coe' : {A B : Set} → (A ≡ B) → (A → B)
coe' path = fst (coe-biject path)

postulate
  apI-path : {A : Set} → {a b : A} → {p q : a ≡ b} → (f : A → Set) → (x : p ≡ q) → (f a ≡ f b) ≡ (f a ≡ f b)

data Singleton {A : Set} (x : A) : Set where
  _with≡_ : (y : A) → x ≡ y → Singleton x

to-Singleton : {A B : Set} {a : A} → (f : A → B) → Singleton a → Singleton (f a)
to-Singleton {a} f (x with≡ p) = (f x with≡ ap f p)

inspect : {A : Set} (x : A) → Singleton x
inspect x = x with≡ refl

postulate
  singleton-equiv : {A B : Set} {f : A → B} {m : A} → (Singleton m → Singleton (f m)) → Singleton m ≃ Singleton (f m)

–> : {A B : Set} → (e : A ≃ B) → (A → B)
–> e = fst e

<– : {A B : Set} → (e : A ≃ B) → (B → A)
<– e = isequiv.g (snd e)

postulate
  α-e : {A B C : Set} → (e1 : B ≃ C) → (e2 : A ≃ B) → ((–> e1 ○ –> e2) ○ (<– e2 ○ <– e1)) ∼ id
-- α-e = {!!}

  β-e : {A B C : Set} → (e1 : B ≃ C) → (e2 : A ≃ B) → ((<– e2 ○ <– e1) ○ (–> e1 ○ –> e2)) ∼ id
-- β-e = {!!}

_∘e_ : {A B C : Set} → B ≃ C → A ≃ B → A ≃ C
e1 ∘e e2 = (–> e1 ○ –> e2) , equiv₁ (mkqinv (<– e2 ○ <– e1) (α-e e1 e2) (β-e e1 e2))

_∘e'_ : {A B C : Set} → {f2 : B → C} → {f1 : A → B} → {m : A} → Singleton (f1 m) ≃ Singleton ((f2 ○ f1) m) → Singleton m ≃ Singleton (f1 m) → Singleton m ≃ Singleton ((f2 ○ f1) m)
_∘e'_ {A} {B} {C} {f2} {f1} {m} e1 e2 = (singleton-equiv {A} {C} {(f2 ○ f1)} {m} (to-Singleton (f2 ○ f1)))

-- (–> e1 ○ –> e2) , equiv₁ (mkqinv (<– e2 ○ <– e1) (α-e e1 e2) (β-e e1 e2)) -- (α-e e1 e2) (β-e e1 e2))

postulate
  ua-∘e : {A B C : Set} → (e₁ : A ≃ B) → (e₂ : B ≃ C) → ua (e₂ ∘e e₁) ≡ (ua e₁ ∘ ua e₂)
  ua-∘e' : {A B C : Set} → {f1 : A → B} → {f2 : B → C} → {m : A} → (e₁ : Singleton m ≃ Singleton (f1 m)) →
           (e₂ : Singleton (f1 m) ≃ Singleton ((f2 ○ f1) m)) → ua (_∘e'_ {A} {B} {C} {f2} {f1} {m} e₂ e₁) ≡ (ua e₁ ∘ ua e₂)

