-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
{-# OPTIONS --verbose tc.sample.debug:20 #-}
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Primitive
open import Data.List
-- open import Data.Vec
open import Data.Fin
open import Automation.utils.reflectionUtils
open import Automation.lib.generateRec
open import Automation.lib.generateBetaRec


module Automation.test.test_Recursion where

macro
  thm-prv : (C : Name) → Term → TC ⊤
  thm-prv C hole = bindTC (getType C)
                          (λ type → unify hole type)

{--
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
--}

unquoteDecl recNat = generateRec (vArg recNat)
                                 (quote Nat)

double : Nat → Nat
double = (λ x → recNat x Nat 0 (λ n r → suc (suc r)))

add : Nat → Nat → Nat
add = (λ x → recNat x (Nat → Nat) (λ n → n) (λ m r → λ n → suc (r n)))

recℕ : Nat → (C : Set) → C → (Nat → C → C) → C
recℕ 0 C c f = c
recℕ (suc n) C c f = f n (recℕ n C c f)

thm1 : thm-prv recℕ ≡ thm-prv recNat
thm1 = refl

-- postulate
  -- recN : Nat → (C : Set) → C → (Nat → C → C) → C

unquoteDecl recN βNzero βNsuc = generateβRec (vArg recN)
                                     ((vArg βNzero) ∷ (vArg βNsuc) ∷ [])
                                     (quote Nat) 0 ((quote Nat.zero) ∷ (quote Nat.suc) ∷ [])

{-# REWRITE βNzero #-}
{-# REWRITE βNsuc #-}



-- --------

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)


unquoteDecl recVec = generateRec (vArg recVec)
                                 (quote Vec) 

recVec' : {A : Set} → {n : Nat} → Vec A n → (C : Set) → C → 
         ({m : Nat} → (x : A) → (xs : Vec A m) → C → C) → C
recVec' [] C cnil ccons = cnil
recVec' (x ∷ xs) C cnil ccons = ccons x xs (recVec' xs C cnil ccons)
 
thm2 : thm-prv recVec
thm2 = recVec'

unquoteDecl recV βV[] βV_∷_ = generateβRec (vArg recV)
                                     ((vArg βV[]) ∷ (vArg βV_∷_) ∷ [])
                                     (quote Vec) 1 ((quote Vec.[]) ∷ (quote Vec._∷_) ∷ [])

{-# REWRITE βV[] #-}
{-# REWRITE βV_∷_ #-}

-- --------

data List1 (A : Set) : Set where
  []  : List1 A
  _∷_ : (x : A) (xs : List1 A) → List1 A


unquoteDecl recList = generateRec (vArg recList)
                                  (quote List1)

{-
recList' : ∀{a} {A : Set a} → List A → (C : Set) → C → 
         ((x : A) → (xs : List A) → C → C) → C
recList' [] C cnil ccons = cnil
recList' (x ∷ xs) C cnil ccons = ccons x xs (recList' xs C cnil ccons)

thm3 : thm-prv recList
thm3 = recList'
-}

unquoteDecl recL βL[] βL_∷_ = generateβRec (vArg recL)
                                     ((vArg βL[]) ∷ (vArg βL_∷_) ∷ [])
                                     (quote List1) 1 ((quote List1.[]) ∷ (quote List1._∷_) ∷ [])

{-# REWRITE βL[] #-}
{-# REWRITE βL_∷_ #-}

-- --------

{--
data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n) 
  suc : ∀ {n} → Fin n → Fin (suc n)
--}

unquoteDecl recFin = generateRec (vArg recFin)
                                 (quote Fin)

recFin' : {n : Nat} → (xs : Fin n) → (C : Set) → (cnil : C) → -- (cnil : {n : Nat} → C) →
         (csuc : {n : Nat} → (x : Fin n) → C → C) → C
recFin' (Fin.zero) C cnil csuc = cnil
recFin' (Fin.suc x) C cnil csuc = csuc x (recFin' x C cnil csuc)

thm4 : thm-prv recFin' ≡ thm-prv recFin
thm4 = refl

unquoteDecl recF βFzero βFsuc = generateβRec (vArg recF)
                                    ((vArg βFzero) ∷ (vArg βFsuc) ∷ [])
                                    (quote Fin) 0 ((quote Fin.zero) ∷ (quote Fin.suc) ∷ [])

{-# REWRITE βFzero #-}
{-# REWRITE βFsuc #-}

postulate
  t0 : (C : Set) (z : C) (f : {n : Nat} (i : Fin n) (Ccons : C) → C)
       {n : Nat} → recFin (zero {n}) C z f ↦ z
  t1 : (C : Set) (z : C) (f : {n : Nat} (i : Fin n) (Ccons : C) → C)
     {n : Nat} {i : Fin n} → recFin (suc i) C z f ↦ f i (recFin i C z f)

-- --------

{--
data Bool : Set where
  false true : Bool
--}

unquoteDecl recBool = generateRec (vArg recBool)
                                  (quote Bool)
                                  
recBool' : Bool → (C : Set) → C → C → C
recBool' false C el th = el
recBool' true C el th = th

thm5 : thm-prv recBool' ≡ thm-prv recBool
thm5 = refl

unquoteDecl recB βtrue βfalse = generateβRec (vArg recB)
                                     ((vArg βtrue) ∷ (vArg βfalse) ∷ [])
                                     (quote Bool) 0 ((quote false) ∷ (quote true) ∷ [])

{-# REWRITE βtrue #-}
{-# REWRITE βfalse #-}

-- --------

data W (A : Set) (B : A → Set) : Set where
   sup : (a : A) → (B a → W A B) → W A B

{-
unquoteDecl recW = generateRec
                   (vArg recW)
                   (quote W)
-}

recW' : {A : Set} {B : A → Set} → W A B → (C : Set) → ((x : A) → (B x → W A B) → (z : B x → C ) → C) → C
recW' {A} {B} (sup a b) C csup = csup a b (λ v → recW' {A} {B} (b v) C csup)

-- thm6 : thm-prv recW ≡ thm-prv recW'
-- thm6 = refl

unquoteDecl recW βWsup = generateβRec (vArg recW)
                                   ((vArg βWsup) ∷ [])
                                   (quote W) 2 ((quote sup) ∷ [])


{-# REWRITE βWsup #-}

