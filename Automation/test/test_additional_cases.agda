-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
-- {-# OPTIONS --verbose tc.sample.debug:12 #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Data.List
open import Automation.utils.reflectionUtils
open import Automation.lib.generateRec
open import Automation.lib.generateInd

module Automation.test.test_additional_cases where

macro
  thm-prv : (C : Name) → Term → TC ⊤
  thm-prv C hole = bindTC (getType C)
                          (λ type → unify hole type)

postulate
  A : Set
  B : Set
  C : Set
  D : Set

data W : Set where
  g : (A → W) → B → W → W

unquoteDecl recW = generateRec (vArg recW)
                               (quote W)


recursionW : W → (P : Set) → (d : (A → W) → (A → P) → B → W → P → P) → P
recursionW (g α β ω) P d = d α (λ a → recursionW (α a) P d) β ω (recursionW ω P d) 

thm1 : thm-prv recW ≡ thm-prv recursionW
thm1 = refl

unquoteDecl indW = generateInd (vArg indW)
                               (quote W)

inductionW : (w : W) → (P : W → Set) → (d : (α : A → W) → ((a : A) → P (α a)) → (β : B) → (ω : W) → P ω → P (g α β ω)) → P w
inductionW (g α β ω) P d = d α (λ a → inductionW (α a) P d) β ω (inductionW ω P d) 

thm2 : thm-prv indW ≡ thm-prv inductionW
thm2 = refl

-- --------

data W' : Set where
  g : (A → W') → (B → C → W') → D → W' → W'

unquoteDecl recW' = generateRec (vArg recW')
                                (quote W')

recursionW' : W' → (P : Set) → (d : (A → W') → (A → P) → (B → C → W') → (B → C → P) → D → W' → P → P) → P
recursionW' (g α β δ ω) P d = d α (λ a → recursionW' (α a) P d) β (λ b c → recursionW' (β b c) P d) δ ω (recursionW' ω P d) 

thm3 : thm-prv recW' ≡ thm-prv recursionW'
thm3 = refl

unquoteDecl indW' = generateInd (vArg indW')
                                (quote W')

inductionW' : (w : W') → (P : W' → Set) → (d : (α : A → W') → ((a : A) → P (α a)) → (β : B → C → W') →
              ((b : B) → (c : C) → P (β b c)) → (δ : D) → (ω : W') → P ω → P (g α β δ ω)) → P w
inductionW' (g α β δ ω) P d = d α (λ a → inductionW' (α a) P d) β (λ b c → inductionW' (β b c) P d) δ ω (inductionW' ω P d) 

thm4 : thm-prv indW' ≡ thm-prv inductionW'
thm4 = refl
