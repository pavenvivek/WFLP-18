-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
{-# OPTIONS --verbose tc.sample.debug:20 #-}
-- {-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-auto-inline #-}
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Reflection
open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Data.List
open import Data.Empty

open import Automation.lib.generateRec
open import Automation.lib.generateInd
open import Automation.lib.generateHit
open import Automation.lib.generateRecHit
open import Automation.lib.generateIndHit
open import Automation.lib.generateBetaRecHit
open import Automation.lib.generateBetaRecHitPath using (generateβRecHitPath)
open import Automation.lib.generateBetaRec
open import Automation.lib.generateBetaIndHit
open import Automation.lib.generateBetaIndHitPath using (generateβIndHitPath)
open import Automation.lib.generateBetaInd
open import Automation.utils.reflectionUtils
open import Automation.utils.pathUtils

module Automation.test.test_HIndTypes where

macro
  thm-prv : (C : Name) → Term → TC ⊤
  thm-prv C hole = bindTC (getType C)
                          (λ type → unify hole type)

module Circle1 where

  postulate
    S₁ : Set
    base : S₁
    loop : base ≡ base

  S₁points : List Name
  S₁points = ((quote base) ∷ [])

  S₁paths : List Name
  S₁paths = ((quote loop) ∷ [])

{--
  recS : S → (C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → C
  recS base* C cbase cloop = cbase
--}

  unquoteDecl recS* βbase* = generateβRec (vArg recS*)
                                     ((vArg βbase*) ∷ [])
                                     (quote S₁) 0 S₁points

  {-# REWRITE βbase* #-}

  unquoteDecl recS = generateRecHit (vArg recS)
                                    (quote S₁)
                                    (quote recS*) 0 S₁points S₁paths

{-
  postulate
    βrecS : (C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → 
      ap (λ x → recS x C cbase cloop) loop ≡ cloop
-}

  unquoteDecl βloop = generateβRecHitPath (quote recS)
                                     ((vArg βloop) ∷ [])
                                     (quote S₁)
                                     (quote recS*) 0 S₁points S₁paths


  thm2 : thm-prv βloop ≡ ((C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → ap (λ x → recS x C cbase cloop) loop ≡ cloop)
  thm2 = refl


{--
  indS : (circle : S) → (C : S → Set) → 
    (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → C circle
  indS base* C cbase cloop = cbase
--}

  unquoteDecl indS* βibase* = generateβInd (vArg indS*)
                                        ((vArg βibase*) ∷ [])
                                        (quote S₁) 0 S₁points

  {-# REWRITE βibase* #-}


  unquoteDecl indS = generateIndHit (vArg indS)
                                    (quote S₁)
                                    (quote indS*) 0 S₁points S₁paths

{-
  postulate
    βindS : (C : S₁ → Set) → 
      (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
      apd (λ x → indS x C cbase cloop) loop ≡ cloop
-}

  unquoteDecl βiloop = generateβIndHitPath (quote indS)
                                     ((vArg βiloop) ∷ [])
                                     (quote S₁)
                                     (quote indS*) 0 S₁points S₁paths

  thm4 : thm-prv βiloop ≡ ((C : S₁ → Set) → (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → apd (λ x → indS x C cbase cloop) loop ≡ cloop)
  thm4 = refl

-- ---------


module Circle2 where

  postulate
    S₂ : Set
    south : S₂
    north : S₂
    east : south ≡ north
    west : south ≡ north

  S₂points : List Name
  S₂points = ((quote south) ∷ (quote north) ∷ [])

  S₂paths : List Name
  S₂paths = ((quote east) ∷ (quote west) ∷ [])
  
  
{--
  recS¹' : S¹' → (C : Set) → 
    (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → C
  recS¹' south* csouth cnorth ceast cwest = csouth
  recS¹' north* csouth cnorth ceast cwest = cnorth
--}

  unquoteDecl recS₂* βsouth* βnorth* = generateβRec (vArg recS₂*)
                                     ((vArg βsouth*) ∷ (vArg βnorth*) ∷ [])
                                     (quote S₂) 0 S₂points

  {-# REWRITE βsouth* #-}
  {-# REWRITE βnorth* #-}

  unquoteDecl recS₂ = generateRecHit (vArg recS₂)
                                     (quote S₂)
                                     (quote recS₂*) 0 S₂points S₂paths


{-
  postulate
    βreceastS¹ : (C : Set) → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (λ x → recS₂ x C csouth cnorth ceast cwest) east ≡ ceast
    βrecwestS¹ : (C : Set) → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (λ x → recS₂ x C csouth cnorth ceast cwest) west ≡ cwest
-}

  unquoteDecl βreceast βrecwest = generateβRecHitPath (quote recS₂)
                                     ((vArg βreceast) ∷ (vArg βrecwest) ∷ [])
                                     (quote S₂)
                                     (quote recS₂*) 0 S₂points S₂paths

  thm6 : thm-prv βreceast ≡ ((C : Set) → (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → ap (λ x → recS₂ x C csouth cnorth ceast cwest) east ≡ ceast)
  thm6 = refl

  thm7 : thm-prv βrecwest ≡ ((C : Set) → (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → ap (λ x → recS₂ x C csouth cnorth ceast cwest) west ≡ cwest)
  thm7 = refl

{--
  indS¹' : (circle : S¹') → (C : S¹' → Set) → 
    (csouth : C south) → (cnorth : C north) → 
    (ceast : transport C east csouth ≡ cnorth) → 
    (cwest : transport C west csouth ≡ cnorth) → C circle
  indS¹' south* C csouth cnorth ceast cwest = csouth
  indS¹' north* C csouth cnorth ceast cwest = cnorth
--}

  unquoteDecl indS₂* βisouth* βinorth* = generateβInd (vArg indS₂*)
                                     ((vArg βisouth*) ∷ (vArg βinorth*) ∷ [])
                                     (quote S₂) 0 S₂points

  {-# REWRITE βisouth* #-}
  {-# REWRITE βinorth* #-}

  unquoteDecl indS₂ = generateIndHit (vArg indS₂)
                                     (quote S₂)
                                     (quote indS₂*) 0 S₂points S₂paths

{-
  postulate
    βindeastS¹' : (C : S₂ → Set) → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (λ x → indS₂ x C csouth cnorth ceast cwest) east ≡ ceast
    βindwestS¹' : (C : S₂ → Set) → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (λ x → indS₂ x C csouth cnorth ceast cwest) west ≡ cwest
-}

  unquoteDecl βindeast βindwest = generateβIndHitPath (quote indS₂)
                                     ((vArg βindeast) ∷ (vArg βindwest) ∷ [])
                                     (quote S₂)
                                     (quote indS₂*) 0 S₂points S₂paths

  thm8 : thm-prv indS₂ ≡ ((circle : S₂) → (C : S₂ → Set) → (csouth : C south) → (cnorth : C north) →  (ceast : transport C east csouth ≡ cnorth) → 
                           (cwest : transport C west csouth ≡ cnorth) → C circle)
  thm8 = refl

  thm9 : thm-prv βindeast ≡ ((C : S₂ → Set) → (csouth : C south) → (cnorth : C north) → (ceast : transport C east csouth ≡ cnorth) → (cwest : transport C west csouth ≡ cnorth) → 
                                apd (λ x → indS₂ x C csouth cnorth ceast cwest) east ≡ ceast)
  thm9 = refl

  thm10 : thm-prv βindwest ≡ ((C : S₂ → Set) → (csouth : C south) → (cnorth : C north) → (ceast : transport C east csouth ≡ cnorth) → (cwest : transport C west csouth ≡ cnorth) → 
                                 apd (λ x → indS₂ x C csouth cnorth ceast cwest) west ≡ cwest)
  thm10 = refl

-- ---------

module Pushout where

  postulate
    Pushout : {A B C : Set} → (f : C → A) → (g : C → B) → Set
    inl : {A B C : Set} → {f : C → A} → {g : C → B} → A → Pushout f g
    inr : {A B C : Set} → {f : C → A} → {g : C → B} → B → Pushout f g
    glue : {A B C : Set} → {f : C → A} → {g : C → B} → (c : C) → (inl {A} {B} {C} {f} {g} (f c)) ≡ (inr (g c))

  Pushoutpoints : List Name
  Pushoutpoints = ((quote inl) ∷ (quote inr) ∷ [])

  Pushoutpaths : List Name
  Pushoutpaths = ((quote glue) ∷ [])

{--
  recPush : {A B C : Set} → {f : C → A} → {g : C → B} →
            Pushout f g → (D : Set) → (f1 : A → D) → (f2 : B → D) →
            (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) → D
  recPush (inl* a) D f1 f2 dglue = (f1 a)
  recPush (inr* b) D f1 f2 dglue = (f2 b)
--}

  unquoteDecl recP* βinl* βinr* = generateβRec (vArg recP*)
                                     ((vArg βinl*) ∷ (vArg βinr*) ∷ [])
                                     (quote Pushout) 5 Pushoutpoints

  {-# REWRITE βinl* #-}
  {-# REWRITE βinr* #-}

  unquoteDecl recP = generateRecHit (vArg recP)
                                    (quote Pushout)
                                    (quote recP*) 5 Pushoutpoints Pushoutpaths

  thm11 : thm-prv recP ≡ ({A B C : Set} → {f : C → A} → {g : C → B} → Pushout f g → (D : Set) → (f1 : A → D) → (f2 : B → D) → (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) → D)
  thm11 = refl

{-
  postulate
    βrecPush' : {A B C : Set} → {f : C → A} → {g : C → B} →
               (D : Set) → (f1 : A → D) → (f2 : B → D) →
               (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) →
               {c : C} → ap (λ x → recP x D f1 f2 dglue) (glue {A} {B} {C} {f} {g} c) ≡ (dglue c)
-}

  unquoteDecl βglue = generateβRecHitPath (quote recP)
                                     ((vArg βglue) ∷ [])
                                     (quote Pushout)
                                     (quote recP*) 5 Pushoutpoints Pushoutpaths

  thm12 : thm-prv βglue ≡ ({A B C : Set} → {f : C → A} → {g : C → B} → (D : Set) → (f1 : A → D) → (f2 : B → D) → (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) →
                               {c : C} → ap (λ x → recP x D f1 f2 dglue) (glue {A} {B} {C} {f} {g} c) ≡ (dglue c))
  thm12 = refl

  unquoteDecl indP* iβinl* iβinr* = generateβInd (vArg indP*)
                                     ((vArg iβinl*) ∷ (vArg iβinr*) ∷ [])
                                     (quote Pushout) 5 Pushoutpoints

  {-# REWRITE iβinl* #-}
  {-# REWRITE iβinr* #-}

{--
  indPush : {A B C : Set} → {f : C → A} → {g : C → B} →
            (p : Pushout f g) → (D : Pushout f g → Set) → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
            (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) → D p
  indPush (inl* a) D f1 f2 dglue = (f1 a)
  indPush (inr* b) D f1 f2 dglue = (f2 b)
--}

  unquoteDecl indP = generateIndHit (vArg indP)
                                    (quote Pushout)
                                    (quote indP*) 5 Pushoutpoints Pushoutpaths

  thm13 : thm-prv indP ≡ ({A B C : Set} → {f : C → A} → {g : C → B} → (p : Pushout f g) → (D : Pushout f g → Set) → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
                              (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) → D p)
  thm13 = refl

{-
  postulate
    βindPush : {A B C : Set} → {f : C → A} → {g : C → B} →
               (D : Pushout f g → Set) → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
               (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) →
               {c : C} → apd (λ x → indP x D f1 f2 dglue) (glue c) ≡ (dglue c)
-}

  unquoteDecl iβglue = generateβIndHitPath (quote indP)
                                     ((vArg iβglue) ∷ [])
                                     (quote Pushout)
                                     (quote indP*) 5 Pushoutpoints Pushoutpaths

  thm14 : thm-prv iβglue ≡ ({A B C : Set} → {f : C → A} → {g : C → B} → (D : Pushout f g → Set) → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
                               (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) → {c : C} → apd (λ x → indP x D f1 f2 dglue) (glue c) ≡ (dglue c))
  thm14 = refl

-- ---------

module Susp where

  postulate
    Σₛ : (A : Set) → Set
    N : {A : Set} → Σₛ A
    S : {A : Set} → Σₛ A
    merid : {A : Set} → (a : A) → (N {A} ≡ S {A})

  Σₛpoints : List Name
  Σₛpoints = ((quote N) ∷ (quote S) ∷ [])

  Σₛpaths : List Name
  Σₛpaths = ((quote merid) ∷ [])

{--
  recₛ : {A : Set} → Σₛ A → (B : Set) → (n s : B) → (m : A → (n ≡ s)) → B
  recₛ N* B n s m = n
  recₛ S* B n s m = s
--}


  unquoteDecl recΣ* βΣn* βΣs* = generateβRec (vArg recΣ*)
                                     ((vArg βΣn*) ∷ (vArg βΣs*) ∷ [])
                                     (quote Σₛ) 1 Σₛpoints

  {-# REWRITE βΣn* #-}
  {-# REWRITE βΣs* #-}

  unquoteDecl recΣ = generateRecHit (vArg recΣ)
                                    (quote Σₛ)
                                    (quote recΣ*) 1 Σₛpoints Σₛpaths

  thm15 : thm-prv recΣ ≡ ({A : Set} → Σₛ A → (B : Set) → (n s : B) → (m : A → (n ≡ s)) → B)
  thm15 = refl

{-
  postulate
    βrecΣ : {A : Set} → (B : Set) → (n s : B) → (m : A → (n ≡ s)) →
            {a : A} → ap (λ x → recΣ x B n s m) (merid a) ≡ m a
-}

  unquoteDecl βmerid = generateβRecHitPath (quote recΣ)
                                     ((vArg βmerid) ∷ [])
                                     (quote Σₛ)
                                     (quote recΣ*) 1 Σₛpoints Σₛpaths

  thm16 : thm-prv βmerid ≡ ({A : Set} → (B : Set) → (n s : B) → (m : A → (n ≡ s)) → {a : A} → ap (λ x → recΣ x B n s m) (merid a) ≡ m a)
  thm16 = refl

{--
  indₛ : {A : Set} → (x : Σₛ A) → (B : Σₛ A → Set) → (n : B (N {A})) → (s : B (S {A})) → (m : (a : A) → (transport B (merid a) n ≡ s)) → B x
  indₛ N* B n s m = n
  indₛ S* B n s m = s
--}

  unquoteDecl indΣ* iβΣn* iβΣs* = generateβInd (vArg indΣ*)
                                     ((vArg iβΣn*) ∷ (vArg iβΣs*) ∷ [])
                                     (quote Σₛ) 1 Σₛpoints

  {-# REWRITE iβΣn* #-}
  {-# REWRITE iβΣs* #-}

  unquoteDecl indΣ = generateIndHit (vArg indΣ)
                                    (quote Σₛ)
                                    (quote indΣ*) 1 Σₛpoints Σₛpaths

  thm17 : thm-prv indΣ ≡ ({A : Set} → (x : Σₛ A) → (B : Σₛ A → Set) → (n : B (N {A})) → (s : B (S {A})) → (m : (a : A) → (transport B (merid a) n ≡ s)) → B x)
  thm17 = refl

{-
  postulate
    βindₛ : {A : Set} → (B : Σₛ A → Set) → (n : B N) → (s : B S) → (m : (a : A) → (transport B (merid a) n ≡ s)) →
            {a : A} → apd (λ x → indΣ x B n s m) (merid a) ≡ m a  
-}

  unquoteDecl iβmerid = generateβIndHitPath (quote indΣ)
                                     ((vArg iβmerid) ∷ [])
                                     (quote Σₛ)
                                     (quote indΣ*) 1 Σₛpoints Σₛpaths

  thm18 : thm-prv iβmerid ≡ ({A : Set} → (B : Σₛ A → Set) → (n : B N) → (s : B S) → (m : (a : A) → (transport B (merid a) n ≡ s)) →
                            {a : A} → apd (λ x → indΣ x B n s m) (merid a) ≡ m a)
  thm18 = refl


{-
open Susp public

absurd' : {A : Set} → (a : A) → (N {A} ≡ S {A}) → ⊥
absurd' {A} a ()
-}


module Interval where

  postulate
    𝕀 : Set
    start : 𝕀
    end : 𝕀
    seg : start ≡ end

  𝕀points : List Name
  𝕀points = ((quote start) ∷ (quote end) ∷ [])

  𝕀paths : List Name
  𝕀paths = ((quote seg) ∷ [])

  unquoteDecl rec𝕀* βstart* βend* = generateβRec (vArg rec𝕀*)
                                     ((vArg βstart*) ∷ (vArg βend*) ∷ [])
                                     (quote 𝕀) 0 𝕀points

  {-# REWRITE βstart* #-}
  {-# REWRITE βend* #-}

  unquoteDecl rec𝕀 = generateRecHit (vArg rec𝕀)
                                    (quote 𝕀)
                                    (quote rec𝕀*) 0 𝕀points 𝕀paths

  thm15 : thm-prv rec𝕀 ≡ (𝕀 → (B : Set) → (st end : B) → (seg : st ≡ end) → B)
  thm15 = refl

  unquoteDecl βseg = generateβRecHitPath (quote rec𝕀)
                                     ((vArg βseg) ∷ [])
                                     (quote 𝕀)
                                     (quote rec𝕀*) 0 𝕀points 𝕀paths

  thm16 : thm-prv βseg ≡ ((B : Set) → (s e : B) → (sg : s ≡ e) → ap (λ x → rec𝕀 x B s e sg) seg ≡ sg)
  thm16 = refl

  unquoteDecl ind𝕀* iβstart* iβend* = generateβInd (vArg ind𝕀*)
                                     ((vArg iβend*) ∷ (vArg iβstart*) ∷ [])
                                     (quote 𝕀) 0 𝕀points

  {-# REWRITE iβstart* #-}
  {-# REWRITE iβend* #-}

  unquoteDecl ind𝕀 = generateIndHit (vArg ind𝕀)
                                    (quote 𝕀)
                                    (quote ind𝕀*) 0 𝕀points 𝕀paths

  thm17 : thm-prv ind𝕀 ≡ ((x : 𝕀) → (B : 𝕀 → Set) → (s : B start) → (e : B end) → (sg : (transport B seg s ≡ e)) → B x)
  thm17 = refl

  unquoteDecl iβseg = generateβIndHitPath (quote ind𝕀)
                                     ((vArg iβseg) ∷ [])
                                     (quote 𝕀)
                                     (quote ind𝕀*) 0 𝕀points 𝕀paths

  thm18 : thm-prv iβseg ≡ ((B : 𝕀 → Set) → (s : B start) → (e : B end) → (sg : transport B seg s ≡ e) →
                            apd (λ x → ind𝕀 x B s e sg) seg ≡ sg)
  thm18 = refl

module IntervalOops where
  open Interval
  -- This is an issue with the technique as implemented. Pattern
  -- matching can still be used to prove disjointness of constructors.
  oops : start ≡ end → ⊥
  oops ()

  double-oops : ⊥
  double-oops = oops seg

