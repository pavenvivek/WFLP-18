-- {-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Data.List
open import Function hiding (flip)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Automation.utils.reflectionUtils
open import Automation.utils.pathUtils
open import Automation.lib.generateRec using (getMapConstructorType; generateRec)

module Automation.lib.generateRecHit where

-- -----

getIndexRef2 : (params : Nat) → Nat → Name → TC (List Bool)
getIndexRef2 d ind cn = bindTC (getType cn)
                        (λ x → bindTC (rmPars d x)
                        (λ x' → (getIndexRef' [] ind x')))


retExprRef2 : (indType : Name) → (params : Nat) → (refLs : List Nat) → (cons : Type) → TC Nat
retExprRef2 ind d ref (pi (arg info t1) (abs s t2)) =
    do let ref' = (map (λ z → z + 1) ref)
           ref'' = (ref' ∷L 0)
       t2' ← retExprRef2 ind d ref'' t2
       pure t2'
retExprRef2 ind d ref (def x lsargs) =
    case (primQNameEquality ind x) of λ
     { true →
       do lsargs' ← dropTC d lsargs
          ref' ← dropTC d ref
          lb ← getBoolList ref'
          lb' ← foldl' (λ {lb' (arg i term) →
                           do b' ← (retExprRef' ref' lb' term)
                              pure b' }) lb lsargs'
          ln ← countB lb'
          pure ln
     ; false → pure 0
     }
retExprRef2 ind d ref x = pure 0


getExprRef2 : (indType : Name) → (params : Nat) → (cons : List Name) → TC (List Nat)
getExprRef2 ind d [] = pure []
getExprRef2 ind d (c ∷ cs) =
    do cTy ← getType c
       l ← retExprRef2 ind d [] cTy
       ls ← getExprRef2 ind d cs
       pure (l ∷ ls)

-- -----


getPathClause : (lpoints : Nat) → (lpaths : Nat) → (baseRec : Name) → TC (List Clause)
getPathClause lpoints lpaths baseRec =
  do vars' ← (getClauseVars zero (lpoints + lpaths))
     vars ← (reverseTC vars')
     args ← (generateRef (suc (suc lpoints))) -- +1 for "C" and +1 for constructor
     args' ← (pure (map (λ z → z + lpaths) args))
     argTerms ← (generateRefTerm args')
     pure ((clause (vArg (var "x") ∷ vArg (var "C1") ∷ vars) (def baseRec argTerms)) ∷ [])

{-# TERMINATING #-}
getMapConstructorType' : (Cref : Nat) → (pars : List Nat) → (R : Name) → (mapTy : Bool) → Type → TC Type
getMapConstructorType' Cref pars R mapTy (pi (arg info t1) (abs s t2)) =
  case! checkCdm (def R []) t1 of λ
   { true →
     do let pars' = map (λ z → z + 2) pars -- +1 for Rcons and +1 for Ccons
            pars'' = map (λ z → z + 1) pars
            pars''' = pars' ∷L 1 -- 1 for Rcons and 0 for Ccons -- ((pars' ∷L 1) ∷L 0))
        t2' ← getMapConstructorType' (suc (suc Cref)) pars''' R mapTy t2
        t1' ← getMapConstructorType' Cref pars R false t1
        cdom' ← getMapConstructorType' (suc Cref) pars'' R false t1
        cdom'' ← changeCodomain (suc Cref) cdom'
        pure (pi (arg info t1') (abs s (pi (arg info cdom'') (abs "Ccons" t2'))))
   ; false →
     do let pars' = map (λ z → z + 1) pars
            pars'' = pars' ∷L 0
        t2' ← getMapConstructorType' (suc Cref) pars'' R mapTy t2
        t1' ← getMapConstructorType' Cref pars R false t1
        pure (pi (arg info t1') (abs s t2'))
   }
getMapConstructorType' Cref pars R mapTy (def x lsargs) =
  case (_and_ mapTy (primQNameEquality R x)) of λ
   { true → pure (var Cref [])
   ; false →
     case null lsargs of λ
      { true → pure (def x [])
      ; false →
        do lsargs' ←
             (map' (λ { (arg i term) →
                       do term' ← getMapConstructorType' Cref pars R mapTy term
                          pure (arg i term') })
                   lsargs)
           pure (def x lsargs')
      }
   }
getMapConstructorType' Cref pars R mapTy (var ref lsargs) =
  do pars' ← (reverseTC pars)
     x ← (getListElement ref pars')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ←
             (map' (λ { (arg i term) →
                       do term' ← (getMapConstructorType' Cref pars R mapTy term)
                          pure (arg i term') })
                  lsargs)
           pure (var x lsargs')
      }
getMapConstructorType' Cref pars R mapTy (lam vis (abs s term)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0)
     term' ← (getMapConstructorType' Cref pars'' R mapTy term)
     pure (lam vis (abs s term'))
getMapConstructorType' Cref pars R mapTy (con cn lsargs) =
  case (null lsargs) of λ
   { true → pure (con cn [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                     do term' ← (getMapConstructorType' Cref pars R mapTy term)
                        pure (arg i term') }) lsargs)
        pure (con cn lsargs')
   }
getMapConstructorType' Cref pars R mapTy (meta x lsargs) =
  case (null lsargs) of λ
   { true → pure (meta x [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                     do term' ← (getMapConstructorType' Cref pars R mapTy term)
                        pure (arg i term') }) lsargs)
        pure (meta x lsargs')
   }
getMapConstructorType' Cref pars R mapTy (pat-lam cs lsargs) =
  case (null lsargs) of λ
   { true → pure (pat-lam cs [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                     do term' ← (getMapConstructorType' Cref pars R mapTy term)
                        pure (arg i term') }) lsargs)
        pure (pat-lam cs lsargs') }
getMapConstructorType' Cref pars R mapTy x = pure x

getMapConsTypeList' : Name → (params : Nat) → (Cref : Nat) → (paths : Type) → (pars : List Nat) → (indexList : List Nat) → (lcons : List Name) → TC Type
getMapConsTypeList' R d Cref paths pars i [] = pure paths
getMapConsTypeList' R d Cref paths pars (i ∷ is) (x ∷ xs) =
  do ty ← (getType x)
     x' ← (rmPars d ty)
     pars' ← (pure (map (λ z → z + 1) pars))
     lb ← (getIndexRef2 d i x)
     case! (isMemberBool true lb) of λ
      { true →
        do t ← (getMapConstructorType' Cref pars R true x')
           xt ← (getMapConsTypeList' R d (suc Cref) paths pars' is xs)
           pure (pi (vArg t) (abs "_" xt))
      ; false →
        do x'' ← (rmIndex i x')
           t ← (getMapConstructorType' Cref pars R true x'')
           xt ← (getMapConsTypeList' R d (suc Cref) paths pars' is xs)
           pure (pi (vArg t) (abs "_" xt))
      }
getMapConsTypeList' R d Cref paths pars x y = pure unknown -- Invalid case


{-# TERMINATING #-}
getMapConstructorPathType' : (baseRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
  (args : List Nat) → (indTyp : Name) → (recurse : Bool) → Type → TC Type
getMapConstructorPathType' baseRec pars cons index args indTyp rcu (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         args' = (map (λ z → z + 1) args)
         args'' = (args' ∷L 0)
     t1' ← (getMapConstructorPathType' baseRec pars cons index args indTyp rcu t1)
     t2' ← (getMapConstructorPathType' baseRec pars' cons' index' args'' indTyp rcu t2)
     pure (pi (arg info t1') (abs s t2'))
getMapConstructorPathType' baseRec pars cons index args indTyp rcu (def x lsargs) =
  case (primQNameEquality x (quote _≡_)) of λ
   { true →
     do lsargsvis ← (removeHidden lsargs)
        lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorPathType' baseRec pars cons index args indTyp rcu term)
                                   case term' of λ
                                    { (var x' args') →
                                        do argCons ← (generateRefTerm cons)
                                           args'' ← (pure ((vArg (var x' args') ∷ []) ++L argCons))
                                           pure (arg i (def baseRec args''))
                                      ; term'' → pure (arg i term'')
                                    }
                            }) lsargsvis)
        pure (def (quote _≡_) lsargs')
   ; false →
     do x' ← (getType x)
        case! (getBaseType x') of λ
         { (def xty argL) →
           case (_and_ rcu (primQNameEquality xty indTyp)) of λ
            { true →
              do lsargs' ← (map' (λ { (arg i term) →
                                         do term' ← (getMapConstructorPathType' baseRec pars cons index args indTyp false term)
                                            pure (arg i term') }) lsargs)
                 argCons ← (generateRefTerm cons)
                 args' ← (pure ((vArg (def x lsargs') ∷ []) ++L argCons))
                 pure (def baseRec args')
            ; false →
              do lsargs' ← (map' (λ { (arg i term) →
                                         do term' ← (getMapConstructorPathType' baseRec pars cons index args indTyp rcu term)
                                            pure (arg i term') }) lsargs)
                 pure (def x lsargs')
            }
         ; type → pure (def x lsargs)
         }
   }
getMapConstructorPathType' baseRec pars cons index args indTyp rcu (var ref lsargs) =
  do let pind = (pars ++L index)
         refL = (pind ++L args)
     refL' ← (reverseTC refL)
     x ← (getListElement ref refL')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ← (map' (λ { (arg i term) →
                                   do term' ← (getMapConstructorPathType' baseRec pars cons index args indTyp rcu term)
                                      pure (arg i term') }) lsargs)
           pure (var x lsargs')
      }
getMapConstructorPathType' baseRec pars cons index args indTyp rcu x = pure x

getMapConstructorPathType : (baseRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorPathType baseRec pars cons index indTyp 0 x = getMapConstructorPathType' baseRec pars cons index [] indTyp true x
getMapConstructorPathType baseRec pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         index'' = (index' ∷L 0)
     ty ← (getMapConstructorPathType baseRec pars' cons' index'' indTyp x t2)
     pure (pi (arg info t1) (abs s ty))
getMapConstructorPathType baseRec pars cons index indTyp x y = pure unknown                                                                            

getPaths : (baseRec : Name) → (CRefBase : Nat) → (pars : List Nat) → (cons : List Nat) → (baseTyp : Name) → (indType : Name) → (params : Nat) → (paths : List Name) → TC Type
getPaths baseRec CRefBase pars cons baseTyp indTyp d [] = pure (var CRefBase [])
getPaths baseRec CRefBase pars cons baseTyp indTyp d (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getPaths baseRec (suc CRefBase) pars' cons' baseTyp indTyp d xs)
     ty ← (getType x)
     ty' ← (rmPars d ty)
     ty2 ← (getType indTyp)
     index ← (getIndexValue zero d ty2)
     x' ← (getMapConstructorPathType baseRec pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getRtypePath : (baseTyp : Name) → (indTyp : Name) → (baseRec : Name) → (param : Nat) → (points : List Name) → (pathList : List Name) → (ref : Nat) → (RTy : Type) → TC Type
getRtypePath baseTyp indTyp baseRec d points pathList ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypePath baseTyp indTyp baseRec d points pathList (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypePath baseTyp indTyp baseRec d points pathList ref (agda-sort Level) =
  do lcons ← (getLength points)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     pars ← (takeTC d refls)
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     refls' ← (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
     parsPath ← (takeTC d refls')
     exp ← (getExprRef2 indTyp d points)
     paths ← (getPaths baseRec lcons parsPath consPath baseTyp indTyp d pathList)
     funType ← (getMapConsTypeList' indTyp d zero paths pars exp points)
     Rty' ← (getType indTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg (agda-sort (lit 0))) (abs "C3" funType)))) 
getRtypePath baseTyp indType baseRec d points pathList ref x = pure unknown


generateRecHit : Arg Name → (indType : Name) → (baseRec : Name) → (param : Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateRecHit (arg i f) indType baseRec d points paths =
  do lpoints ← getLength points
     lpaths ← getLength paths
     clauses ← getPathClause lpoints lpaths baseRec
     RTy ← getType indType
     funTypePath ← getRtypePath indType indType baseRec d points paths zero RTy
     declareDef (arg i f) funTypePath
     defineFun f clauses


