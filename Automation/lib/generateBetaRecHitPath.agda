{-# OPTIONS --verbose tc.sample.debug:20 #-}

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

module Automation.lib.generateBetaRecHitPath where

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

{-# TERMINATING #-}
βrecMapPath' : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
  (args : List Nat) → (argInfo : List ArgInfo) → (indTyp : Name) → Type → TC Type
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         args' = (map (λ z → z + 1) args)
         args'' = (args' ∷L 0)
         argInfo' = (argInf ∷L info)
     t1' ← (βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp t1)
     t2' ← (βrecMapPath' Rpath (suc RpathRef) indRec pars' cons' index' args'' argInfo' indTyp t2)
     pure (pi (hArg t1') (abs s t2'))
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (def x lsargs) =
  case (primQNameEquality x (quote _≡_)) of λ
   { true →
     do let cons' = (map (λ z → z + 1) cons) -- +1 for lam "x"
            index' = (map (λ z → z + 1) index) -- +1 for lam "x"
        argCons ← (generateRefTerm cons')
        argPars ← (generateRefTermHid pars)
        argInds ← (generateRefTermHid index)
        argInds' ← (generateRefTermHid index')
        argInfo' ← (getHidArgs' argInf)
        argArgs ← (generateRefTerm' argInfo' args)
        args' ← (pure ((argPars ++L argInds) ++L argArgs))
        argIndRec ← (pure (lam visible (abs "x" (def indRec (vArg (var 0 []) ∷ argCons)))))
        pathTyp ← (pure (def Rpath args'))
        CpathTyp ← (pure (var RpathRef argArgs))
        pure (def (quote _≡_) (vArg (def (quote ap) (vArg argIndRec ∷ vArg pathTyp ∷ [])) ∷ vArg CpathTyp ∷ []))
   ; false → pure unknown
   }
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (var ref lsargs) =
  do let pind = (pars ++L index)
         refL = (pind ++L args)
     refL' ← (reverseTC refL)
     x ← (getListElement ref refL')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ← (map' (λ { (arg i term) →
                                   do term' ← (βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp term)
                                      pure (arg i term') }) lsargs)
           pure (var x lsargs')
      }
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp x = pure x

βrecMapPath : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
βrecMapPath Rpath RpathRef indRec pars cons index indTyp 0 x = βrecMapPath' Rpath RpathRef indRec pars cons index [] [] indTyp x
βrecMapPath Rpath RpathRef indRec pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         index'' = (index' ∷L 0)
     ty ← (βrecMapPath Rpath (suc RpathRef) indRec pars' cons' index'' indTyp x t2)
     pure (pi (hArg t1) (abs s ty))
βrecMapPath Rpath RpathRef indRec pars cons index indTyp x y = pure unknown

getβrecPaths : (baseRec : Name) → (params : Nat) → (mapPath : Type) → (pars : List Nat) → (cons : List Nat) → (indType : Name) → (paths : List Name) → TC Type
getβrecPaths baseRec d mapPath pars cons indTyp [] = pure mapPath
getβrecPaths baseRec d mapPath pars cons indTyp (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getβrecPaths baseRec d mapPath pars' cons' indTyp xs)
     ty ← (getType x)
     ty' ← (rmPars d ty)
     t ← (getType indTyp)
     index ← (getIndexValue zero d t)
     x' ← (getMapConstructorPathType baseRec pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getβrecRtypePath : (Rpoint : Name) → (indTyp : Name) → (pntInd : Nat) → (elim : Name) → (baseElim : Name) → 
  (indexList : List Nat) → (points : List Name) → (paths : List Name) → (param : Nat) → (pars : Nat) → (ref : Nat) → (RTy : Type) → TC Type
getβrecRtypePath Rpnt indTyp pntInd elim baseElim indLs points paths d1 0 ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getβrecRtypePath Rpnt indTyp pntInd elim baseElim indLs points paths d1 0 ref t2)
     pure t2'
getβrecRtypePath Rpnt indTyp pntInd elim baseElim indLs points paths d1 (suc d) ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getβrecRtypePath Rpnt indTyp pntInd elim baseElim indLs points paths d1 d (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getβrecRtypePath Rpnt indTyp pntInd elim baseElim indLs points paths d1 d ref (agda-sort Level) =
  do lcons ← (getLength points)
     refls ← (generateRef (suc ref)) -- +1 for "C"
     pars ← (takeTC d1 refls)
     consPnt ← (generateRef (suc lcons)) -- +1 for "C"
     lpaths ← (getLength paths)
     consPath ← (generateRef ((suc lcons) + lpaths)) -- +1 for "C"
     refls' ← (generateRef ((suc ref) + lcons)) -- +1 for "C"
     parsPnt ← (takeTC d1 refls')
     parsPath ← (pure (map (λ z → z + lpaths) parsPnt))
     t ← (getType indTyp)
     index ← (getIndexValue zero d1 t)
     pntTyp ← (getType Rpnt)
     pntTyp' ← (rmPars d1 pntTyp)
     mapPnt ← (βrecMapPath Rpnt pntInd elim parsPath consPath [] indTyp index pntTyp')
     -- (βrecMapPath Rpnt (pntInd + lpaths) elim lpaths d1 parsPath consPath [] indTyp indL indL pntTyp')
     (debugPrint "tc.sample.debug" 20 (strErr "index length " ∷ strErr (showNat index) ∷ []))
     pathTyp ← (getβrecPaths baseElim d1 mapPnt parsPnt consPnt indTyp paths)
     funType ← (getMapConsTypeList' indTyp d1 zero pathTyp pars indLs points)
     pure (pi (vArg (agda-sort (lit 0))) (abs "C" funType))
getβrecRtypePath Rpnt indType pntInd elim baseElim indLs points paths d1 d ref x = pure unknown


generateβRecHit' : Arg Name → (R : Name) → (pntInd : Nat) → (elim : Name) → (baseElim : Name) → 
  (indexList : List Nat) → (indType : Name) → (param : Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHit' (arg i f) R pntInd elim baseElim indLs indType d points paths = 
  do RTy ← (getType indType)
     funTypePath ← (getβrecRtypePath R indType pntInd elim baseElim indLs points paths d d zero RTy)
     (debugPrint "tc.sample.debug" 20 (strErr "issue : checking here ---> for paths comp " ∷ termErr funTypePath ∷ []))
     (declarePostulate (arg i f) funTypePath)

generateβRecHit'' : List (Arg Name) → (Lpaths : List Name) → (pntInd : Nat) → (elim : Name) → (baseElim : Name) → 
  (indexList : List Nat) → (indType : Name) → (params : Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHit'' (x ∷ xs) (p ∷ ps) (suc pntInd) elim baseElim indLs indType d points paths =
  do (generateβRecHit' x p pntInd elim baseElim indLs indType d points paths)
     (generateβRecHit'' xs ps pntInd elim baseElim indLs indType d points paths)
generateβRecHit'' [] p pntInd elim baseElim indLs indType d points paths = pure tt
generateβRecHit'' n p pntInd elim baseElim indLs indType d points paths = pure tt

generateβRecHitPath : (elim : Name) → (comp : List (Arg Name)) →
  (indType : Name) → (baseElim : Name) → (param : Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHitPath elim comp indType baseElim d points paths =
  do exp ← (getExprRef2 indType d points)
     argL ← (getLength comp)
     (debugPrint "tc.sample.debug" 20 (strErr "coming here" ∷ []))
     (generateβRecHit'' comp paths argL elim baseElim exp indType d points paths)
