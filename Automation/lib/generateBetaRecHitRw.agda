{-# OPTIONS --verbose tc.sample.debug:20 #-}
{-# OPTIONS --rewriting #-}

open import Data.List
open import Function hiding (flip)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Automation.utils.reflectionUtils
open import Automation.utils.pathUtils
-- open import Automation.lib.generateRec using (getMapConstructorType; generateRec)

module Automation.lib.generateBetaRecHitRw where

-- -----

generateMapRefRec2 : (f : Nat) → (fargs : List (Arg Term)) → (g : Name) → (args : List Nat) →  Nat → TC Term
generateMapRefRec2 f fargs g args 0 =
  do largs ← generateRefTerm args
     pure (def g (vArg (var f fargs) ∷ largs))
generateMapRefRec2 f fargs g args (suc x) =
  do y ← generateMapRefRec2 f fargs g args x
     pure (lam visible (abs "lx" y))

getTermRec : (g : Name) → (f : Nat) → (ref : Nat) → (args : List Nat) → Type → TC Term
getTermRec g f 0 args (def ty y) =
  do largs ← generateRefTerm args
     -- (debugPrint "tc.sample.debug" 20 (strErr "getTermRec 2 !!!!!! *** " ∷ []))
     pure (def g (vArg (var f []) ∷ largs))
getTermRec g f ref args (def ty y) =
  do ls ← generateRef ref
     _ ← printList ls
     (debugPrint "tc.sample.debug" 20 (strErr "printList 2 *** " ∷ []))
     fargs ← generateRefTerm ls
     len ← getLength fargs
     let args' = map (λ z → z + len) args
     generateMapRefRec2 (f + len) fargs g args' len
getTermRec g f ref args (pi (arg info dom) (abs s cdom)) =
  do (debugPrint "tc.sample.debug" 20 (strErr "getTermRec !!! *** " ∷ []))
     getTermRec g f (suc ref) args cdom
getTermRec g f ref args x = pure unknown

getTerm : (R : Name) → (ty : Name) → (cRef : Nat) → (lcarg : List Nat) → (lfarg : List Nat) → (cTy : Type) → TC (List (Arg Term))
getTerm R ty cRef lcarg lfarg (def qn ls) = pure []
getTerm R ty cRef lcarg lfarg (pi (arg info dom) (abs s cdom)) =
  do r ← (getListElement cRef lcarg)
     _ ← printList lcarg
     (debugPrint "tc.sample.debug" 20 (strErr "getTerm !!! cRef *** " ∷ strErr (showNat cRef) ∷ []))
     (debugPrint "tc.sample.debug" 20 (strErr "getTerm !!! r *** " ∷ strErr (showNat r) ∷ []))
     cdom' ← (getTerm R ty (suc cRef) lcarg lfarg cdom)
     case! (checkCdmR R dom) of λ
      { true →
        do tm ← (getTermRec ty r zero lfarg dom)
           pure (arg info (var r []) ∷ vArg tm ∷ cdom')
      ; false →
        do pure (arg info (var r []) ∷ cdom')
      }
getTerm R ty cRef lcarg lfarg x = pure []


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
getMapConstructorType : (Cref : Nat) → (pars : List Nat) → (R : Name) → (mapTy : Bool) → Type → TC Type
getMapConstructorType Cref pars R mapTy (pi (arg info t1) (abs s t2)) =
  case! checkCdm (def R []) t1 of λ
   { true →
     do let pars' = map (λ z → z + 2) pars -- +1 for Rcons and +1 for Ccons
            pars'' = map (λ z → z + 1) pars
            pars''' = pars' ∷L 1 -- 1 for Rcons and 0 for Ccons -- ((pars' ∷L 1) ∷L 0))
        t2' ← getMapConstructorType (suc (suc Cref)) pars''' R mapTy t2
        t1' ← getMapConstructorType Cref pars R false t1
        cdom' ← getMapConstructorType (suc Cref) pars'' R false t1
        cdom'' ← changeCodomain (suc Cref) cdom'
        pure (pi (arg info t1') (abs s (pi (arg info cdom'') (abs "Ccons" t2'))))
   ; false →
     do let pars' = map (λ z → z + 1) pars
            pars'' = pars' ∷L 0
        t2' ← getMapConstructorType (suc Cref) pars'' R mapTy t2
        t1' ← getMapConstructorType Cref pars R false t1
        pure (pi (arg info t1') (abs s t2'))
   }
getMapConstructorType Cref pars R mapTy (def x lsargs) =
  case (_and_ mapTy (primQNameEquality R x)) of λ
   { true → pure (var Cref [])
   ; false →
     case null lsargs of λ
      { true → pure (def x [])
      ; false →
        do lsargs' ←
             (map' (λ { (arg i term) →
                       do term' ← getMapConstructorType Cref pars R mapTy term
                          pure (arg i term') })
                   lsargs)
           pure (def x lsargs')
      }
   }
getMapConstructorType Cref pars R mapTy (var ref lsargs) =
  do pars' ← (reverseTC pars)
     x ← (getListElement ref pars')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ←
             (map' (λ { (arg i term) →
                       do term' ← (getMapConstructorType Cref pars R mapTy term)
                          pure (arg i term') })
                  lsargs)
           pure (var x lsargs')
      }
getMapConstructorType Cref pars R mapTy (lam vis (abs s term)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0)
     term' ← (getMapConstructorType Cref pars'' R mapTy term)
     pure (lam vis (abs s term'))
getMapConstructorType Cref pars R mapTy (con cn lsargs) =
  case (null lsargs) of λ
   { true → pure (con cn [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                     do term' ← (getMapConstructorType Cref pars R mapTy term)
                        pure (arg i term') }) lsargs)
        pure (con cn lsargs')
   }
getMapConstructorType Cref pars R mapTy (meta x lsargs) =
  case (null lsargs) of λ
   { true → pure (meta x [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                     do term' ← (getMapConstructorType Cref pars R mapTy term)
                        pure (arg i term') }) lsargs)
        pure (meta x lsargs')
   }
getMapConstructorType Cref pars R mapTy (pat-lam cs lsargs) =
  case (null lsargs) of λ
   { true → pure (pat-lam cs [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                     do term' ← (getMapConstructorType Cref pars R mapTy term)
                        pure (arg i term') }) lsargs)
        pure (pat-lam cs lsargs') }
getMapConstructorType Cref pars R mapTy x = pure x

getMapConsTypeList : Name → (params : Nat) → (Cref : Nat) → (paths : Type) → (pars : List Nat) → (indexList : List Nat) → (lcons : List Name) → TC Type
getMapConsTypeList R d Cref paths pars i [] = pure paths
getMapConsTypeList R d Cref paths pars (i ∷ is) (x ∷ xs) =
  do ty ← (getType x)
     x' ← (rmPars d ty)
     pars' ← (pure (map (λ z → z + 1) pars))
     lb ← (getIndexRef2 d i x)
     case! (isMemberBool true lb) of λ
      { true →
        do t ← (getMapConstructorType Cref pars R true x')
           xt ← (getMapConsTypeList R d (suc Cref) paths pars' is xs)
           pure (pi (vArg t) (abs "_" xt))
      ; false →
        do x'' ← (rmIndex i x')
           t ← (getMapConstructorType Cref pars R true x'')
           xt ← (getMapConsTypeList R d (suc Cref) paths pars' is xs)
           pure (pi (vArg t) (abs "_" xt))
      }
getMapConsTypeList R d Cref paths pars x y = pure unknown -- Invalid case



-- -----------


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

getPathsRw : (baseRec : Name) → (rec : Name) → (CRefBase : Nat) → (lpnts : Nat) → (cons2 : List Nat) → (pars : List Nat) → (cons : List Nat) →
  (indType : Name) → (params : Nat) → (paths : List Name) → TC Type
getPathsRw baseRec indRec CRefBase lpnts cons2 pars cons indTyp d [] =
  do argCons ← (generateRefTerm cons2)
     argConsPnts ← takeTC (suc lpnts) argCons  
     pure (def (quote _↦_) (vArg (def indRec (vArg (var (suc CRefBase) []) ∷ argCons)) ∷ vArg (def baseRec (vArg (var (suc CRefBase) []) ∷ argConsPnts)) ∷ []))
getPathsRw baseRec indRec CRefBase lpnts cons2 pars cons indTyp d (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getPathsRw baseRec indRec (suc CRefBase) lpnts cons2 pars' cons' indTyp d xs)
     ty ← (getType x)
     ty' ← (rmPars d ty)
     ty2 ← (getType indTyp)
     index ← (getIndexValue zero d ty2)
     x' ← (getMapConstructorPathType baseRec pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getPaths : (baseRec : Name) → (CRefBase : Nat) → (pars : List Nat) → (cons : List Nat) → (indType : Name) → (params : Nat) → (paths : List Name) → TC Type
getPaths baseRec CRefBase pars cons indTyp d [] = pure (var CRefBase [])
getPaths baseRec CRefBase pars cons indTyp d (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getPaths baseRec (suc CRefBase) pars' cons' indTyp d xs)
     ty ← (getType x)
     ty' ← (rmPars d ty)
     ty2 ← (getType indTyp)
     index ← (getIndexValue zero d ty2)
     x' ← (getMapConstructorPathType baseRec pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))


getRtypePathRw : (indTyp : Name) → (indRec : Name) → (baseRec : Name) → (params : Nat) → (points : List Name) → (pathList : List Name) → (ref : Nat) → (RTy : Type) → TC Type
getRtypePathRw indTyp indRec baseRec d points pathList ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypePathRw indTyp indRec baseRec d points pathList (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypePathRw indTyp indRec baseRec d points pathList ref (agda-sort Level) =
  do lcons ← (getLength points)
     lpaths ← (getLength pathList)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     pars ← (takeTC d refls)
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     consPath' ← (generateRef ((suc lcons) + lpaths)) -- +1 for "C"
     refls' ← (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
     parsPath ← (takeTC d refls')
     exp ← (getExprRef2 indTyp d points)
     paths ← (getPathsRw baseRec indRec lcons lcons consPath' parsPath consPath indTyp d pathList)
     funType ← (getMapConsTypeList indTyp d zero paths pars exp points)
     Rty' ← (getType indTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg (agda-sort (lit 0))) (abs "C3" funType)))) 
getRtypePathRw indType indRec baseRec d points pathList ref x = pure unknown

getRtypePath : (indTyp : Name) → (baseRec : Name) → (params : Nat) → (points : List Name) → (pathList : List Name) → (ref : Nat) → (RTy : Type) → TC Type
getRtypePath indTyp baseRec d points pathList ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypePath indTyp baseRec d points pathList (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypePath indTyp baseRec d points pathList ref (agda-sort Level) =
  do lcons ← (getLength points)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     pars ← (takeTC d refls)
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     refls' ← (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
     parsPath ← (takeTC d refls')
     exp ← (getExprRef2 indTyp d points)
     paths ← (getPaths baseRec lcons parsPath consPath indTyp d pathList)
     funType ← (getMapConsTypeList indTyp d zero paths pars exp points)
     Rty' ← (getType indTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg (agda-sort (lit 0))) (abs "C3" funType)))) 
getRtypePath indType baseRec d points pathList ref x = pure unknown


generateElim : Arg Name → (cmp : Arg Name) → (indType : Name) → (baseElim : Name) → (param : Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateElim (arg i f) cmp indType baseElim d points paths = 
  do RTy ← (getType indType)
     funTypePath ← (getRtypePath indType baseElim d points paths zero RTy)
     cmpRule ← (getRtypePathRw indType f baseElim d points paths zero RTy)
     (declarePostulate (arg i f) funTypePath)
     (debugPrint "tc.sample.debug" 20 (strErr "issue : checking here ---> " ∷ termErr cmpRule ∷ []))
     (declarePostulate cmp cmpRule)

generateβRecHitRw : (elim : Arg Name) → (comp : Arg Name) →
  (indType : Name) → (baseElim : Name) → (param : Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHitRw (arg i elim) comp indType baseElim d points paths =
  do (generateElim (arg i elim) comp indType baseElim d points paths)


