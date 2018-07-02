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
open import Automation.lib.generateRec using (getMapConstructorType)
-- open import Automation.lib.generateInd using (getCTypeInd)

module Automation.lib.generateBetaInd where

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
     pure (def g (vArg (var f []) ∷ largs))
getTermRec g f ref args (def ty y) =
  do ls ← generateRef ref
     fargs ← generateRefTerm ls
     len ← getLength fargs
     let args' = map (λ z → z + len) args
     generateMapRefRec2 (f + len) fargs g args' len
getTermRec g f ref args (pi (arg info dom) (abs s cdom)) =
  do getTermRec g f (suc ref) args cdom
getTermRec g f ref args x = pure unknown

getTerm : (R : Name) → (ty : Name) → (cRef : Nat) → (lcarg : List Nat) → (lfarg : List Nat) → (cTy : Type) → TC (List (Arg Term))
getTerm R ty cRef lcarg lfarg (def qn ls) = pure []
getTerm R ty cRef lcarg lfarg (pi (arg info dom) (abs s cdom)) =
  do r ← (getListElement cRef lcarg)
     cdom' ← (getTerm R ty (suc cRef) lcarg lfarg cdom)
     case! (checkCdmR R dom) of λ
      { true →
        do tm ← (getTermRec ty r zero lfarg dom)
           pure (arg info (var r []) ∷ vArg tm ∷ cdom')
      ; false →
           pure (arg info (var r []) ∷ cdom')
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
getMapConstructorTypeInd2 : (Cref : Nat) → (params : Nat) → (cName : Name) → (pars : List Nat) → (inds : List Nat) → (args : List Nat) →
  (R : Name) → (mapTy : Bool) → (cty : Type) → (cns : Name) → Type → TC Type
getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns (pi (arg info t1) (abs s t2)) =
  case! (checkCdm (def R []) t1) of λ
   { true →
     do let pars' = (map (λ z → z + 2) pars) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            pars'' = ((pars' ∷L 1) ∷L 0) -- 1 for t1' and 0 for cdom'
            pars''' = (map (λ z → z + 1) pars) -- +1 for Rcons (t1')
            inds' = (map (λ z → z + 1) inds) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            inds'' = (map (λ z → z + 2) inds) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            args' = (map (λ z → z + 1) args) -- +1 for Rcons (t1') 
            args'' = (args' ∷L 0) -- 0 for Rcons (t1')
            args''' = (map (λ z → z + 1) args'') -- +1 for Ccons (cdom')
        t1'' ← (getMapConstructorType (suc Cref) pars''' R false t1)
        cdom' ← (changeCodomainInd (suc Cref) (inds' ++L args') zero t1'')
        t2' ← (getMapConstructorTypeInd2 (suc (suc Cref)) d cName pars'' inds'' args''' R mapTy ctype cns t2)
        t1' ← (getMapConstructorTypeInd2 Cref d cName pars inds args R false ctype cns t1)
        pure (pi (arg info t1') (abs s (pi (arg info cdom') (abs "Ccons" t2'))))
     ; false →
       do let pars' = (map (λ z → z + 1) pars) -- +1 for Rcons (t1')
              pars'' = (pars' ∷L 0) -- 0 for Rcons (t1')
              inds' = (map (λ z → z + 1) inds) -- +1 for Rcons (t1')
              args' = (map (λ z → z + 1) args) -- +1 for Rcons (t1')
              args'' = (args' ∷L 0) -- 0 for Rcons (t1')
          t2' ← (getMapConstructorTypeInd2 (suc Cref) d cName pars'' inds' args'' R mapTy ctype cns t2)
          t1' ← (getMapConstructorTypeInd2 Cref d cName pars inds args R false ctype cns t1)
          pure (pi (arg info t1') (abs s t2'))
     }
getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns (def x lsargs) =
  case (_and_ mapTy (primQNameEquality R x)) of λ
   { true →
     do args' ← (generateRefTerm args)
        argInfoL ← (getHidArgs ctype)
        cargs ← (generateRefTerm' argInfoL args)
        -- d ← (getParameters x)
        index ← (dropTC d lsargs)
        index' ← (updateArgs (inds ++L args) index)
        indexH ← (changeVisToHid index')
        pure (var Cref (indexH ++L (vArg (def cName cargs) ∷ [])))
     ; false →
       case (null lsargs) of λ
        { true → pure (def x [])
        ; false →
            do lsargs' ← (map' (λ { (arg i term) →
                                     do term' ← (getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns term)
                                        pure (arg i term') })
                                lsargs)
               pure (def x lsargs')
        }
     }
getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns (var ref lsargs) =
  do pars' ← (reverseTC pars)
     x ← (getListElement ref pars')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
         do lsargs' ← (map' (λ { (arg i term) →
                                  do term' ← (getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns term)
                                     pure (arg i term') })
                             lsargs)
            pure (var x lsargs')
      }
getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns (lam vis (abs s term)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0)
     term' ← (getMapConstructorTypeInd2 Cref d cName pars'' inds args R mapTy ctype cns term)
     pure (lam vis (abs s term'))                                                                        
getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns (con cn lsargs) =
  case (null lsargs) of λ
   { true → pure (con cn [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (con cn lsargs')
   }
getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns (meta x lsargs) =
  case (null lsargs) of λ
   { true → pure (meta x [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (meta x lsargs')
   }
getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns (pat-lam cs lsargs) =
  case (null lsargs) of λ
   { true → pure (pat-lam cs [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (pat-lam cs lsargs')
   }
getMapConstructorTypeInd2 Cref d cName pars inds args R mapTy ctype cns x = pure x

getMapConstructorTypeInd2' : (Cref : Nat) → (params : Nat) → (cName : Name) → (pars : List Nat) → (index : List Nat) →
  (R : Name) → (cns : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorTypeInd2' Cref d cName pars inds R cns 0 x = getMapConstructorTypeInd2 Cref d cName pars inds [] R true x cns x 
getMapConstructorTypeInd2' Cref d cName pars inds R cns (suc x) (pi (arg info t1) (abs s t2)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0) -- pars take index as well and will be used as the only list for var reference
         index' = (map (λ z → z + 1) inds)
         index'' = (index' ∷L 0)
     ty ← (getMapConstructorTypeInd2' (suc Cref) d cName pars'' index'' R cns x t2)
     pure (pi (arg info t1) (abs s ty))
getMapConstructorTypeInd2' Cref d cName pars inds R cns x y = pure unknown                                                                            

getMapConsTypeListInd : Name → (params : Nat) → (Cref : Nat) → (paths : Type) → (pars : List Nat) → (indLs : List Nat) →
  (points : List Name) → (lcons : List Name) → TC Type
getMapConsTypeListInd R d Cref paths pars x y [] = pure paths
getMapConsTypeListInd R d Cref paths pars (i ∷ is) (p ∷ ps) (cn ∷ xs) =
  do let pars' = (map (λ z → z + 1) pars)
     x ← (getType cn)
     x' ← (rmPars d x)
     indL ← (getIndex' R)
     t ← (getMapConstructorTypeInd2' Cref d p pars [] R cn i x')
     xt ← (getMapConsTypeListInd R d (suc Cref) paths pars' is ps xs)
     pure (pi (vArg t) (abs "_" xt))
getMapConsTypeListInd R d Cref paths pars x y z = pure unknown

-- -------

{-# TERMINATING #-}
βrecMapPath' : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (params : Nat) → (mapTy : Bool) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
  (indL : Nat) → (args : List Nat) → (argInfo : List ArgInfo) → (indTyp : Name) → Type → TC Type
βrecMapPath' Rpath RpathRef indRec d mapTy pars cons index indL args argInf indTyp (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         args' = (map (λ z → z + 1) args)
         args'' = (args' ∷L 0)
         argInfo' = (argInf ∷L info)
     t1' ← (βrecMapPath' Rpath RpathRef indRec d false pars cons index indL args argInf indTyp t1)
     t2' ← (βrecMapPath' Rpath (suc RpathRef) indRec d mapTy pars' cons' index' indL args'' argInfo' indTyp t2)
     case mapTy of λ
      { true → pure (pi (hArg t1') (abs s t2'))
      ; false → pure (pi (arg info t1') (abs s t2'))
      }
βrecMapPath' Rpath RpathRef indRec d mapTy pars cons index indL args argInf indTyp (def x lsargs) =
  case (_and_ mapTy (primQNameEquality x indTyp)) of λ
   { true →
     do let cons' = (map (λ z → z + 1) cons) -- +1 for lam "x"
            index' = (map (λ z → z + 1) index) -- +1 for lam "x"
        argCons ← (generateRefTerm cons)
        argPars ← (generateRefTermHid pars)
        argInds ← (generateRefTermHid index)
        argInds' ← (generateRefTermHid index)
        argInfo' ← (getHidArgs' argInf)
        argArgs ← (generateRefTerm' argInfo' args)
        args' ← (pure ((argPars ++L argInds) ++L argArgs))
        argIndRec ← (pure (def indRec (vArg (def Rpath []) ∷ argCons)))
        -- pathTyp ← (pure (con Rpath args'))
        y ← getType Rpath
        y' ← rmPars d y
        lb ← (getIndexRef2 d indL Rpath)
        case! (isMemberBool true lb) of λ
         { true →
           do y'' ← (rmIndex indL y')
              ltm ← getTerm indTyp indRec zero args cons y''
              CpathTyp ← (pure (var RpathRef ltm))
              pure (def (quote _↦_) (vArg (def indRec (vArg (def Rpath args') ∷ argCons)) ∷ vArg CpathTyp ∷ []))
         ; false →
           do y'' ← (rmIndex indL y')
              ltm ← getTerm indTyp indRec zero args cons y''
              CpathTyp ← (pure (var RpathRef ltm))
              pure (def (quote _↦_) (vArg (def indRec (vArg (def Rpath args') ∷ argCons)) ∷ vArg CpathTyp ∷ []))
         }
   ; false →
     do
        case (null lsargs) of λ
         { true → pure (def x [])
         ; false →
           do lsargs' ← (map' (λ { (arg i term) →
                                   do term' ← (βrecMapPath' Rpath RpathRef indRec d mapTy pars cons index indL args argInf indTyp term)
                                      pure (arg i term') }) lsargs)
              pure (def x lsargs')
         }
   }
βrecMapPath' Rpath RpathRef indRec d mapTy pars cons index indL args argInf indTyp (var ref lsargs) =
  do let pind = (pars ++L index)
         refL = (pind ++L args)
     refL' ← (reverseTC refL)
     x ← (getListElement ref refL')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ← (map' (λ { (arg i term) →
                                   do term' ← (βrecMapPath' Rpath RpathRef indRec d mapTy pars cons index indL args argInf indTyp term)
                                      pure (arg i term') }) lsargs)
           pure (var x lsargs')
      }
βrecMapPath' Rpath RpathRef indRec d mapTy pars cons index indL args argInf indTyp x = pure x

βrecMapPath : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (params : Nat) → (pars : List Nat) → (cons : List Nat) →
  (index : List Nat) → (indTyp : Name) → (indL : Nat) → (indLength : Nat) → Type → TC Type
βrecMapPath Rpath RpathRef indRec d pars cons index indTyp indL 0 x = βrecMapPath' Rpath RpathRef indRec d true pars cons index indL [] [] indTyp x
βrecMapPath Rpath RpathRef indRec d pars cons index indTyp indL (suc x) (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         index'' = (index' ∷L 0)
     ty ← (βrecMapPath Rpath (suc RpathRef) indRec d pars' cons' index'' indTyp indL x t2)
     pure (pi (hArg t1) (abs s ty))
βrecMapPath Rpath RpathRef indRec d pars cons index indTyp indL x y = pure unknown

getCTypeInd' : (R : Name) → (pars : List Nat) → (indexRef : Nat) → (RTy : Type) → TC Type
getCTypeInd' R pars indexRef (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do let pars' = (map (λ z → z + 1) pars)
     t2' ← (getCTypeInd' R pars' (suc indexRef) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getCTypeInd' R pars indexRef (agda-sort Level) =
  do ref' ← (generateRef indexRef)
     refls ← (generateRefTerm ref')
     pars' ← (generateRefTerm pars)
     Rty ← (getType R)
     level ← (getHidPars Rty)
     pars'' ← (dropTC level pars')
     args ← (pure (pars'' ++L refls))
     pure (pi (vArg (def R args)) (abs "RMap" (agda-sort (lit 0))))
getCTypeInd' R pars indexRef x = pure unknown

getCTypeInd : (R : Name) → (pars : List Nat) → (d : Nat) → (RTy : Type) → TC Type
getCTypeInd R pars 0 ty = do ty' ← (getCTypeInd' R pars zero ty)
                             pure ty'
getCTypeInd R pars (suc x) (pi (arg info t1) (abs s t2)) = do t2' ← (getCTypeInd R pars x t2)
                                                              pure t2'
getCTypeInd R pars x ty = pure unknown

getβrecRtypePath : (Rpoint : Name) → (indTyp : Name) → (pathInd : Nat) → (elim : Name) →
  (indexList : List Nat) → (indL : Nat) → (points : List Name) → (param : Nat) → (pars : Nat) → (ref : Nat) → (RTy : Type) → TC Type
getβrecRtypePath Rpnt indTyp pathInd elim indLs indL points d1 0 ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getβrecRtypePath Rpnt indTyp pathInd elim indLs indL points d1 0 ref t2)
     pure t2'
getβrecRtypePath Rpnt indTyp pathInd elim indLs indL points d1 (suc d) ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getβrecRtypePath Rpnt indTyp pathInd elim indLs indL points d1 d (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getβrecRtypePath Rpnt indTyp pathInd elim indLs indL points d1 d ref (agda-sort Level) =
  do lcons ← (getLength points)
     refls ← (generateRef (suc ref)) -- +1 for "C"
     pars ← (takeTC d1 refls)
     refls'' ← (generateRef ref)
     pars' ← (takeTC d1 refls'')
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     refls' ← (generateRef ((suc ref) + lcons)) -- +1 for "C"
     parsPath ← (takeTC d1 refls')
     pathTyp ← (getType Rpnt)
     RTyp ← (getType indTyp)
     RTyp' ← (rmPars d1 RTyp)
     pathTyp' ← (rmPars d1 pathTyp)
     mapPath ← (βrecMapPath Rpnt pathInd elim d1 parsPath consPath [] indTyp indL indL pathTyp')
     -- (debugPrint "tc.sample.debug" 20 (strErr "issue : comes here in Induction *** ---> " ∷ termErr mapPath ∷ []))
     funType ← (getMapConsTypeListInd indTyp d1 zero mapPath pars indLs points points)
     -- (debugPrint "tc.sample.debug" 20 (strErr "issue : comes here in Induction 2 *** ---> " ∷ termErr (pi (vArg (agda-sort (lit 0))) (abs "C" funType)) ∷ []))
     -- _ ← printList pars'
     CType ← (getCTypeInd indTyp pars' d RTyp')
     -- (debugPrint "tc.sample.debug" 20 (strErr "issue : CType ---> " ∷ termErr CType ∷ []))     
     pure (pi (vArg CType) (abs "C" funType))
     -- pure (pi (vArg (agda-sort (lit 0))) (abs "C" funType))
getβrecRtypePath Rpnt indType pathInd elim indLs indL points d1 d ref x = pure unknown


{-
getRtype : (indTyp : Name) → (params : Nat) → (indexList : List Nat) → (points : List Name) → (ref : Nat) → (RTy : Type) → TC Type
getRtype indTyp d exp points ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtype indTyp d exp points (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtype indTyp d exp points ref (agda-sort Level) =
  do lcons ← (getLength points)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     Rty' ← (getType indTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     pars ← (takeTC d refls)
     -- exp ← (getExpRef indTyp)
     funType ← (getMapConsTypeList indTyp d zero (var lcons []) pars exp points)
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg (agda-sort (lit 0))) (abs "C" funType))))
getRtype indTyp d exp points ref x = pure unknown
-}

getRtypeInd : (R : Name) → (params : Nat) → (indexList : List Nat) → (points : List Name) → (ref : Nat) → (RTy : Type) → TC Type
getRtypeInd R d exp points ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypeInd R d exp points (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypeInd R d exp points ref (agda-sort Level) =
  do -- cns ← (getConstructors R)
     -- ty ← (getConsTypes points)
     lcons ← (getLength points)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     refls' ← (generateRef (suc ref)) -- +1 for "R"
     -- d ← (getParameters R)
     pars ← (takeTC d refls)
     pars' ← (takeTC d refls')
     ls ← (generateRef ref)
     -- exp ← (getExpRef R)
     funType ← (getMapConsTypeListInd R d zero (var lcons (vArg (var (suc lcons) []) ∷ [])) pars exp points points)
     RType ← (getType R)
     argInfoL ← (getHidArgs RType)
     Rargs ← (generateRefTerm' argInfoL ls)
     CType ← (getCTypeInd R pars' d RType)
     pure (pi (vArg (def R Rargs)) (abs "R" (pi (vArg CType) (abs "C1" funType))))     
getRtypeInd R d exp points ref x = pure unknown

generateβRec' : Arg Name → (R : Name) → (pathInd : Nat) → (elim : Name) 
  (indexList : List Nat) → (indL : Nat) → (indType : Name) → (param : Nat) → (points : List Name) → TC ⊤
generateβRec' (arg i f) R pathInd elim indLs indL indType d points = 
  do RTy ← (getType indType)
     funTypePath ← (getβrecRtypePath R indType pathInd elim indLs indL points d d zero RTy)
     (debugPrint "tc.sample.debug" 20 (strErr "issue : checking here for Induction $$$###*** ---> " ∷ termErr funTypePath ∷ []))
     (declarePostulate (arg i f) funTypePath)

generateβRec'' : List (Arg Name) → (Lpoints : List Name) → (indList : List Nat) → (pathInd : Nat) → (elim : Name) →
  (indexList : List Nat) → (indType : Name) → (params : Nat) → (points : List Name) → TC ⊤
generateβRec'' (x ∷ xs) (p ∷ ps) (i ∷ is) (suc pathInd) elim indLs indType d points =
  do (generateβRec' x p pathInd elim indLs i indType d points)
     (generateβRec'' xs ps is pathInd elim indLs indType d points)
generateβRec'' [] p il pathInd elim indLs indType d points = pure tt
generateβRec'' n p il pathInd elim indLs indType d points = pure tt

generateElim : Arg Name → (indType : Name) → (param : Nat) → (indexList : List Nat) → (points : List Name) → TC ⊤
generateElim (arg i f) indType d exp points = 
  do RTy ← (getType indType)
     funTypePath ← (getRtypeInd indType d exp points zero RTy)
     (debugPrint "tc.sample.debug" 20 (strErr "issue : Eliminator $$$###*** ---> " ∷ termErr funTypePath ∷ []))
     (declarePostulate (arg i f) funTypePath)

generateβInd : (elim : Arg Name) → (comp : List (Arg Name)) →
  (indType : Name) → (param : Nat) → (points : List Name) → TC ⊤
generateβInd (arg i elim) comp indType d points =
  do exp ← (getExprRef2 indType d points)
     argL ← (getLength comp)
     (generateElim (arg i elim) indType d exp points)
     (generateβRec'' comp points exp argL elim exp indType d points)
