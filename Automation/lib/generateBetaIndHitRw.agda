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
-- open import Automation.lib.generateIndHit using (getPathsDep)

module Automation.lib.generateBetaIndHitRw where

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
getMapConstructorPathTypeDep' : (baseRec : Name) → (cref : Nat) → (path : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
                                (args : List Nat) → (indTyp : Name) → (ctype : Type) → (recurse : Bool) → Type → TC Type
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         args' = (map (λ z → z + 1) args)
         args'' = (args' ∷L 0)
     t1' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu t1)
     t2' ← (getMapConstructorPathTypeDep' baseRec (suc cref) path pars' cons' index' args'' indTyp ctype rcu t2)
     pure (pi (arg info t1') (abs s t2'))
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (def x lsargs) =
  case (primQNameEquality x (quote _≡_)) of λ
   { true →
       do lsargsvis ← (removeHidden lsargs)
          lsargs' ← (map' (λ { (arg i term) →
                                  do term' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu term)
                                     case term' of λ
                                      { (var x' args') →
                                          do argCons ← (generateRefTerm cons)
                                             argPars ← (generateRefTermHid pars)
                                             argInds ← (generateRefTermHid index)
                                             args'' ← (returnTC ((vArg (var x' args') ∷ []) ++L argCons))
                                             pure (arg i (def baseRec args''))
                                      ; term'' → pure (arg i term'')
                                      }
                              })
                           lsargsvis)
          args' ← (generateRefTerm args)
          argInfoL ← (getHidArgs ctype)
          cargs ← (generateRefTerm' argInfoL args)
          fstarg ← (takeTC 1 lsargs') -- take the first argument
          fstarg' ← (pure (vArg (def (quote transport) (vArg (var cref []) ∷ vArg (def path cargs) ∷ fstarg)) ∷ [])) -- trans C (p x) ≡ (p y)
          secarg ← (dropTC 1 lsargs')
          pure (def (quote _≡_) (fstarg' ++L secarg))
   ; false →
       do x' ← (getType x)
          case! (getBaseType x') of λ
           { (def xty argL) →
               case (_and_ rcu (primQNameEquality xty indTyp)) of λ
                { true →
                    do lsargs' ← (map' (λ { (arg i term) →
                                               do term' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype false term)
                                                  pure (arg i term') })
                                        lsargs)
                       argCons ← (generateRefTerm cons)
                       argPars ← (generateRefTermHid pars)
                       argInds ← (generateRefTermHid index)
                       args' ← (pure ((vArg (def x lsargs') ∷ []) ++L argCons))
                       pure (def baseRec args')
                ; false →
                    do lsargs' ← (map' (λ { (arg i term) →
                                               do term' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu term)
                                                  pure (arg i term')
                                           }) lsargs)
                       pure (def x lsargs')
                }
                ; type → pure (def x lsargs)
           }
   }
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (var ref lsargs) =
  do let pind = (pars ++L index)
         refL = (pind ++L args)
     refL' ← (reverseTC refL)
     x ← (getListElement ref refL')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
          do lsargs' ← (map' (λ { (arg i term) →
                                     do term' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu term)
                                        pure (arg i term') }) lsargs)
             pure (var x lsargs')
      }
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu x = pure x

getMapConstructorPathTypeDep : (baseRec : Name) → (cref : Nat) → (path : Name) → (pars : List Nat) → (cons : List Nat) →
  (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp 0 x = getMapConstructorPathTypeDep' baseRec cref path pars cons index [] indTyp x true x
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         index'' = (index' ∷L 0)
     ty ← (getMapConstructorPathTypeDep baseRec (suc cref) path pars' cons' index'' indTyp x t2)
     pure (pi (arg info t1) (abs s ty))
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp x y = pure unknown                                                                            

getβIndPaths : (baseRec : Name) → (params : Nat) → (mapPath : Type) → (ref : Nat) → (pars : List Nat) → (cons : List Nat) →
  (indType : Name) → (points : List Name) → (paths : List Name) → TC Type
getβIndPaths baseRec d mapPath ref pars cons indTyp pts [] = pure mapPath
getβIndPaths baseRec d mapPath ref pars cons indTyp pts (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getβIndPaths baseRec d mapPath (suc ref) pars' cons' indTyp pts xs)
     ty ← (getType x)
     lcons ← (getLength pts)
     ty' ← (rmPars d ty)
     ty2 ← (getType indTyp)
     index ← (getIndexValue zero d ty2)
     x' ← (getMapConstructorPathTypeDep baseRec (lcons + ref) x pars cons [] indTyp index ty') 
     pure (pi (vArg x') (abs "_" xs'))

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


getPathsDepRw : (baseRec : Name) → (indRec : Name) → (params : Nat) → (CRefBase : Nat) → (lpnts : Nat) → (cons2 : List Nat) → (pars : List Nat) → (cons : List Nat) →
  (indType : Name) → (paths : List Name) → TC Type
getPathsDepRw baseRec indRec d CRefBase lpnts cons2 pars cons indTyp [] =
  do argCons ← (generateRefTerm cons2)
     argConsPnts ← takeTC (suc lpnts) argCons  
     pure (def (quote _↦_) (vArg (def indRec (vArg (var (suc CRefBase) []) ∷ argCons)) ∷ vArg (def baseRec (vArg (var (suc CRefBase) []) ∷ argConsPnts)) ∷ []))
getPathsDepRw baseRec indRec d CRefBase lpnts cons2 pars cons indTyp (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getPathsDepRw baseRec indRec d (suc CRefBase) lpnts cons2 pars' cons' indTyp xs)
     ty ← (getType x)
     ty' ← (rmPars d ty)
     ty2 ← (getType indTyp)
     index ← (getIndexValue zero d ty2)
     -- index ← (getIndex' indTyp)
     x' ← (getMapConstructorPathTypeDep baseRec CRefBase x pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getRtypePathDepRw : (indTyp : Name) → (params : Nat) → (indexList : List Nat) → (baseRec : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) →
  (ref : Nat) → (RTy : Type) → TC Type
getRtypePathDepRw indTyp d exp baseRec indRec points paths ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypePathDepRw indTyp d exp baseRec indRec points paths (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypePathDepRw indTyp d exp baseRec indRec points paths ref (agda-sort Level) =
  do lcons ← (getLength points)
     lpaths ← (getLength paths)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     refls'' ← (generateRef (suc ref)) -- +1 for "R"
     pars ← (takeTC d refls)
     pars' ← (takeTC d refls'')
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     consPath' ← (generateRef ((suc lcons) + lpaths)) -- +1 for "C"
     refls' ← (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
     parsPath ← (takeTC d refls')
     pathTyp ← (getPathsDepRw baseRec indRec d lcons lcons consPath' parsPath consPath indTyp paths)
     funType ← (getMapConsTypeListInd indTyp d zero pathTyp pars exp points points)
     Rty' ← (getType indTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     CType ← (getCTypeInd indTyp pars' d Rty')
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg CType) (abs "C" funType))))
getRtypePathDepRw indType d exp baseRec indRec points paths ref x = pure unknown


getPathsDep : (baseRec : Name) → (params : Nat) → (CRefBase : Nat) → (pars : List Nat) → (cons : List Nat) →
  (indType : Name) → (paths : List Name) → TC Type
getPathsDep baseRec d CRefBase pars cons indTyp [] = pure (var CRefBase (vArg (var (suc CRefBase) []) ∷ []))
getPathsDep baseRec d CRefBase pars cons indTyp (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getPathsDep baseRec d (suc CRefBase) pars' cons' indTyp xs)
     ty ← (getType x)
     ty' ← (rmPars d ty)
     ty2 ← (getType indTyp)
     index ← (getIndexValue zero d ty2)
     -- index ← (getIndex' indTyp)
     x' ← (getMapConstructorPathTypeDep baseRec CRefBase x pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getRtypePathDep : (indTyp : Name) → (params : Nat) → (indexList : List Nat) → (baseRec : Name) → (points : List Name) → (paths : List Name) →
  (ref : Nat) → (RTy : Type) → TC Type
getRtypePathDep indTyp d exp baseRec points paths ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypePathDep indTyp d exp baseRec points paths (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypePathDep indTyp d exp baseRec points paths ref (agda-sort Level) =
  do -- cns ← (getConstructors baseTyp)
     -- ty ← (getConsTypes cns)
     lcons ← (getLength points)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     refls'' ← (generateRef (suc ref)) -- +1 for "R"
     -- d ← (getParameters baseTyp)
     pars ← (takeTC d refls)
     pars' ← (takeTC d refls'')
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     refls' ← (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
     parsPath ← (takeTC d refls')
     -- exp ← (getExpRef baseTyp)
     -- pathTyp ← (getβIndPaths' baseRec d zero parsPath consPath indTyp points paths)
     pathTyp ← (getPathsDep baseRec d lcons parsPath consPath indTyp paths)
     funType ← (getMapConsTypeListInd indTyp d zero pathTyp pars exp points points)
     Rty' ← (getType indTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     CType ← (getCTypeInd indTyp pars' d Rty')
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg CType) (abs "C" funType))))
getRtypePathDep indType d exp baseRec points paths ref x = pure unknown

generateElim : Arg Name → (cmp : Arg Name) → (indType : Name) → (baseElim : Name) → (param : Nat) → (indexList : List Nat) →
  (points : List Name) → (paths : List Name) → TC ⊤
generateElim (arg i f) cmp indType baseElim d exp points paths = 
  do RTy ← (getType indType)
     funTypePath ← (getRtypePathDep indType d exp baseElim points paths zero RTy)
     -- (debugPrint "tc.sample.debug" 20 (strErr "issue : Eliminator $$$###*** ---> " ∷ termErr funTypePath ∷ []))
     cmpRule ← (getRtypePathDepRw indType d exp baseElim f points paths zero RTy)
     (declarePostulate (arg i f) funTypePath)
     (debugPrint "tc.sample.debug" 20 (strErr "issue : Computation Rule ---> " ∷ termErr cmpRule ∷ []))
     (declarePostulate cmp cmpRule)

generateβIndHitRw : (elim : Arg Name) → (comp : Arg Name) →
  (indType : Name) → (baseElim : Name) → (param : Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβIndHitRw (arg i elim) comp indType baseElim d points paths =
  do exp ← (getExprRef2 indType d points)
     -- argL ← (getLength comp)
     (generateElim (arg i elim) comp indType baseElim d exp points paths)
     -- (generateβRec'' comp points exp argL elim baseElim exp indType d points paths)
