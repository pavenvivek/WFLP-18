{-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Data.List
open import Data.Bool
open import Function hiding (flip)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Automation.utils.reflectionUtils
open import Automation.utils.pathUtils
open import Automation.lib.generateRec using (getMapConstructorType)
open import Automation.lib.generateInd
open import Automation.lib.generateHit

module Automation.lib.generateIndHit where


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
       
getPathClauseDep' : (lpoints : Nat) → (lpaths : Nat) → (baseTyp : Name) → (params : Nat) → (baseRec : Name) →
  (indLs : List Nat) → (cns : List Name) → TC (List Clause)
getPathClauseDep' lpoints lpaths baseTyp d baseRec [] [] = pure []
getPathClauseDep' lpoints lpaths baseTyp d baseRec (i ∷ is) (x ∷ xs) =
  do xs' ← (getPathClauseDep' lpoints lpaths baseTyp d baseRec is xs)
     y ← (getType x)
     -- d ← (getParameters baseTyp)
     y' ← (rmPars d y)
     vars' ← (getClauseVars zero (lpoints + lpaths))
     vars ← (reverseTC vars')
     argInfo ← (getHidArgs y')
     laP ← (consArgs zero argInfo y')
     args ← (generateRef (suc lpoints)) -- +1 for "C"
     args' ← (pure (map (λ z → z + lpaths) args))
     argTerms ← (generateRefTerm args')
     argC ← (getLength laP)
     argCons ← (generateRef argC)
     laP' ← (returnTC (map (λ z → z + (suc (lpoints + lpaths))) argCons))
     reflaP' ← (generateRefTerm' argInfo laP')
     iargs ← (takeTC i reflaP')
     refargs ← (dropTC i reflaP')
     clargsRef ← (generateRef (d + i))
     clargsRef' ← (pure (map (λ z → z + (suc (argC + (lpoints + lpaths)))) clargsRef))
     clargs ← (generateRefTermHid clargsRef')
     clvars ← (getClauseVarsHid zero (d + i))
     pure ((clause (clvars ++L (vArg (con x laP) ∷ vArg (var "C") ∷ vars)) (def baseRec (clargs ++L (vArg (def x refargs) ∷ argTerms)))) ∷ xs')
getPathClauseDep' lpoints lpaths baseTyp d baseRec x y = pure [] -- Invalid case

getPathClauseDep : (lpoints : Nat) → (lpaths : Nat) → (indTyp : Name) → (baseRec : Name) → (params : Nat) →
  (cns : List Name) → TC (List Clause)
getPathClauseDep lpoints lpaths indTyp baseRec d cns =
  do exp ← (getExprRef2 indTyp d cns)
     (getPathClauseDep' lpoints lpaths indTyp d baseRec exp cns)

getPathClause : (lpoints : Nat) → (lpaths : Nat) → (baseRec : Name) → TC (List Clause)
getPathClause lpoints lpaths baseRec =
  do vars' ← (getClauseVars zero (lpoints + lpaths))
     vars ← (reverseTC vars')
     args ← (generateRef (suc (suc lpoints))) -- +1 for "C" and +1 for constructor
     args' ← (pure (map (λ z → z + lpaths) args))
     argTerms ← (generateRefTerm args')
     pure ((clause (vArg (var "x") ∷ vArg (var "C1") ∷ vars) (def baseRec argTerms)) ∷ [])



{-# TERMINATING #-}
getMapConstructorTypeInd2 : (Cref : Nat) → (cName : Name) → (pars : List Nat) → (inds : List Nat) → (args : List Nat) →
  (R : Name) → (params : Nat) → (mapTy : Bool) → (cty : Type) → (cns : Name) → Type → TC Type
getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns (pi (arg info t1) (abs s t2)) =
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
        t2' ← (getMapConstructorTypeInd2 (suc (suc Cref)) cName pars'' inds'' args''' R d mapTy ctype cns t2)
        t1' ← (getMapConstructorTypeInd2 Cref cName pars inds args R d false ctype cns t1)
        pure (pi (arg info t1') (abs s (pi (arg info cdom') (abs "Ccons" t2'))))
     ; false →
       do let pars' = (map (λ z → z + 1) pars) -- +1 for Rcons (t1')
              pars'' = (pars' ∷L 0) -- 0 for Rcons (t1')
              inds' = (map (λ z → z + 1) inds) -- +1 for Rcons (t1')
              args' = (map (λ z → z + 1) args) -- +1 for Rcons (t1')
              args'' = (args' ∷L 0) -- 0 for Rcons (t1')
          t2' ← (getMapConstructorTypeInd2 (suc Cref) cName pars'' inds' args'' R d mapTy ctype cns t2)
          t1' ← (getMapConstructorTypeInd2 Cref cName pars inds args R d false ctype cns t1)
          pure (pi (arg info t1') (abs s t2'))
     }
getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns (def x lsargs) =
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
                                     do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns term)
                                        pure (arg i term') })
                                lsargs)
               pure (def x lsargs')
        }
     }
getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns (var ref lsargs) =
  do pars' ← (reverseTC pars)
     x ← (getListElement ref pars')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
         do lsargs' ← (map' (λ { (arg i term) →
                                  do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns term)
                                     pure (arg i term') })
                             lsargs)
            pure (var x lsargs')
      }
getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns (lam vis (abs s term)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0)
     term' ← (getMapConstructorTypeInd2 Cref cName pars'' inds args R d mapTy ctype cns term)
     pure (lam vis (abs s term'))                                                                        
getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns (con cn lsargs) =
  case (null lsargs) of λ
   { true → pure (con cn [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (con cn lsargs')
   }
getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns (meta x lsargs) =
  case (null lsargs) of λ
   { true → pure (meta x [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (meta x lsargs')
   }
getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns (pat-lam cs lsargs) =
  case (null lsargs) of λ
   { true → pure (pat-lam cs [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (pat-lam cs lsargs')
   }
getMapConstructorTypeInd2 Cref cName pars inds args R d mapTy ctype cns x = pure x

getMapConstructorTypeInd2' : (Cref : Nat) → (cName : Name) → (pars : List Nat) → (index : List Nat) →
  (R : Name) → (params : Nat) → (cns : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorTypeInd2' Cref cName pars inds R d cns 0 x = getMapConstructorTypeInd2 Cref cName pars inds [] R d true x cns x 
getMapConstructorTypeInd2' Cref cName pars inds R d cns (suc x) (pi (arg info t1) (abs s t2)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0) -- pars take index as well and will be used as the only list for var reference
         index' = (map (λ z → z + 1) inds)
         index'' = (index' ∷L 0)
     ty ← (getMapConstructorTypeInd2' (suc Cref) cName pars'' index'' R d cns x t2)
     pure (pi (arg info t1) (abs s ty))
getMapConstructorTypeInd2' Cref cName pars inds R d cns x y = pure unknown                                                                            

getMapConsTypeListInd' : (R : Name) → (params : Nat) → (Cref : Nat) → (paths : Type) → (pars : List Nat) → (indLs : List Nat) →
  (points : List Name) → (lcons : List Name) → TC Type
getMapConsTypeListInd' R d Cref paths pars x y [] = pure paths
getMapConsTypeListInd' R d Cref paths pars (i ∷ is) (p ∷ ps) (cn ∷ xs) =
  do let pars' = (map (λ z → z + 1) pars)
     -- d ← (getParameters R)
     x ← (getType cn)
     x' ← (rmPars d x)
     -- indL ← (getIndex' R)
     ty2 ← (getType R)
     indL ← (getIndexValue zero d ty2)
     t ← (getMapConstructorTypeInd2' Cref p pars [] R d cn i x')
     xt ← (getMapConsTypeListInd' R d (suc Cref) paths pars' is ps xs)
     pure (pi (vArg t) (abs "_" xt))
getMapConsTypeListInd' R d Cref paths pars x y z = pure unknown


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

getPathsDep : (baseRec : Name) → (CRefBase : Nat) → (pars : List Nat) → (cons : List Nat) → (baseTyp : Name) →
  (indType : Name) → (params : Nat) → (paths : List Name) → TC Type
getPathsDep baseRec CRefBase pars cons baseTyp indTyp d [] = pure (var CRefBase (vArg (var (suc CRefBase) []) ∷ []))
getPathsDep baseRec CRefBase pars cons baseTyp indTyp d (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getPathsDep baseRec (suc CRefBase) pars' cons' baseTyp indTyp d xs)
     ty ← (getType x)
     -- d ← (getParameters baseTyp)
     ty' ← (rmPars d ty)
     ty2 ← (getType indTyp)
     index ← (getIndexValue zero d ty2)
     -- index ← (getIndex' baseTyp)
     x' ← (getMapConstructorPathTypeDep baseRec CRefBase x pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getRtypePathDep : (baseTyp : Name) → (indTyp : Name) → (baseRec : Name) → (param : Nat) → (points : List Name) → (pathList : List Name) →
  (ref : Nat) → (RTy : Type) → TC Type
getRtypePathDep baseTyp indTyp baseRec d points pathList ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypePathDep baseTyp indTyp baseRec d points pathList (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypePathDep baseTyp indTyp baseRec d points pathList ref (agda-sort Level) =
  do lcons ← (getLength points)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     refls'' ← (generateRef (suc ref)) -- +1 for "R"
     pars ← (takeTC d refls)
     pars' ← (takeTC d refls'')
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     refls' ← (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
     parsPath ← (takeTC d refls')
     exp ← (getExprRef2 indTyp d points)
     paths ← (getPathsDep baseRec lcons parsPath consPath indTyp indTyp d pathList)
     funType ← (getMapConsTypeListInd' indTyp d zero paths pars exp points points)
     Rty' ← (getType indTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     CType ← (getCTypeInd indTyp pars' d Rty')
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg CType) (abs "C" funType))))
getRtypePathDep baseTyp indType baseRec d points pathList ref x = pure unknown


generateIndHit : Arg Name → (indType : Name) → (baseRec : Name) → (param : Nat) →
  (points : List Name) → (paths : List Name) → TC ⊤
generateIndHit (arg i f) indType baseRec d points paths =
  do -- lcons ← getConstructors baseType
     lpoints ← getLength points
     lpaths ← getLength paths
     -- clauses ← getPathClauseDep lpoints lpaths indType baseRec d points
     clauses ← getPathClause lpoints lpaths baseRec
     RTy ← getType indType
     funTypePath ← getRtypePathDep indType indType baseRec d points paths zero RTy
     -- (debugPrint "tc.sample.debug" 20 (strErr "issue : induction path pos ---> " ∷ termErr funTypePath ∷ []))
     declareDef (arg i f) funTypePath
     defineFun f clauses
     -- generateβIndHit argD baseType baseRec indType f points paths
