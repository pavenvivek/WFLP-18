-- {-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Data.List
open import Function hiding (flip)
open import Agda.Builtin.Reflection
open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Automation.utils.reflectionUtils
open import Automation.lib.generateRec using (getMapConstructorType)


module Automation.lib.generateInd where

getTermRecDep : (g : Name) → (ils : List Nat) → (irefs : List (List Bool)) → (f : Nat) → (ref : Nat) → (args : List Nat) → Type → TC Term
getTermRecDep g ils irefs f 0 args (def ty y) = do gargs ← (generateRefTerm args)
                                                   pure (def g (vArg (var f []) ∷ gargs))
getTermRecDep g ils irefs f ref args (def ty y) = do ls ← (generateRef ref)
                                                     fargs ← (generateRefTerm ls)
                                                     len ← (getLength fargs)
                                                     gargs' ← pure (map (λ z → z + len) args)
                                                     gargs ← (generateRefTerm gargs')
                                                     tm ← (generateMapRef (f + len) fargs g gargs len)
                                                     pure tm
getTermRecDep g ils irefs f ref args (pi (arg info dom) (abs s cdom)) = do cdom' ←  (getTermRecDep g ils irefs f (suc ref) args cdom)
                                                                           pure cdom'
getTermRecDep g ils irefs f ref args x = pure unknown

getTermDep : (R : Name) → (ty : Name) → (ils : List Nat) → (irefs : List (List Bool)) → (cRef : Nat) → (lcarg : List Nat) → (lfarg : List Nat) → (cTy : Type) → TC (List (Arg Term))
getTermDep R ty ils irefs cRef lcarg lfarg (def qn ls) = pure []
getTermDep R ty ils irefs cRef lcarg lfarg (pi (arg info dom) (abs s cdom)) = do r ← (getListElement cRef lcarg)
                                                                                 cdom' ← (getTermDep R ty ils irefs (suc cRef) lcarg lfarg cdom)
                                                                                 case! (checkCdmR R dom) of λ
                                                                                  { true →
                                                                                      do tm ← (getTermRecDep ty ils irefs r zero lfarg dom)
                                                                                         pure (arg info (var r []) ∷ vArg tm ∷ cdom')
                                                                                  ; false → pure (arg info (var r []) ∷ cdom')
                                                                                  }
getTermDep R ty ils irefs cRef lcarg lfarg x = pure []

getClauseDep' : Nat → Nat → (R : Name) → (ty : Name) → (irefs : List (List Bool)) → (indList : List Nat) → (lcons : List Name) → TC (List Clause)
getClauseDep' l ref R ty irefs [] [] = pure []
getClauseDep' l ref R ty irefs (i ∷ is) (x ∷ xs) =
  do y ← (getType x)
     d ← (getParameters R)
     y' ← (rmPars d y)
     il ← (generateRef i)
     argC ← (getArgsCount 0 y')
     argC' ← (getDiff argC i)
     vars' ← (getClauseVars zero l)
     vars ← (reverseTC vars')
     lfargRev ← (getRef 0 vars)
     lfarg ← (reverseTC lfargRev)
     lenlfarg ← (getLength lfarg)
     argInfo ← (getHidArgs y')
     laP ← (consArgs (suc lenlfarg) argInfo y')
     lcargRev ← (getRef (suc lenlfarg) laP)
     lcarg ← (reverseTC lcargRev)
     il' ← (pure (map (λ z → z + (argC' + (suc lenlfarg))) il)) 
     ltm ← (getTermDep R ty il' irefs zero lcarg (lenlfarg ∷ lfarg) y')
     Ccon ← (getListElement ref lfarg)
     xs' ← (getClauseDep' l (suc ref) R ty irefs is xs)
     pure ((clause (vArg (con x laP) ∷ vArg (var (showNat lenlfarg)) ∷ vars) (var Ccon ltm)) ∷ xs')
getClauseDep' l ref R ty irefs x y = pure [] -- Invalid case

getClauseDep : Nat → Nat → (R : Name) → (ty : Name) → (lcons : List Name) → TC (List Clause)
getClauseDep l ref R ty lcons =
  do exp ← (getExpRef R)
     lbs ← (getIndexRefInfo R exp lcons)
     (getClauseDep' l ref R ty lbs exp lcons)

{-# TERMINATING #-}
getMapConstructorTypeInd : (Cref : Nat) → (pars : List Nat) → (inds : List Nat) →
  (args : List Nat) → (R : Name) → (mapTy : Bool) → (ctype : Type) → (cns : Name) → Type → TC Type
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (pi (arg info t1) (abs s t2)) =
  case! (checkCdm (def R []) t1) of λ
   { true →
     do let pars' = (map (λ z → z + 2) pars) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            pars'' = (pars' ∷L 1) -- 1 for t1' and 0 for cdom' -- ((pars' ∷L 1) ∷L 0)
            pars''' = (map (λ z → z + 1) pars) -- +1 for Rcons (t1')
            inds' = (map (λ z → z + 1) inds) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            inds'' = (map (λ z → z + 2) inds) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            args' = (map (λ z → z + 1) args) -- +1 for Rcons (t1') 
            args'' = (args' ∷L 0) -- 0 for Rcons (t1')
            args''' = (map (λ z → z + 1) args'') -- +1 for Ccons (cdom')
        t1'' ← (getMapConstructorType (suc Cref) pars''' R false t1)
        cdom' ← (changeCodomainInd (suc Cref) (inds' ++L args') zero t1'')
        t2' ← (getMapConstructorTypeInd (suc (suc Cref)) pars'' inds'' args''' R mapTy ctype cns t2)
        t1' ← (getMapConstructorTypeInd Cref pars inds args R false ctype cns t1)
        pure (pi (arg info t1') (abs s (pi (arg info cdom') (abs "Ccons" t2'))))
    ; false →
      do let pars' = (map (λ z → z + 1) pars) -- +1 for Rcons (t1')
             pars'' = (pars' ∷L 0) -- 0 for Rcons (t1')
             inds' = (map (λ z → z + 1) inds) -- +1 for Rcons (t1')
             args' = (map (λ z → z + 1) args) -- +1 for Rcons (t1')
             args'' = (args' ∷L 0) -- 0 for Rcons (t1')
         t2' ← (getMapConstructorTypeInd (suc Cref) pars'' inds' args'' R mapTy ctype cns t2)
         t1' ← (getMapConstructorTypeInd Cref pars inds args R false ctype cns t1)
         pure (pi (arg info t1') (abs s t2'))
   }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (def x lsargs) =
  case (_and_ mapTy (primQNameEquality R x)) of λ
   { true →
     do args' ← (generateRefTerm args)
        argInfoL ← (getHidArgs ctype)
        cargs ← (generateRefTerm' argInfoL args)
        d ← (getParameters x)
        index ← (dropTC d lsargs)
        index' ← (updateArgs (inds ++L args) index)
        indexH ← (changeVisToHid index')
        pure (var Cref (indexH ++L (vArg (con cns cargs) ∷ [])))
   ; false →
     case null lsargs of λ
       { true → returnTC (def x [])
       ; false →
         do lsargs' ←
              (map' (λ { (arg i term) →
                         do term' ← (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                            pure (arg i term') }) lsargs)
            pure (def x lsargs')
       }
   }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (var ref lsargs) =
  do pars' ← (reverseTC pars)
     x ← (getListElement ref pars')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ← (map' (λ { (arg i term) →
                                   do term' ← (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                                      pure (arg i term') })
                            lsargs)
           pure (var x lsargs')
      }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (lam vis (abs s term)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0)
     term' ← (getMapConstructorTypeInd Cref pars'' inds args R mapTy ctype cns term)
     pure (lam vis (abs s term'))                                                                        
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (con cn lsargs) =
  case (null lsargs) of λ
   { true → pure (con cn [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (con cn lsargs')
   }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (meta x lsargs) =
  case (null lsargs) of λ
   { true → pure (meta x [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (meta x lsargs')
   }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (pat-lam cs lsargs) =
  case (null lsargs) of λ
   { true → pure (pat-lam cs [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (pat-lam cs lsargs')
   }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns x = pure x

getMapConstructorTypeInd' : (Cref : Nat) → (pars : List Nat) → (index : List Nat) → (R : Name) → (cns : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorTypeInd' Cref pars inds R cns 0 x = getMapConstructorTypeInd Cref pars inds [] R true x cns x 
getMapConstructorTypeInd' Cref pars inds R cns (suc x) (pi (arg info t1) (abs s t2)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0) -- pars take index as well and will be used as the only list for var reference
         index' = (map (λ z → z + 1) inds)
         index'' = (index' ∷L 0)
     ty ← (getMapConstructorTypeInd' (suc Cref) pars'' index'' R cns x t2)
     pure (pi (arg info t1) (abs s ty))
getMapConstructorTypeInd' Cref pars inds R cns  x y = pure unknown                                                                            

getMapConsTypeListInd : Name → (Cref : Nat) → (Crefbase : Nat) → (pars : List Nat) → (indLs : List Nat) → (lcons : List Name) → TC Type
getMapConsTypeListInd R Cref Crefbase pars [] [] = pure (var Crefbase (vArg (var (suc Crefbase) []) ∷ []))
getMapConsTypeListInd R Cref Crefbase pars (i ∷ is) (cn ∷ xs) =
  do let pars' = (map (λ z → z + 1) pars)
     d ← (getParameters R)
     x ← (getType cn)
     x' ← (rmPars d x)
     t ← (getMapConstructorTypeInd' Cref pars [] R cn i x')
     xt ← (getMapConsTypeListInd R (suc Cref) Crefbase pars' is xs)
     pure (pi (vArg t) (abs "_" xt))
getMapConsTypeListInd R Cref Crefbase pars x y = pure unknown

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

getRtypeInd : (R : Name) → (ref : Nat) → (RTy : Type) → TC Type
getRtypeInd R ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypeInd R (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypeInd R ref (agda-sort Level) =
  do cns ← (getConstructors R)
     ty ← (getConsTypes cns)
     lcons ← (getLength cns)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     refls' ← (generateRef (suc ref)) -- +1 for "R"
     d ← (getParameters R)
     pars ← (takeTC d refls)
     pars' ← (takeTC d refls')
     ls ← (generateRef ref)
     exp ← (getExpRef R)
     funType ← (getMapConsTypeListInd R zero lcons pars exp cns)
     RType ← (getType R)
     argInfoL ← (getHidArgs RType)
     Rargs ← (generateRefTerm' argInfoL ls)
     CType ← (getCTypeInd R pars' d RType)
     pure (pi (vArg (def R Rargs)) (abs "R" (pi (vArg CType) (abs "C1" funType))))     
getRtypeInd R ref x = pure unknown

generateInd : Arg Name → Name → TC ⊤
generateInd (arg i f) t =
  do cns ← getConstructors t
     lcons ← getLength cns
     cls ← getClauseDep lcons zero t f cns
     RTy ← getType t
     funType ← getRtypeInd t zero RTy
     declareDef (arg i f) funType
     defineFun f cls
