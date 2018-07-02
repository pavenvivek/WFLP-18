-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}

open import Data.List
open import Function hiding (flip)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Automation.utils.reflectionUtils
open import Automation.lib.generateHit

module Automation.lib.generateRec where


getRecArgs2 : (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → TC (List (Arg Term))
getRecArgs2 args inds irefs =
  do args' ← dropTC 1 args -- drop C
     argC ← takeTC 1 args -- take C
     argC' ← generateRefTerm argC
     argsR ← generateIndexRef inds irefs args'
     pure (argC' ++L argsR)

generateMapRefRec2 : (f : Nat) → (fargs : List (Arg Term)) → (g : Name) → (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → Nat → TC Term
generateMapRefRec2 f fargs g args inds irefs 0 =
  do largs ← generateRefTerm args
     pure (def g (vArg (var f fargs) ∷ largs))
generateMapRefRec2 f fargs g args inds irefs (suc x) =
  do y ← generateMapRefRec2 f fargs g args inds irefs x
     pure (lam visible (abs "lx" y))

getTermRec : (g : Name) → (inds : List Nat) → (irefs : List (List Bool)) → (f : Nat) → (ref : Nat) → (args : List Nat) → Type → TC Term
getTermRec g inds irefs f 0 args (def ty y) =
  do largs ← generateRefTerm args
     pure (def g (vArg (var f []) ∷ largs))
getTermRec g inds irefs f ref args (def ty y) =
  do ls ← generateRef ref
     fargs ← generateRefTerm ls
     len ← getLength fargs
     let inds' = map (λ z → z + len) inds
         args' = map (λ z → z + len) args
     generateMapRefRec2 (f + len) fargs g args' inds' irefs len
getTermRec g inds irefs f ref args (pi (arg info dom) (abs s cdom)) =
  getTermRec g inds irefs f (suc ref) args cdom
getTermRec g inds irefs f ref args x = pure unknown

getTerm : (R : Name) → (ty : Name) → (inds : List Nat) → (irefs : List (List Bool)) → (cRef : Nat) → (lcarg : List Nat) → (lfarg : List Nat) → (cTy : Type) → TC (List (Arg Term))
getTerm R ty inds irefs cRef lcarg lfarg (def qn ls) = pure []
getTerm R ty inds irefs cRef lcarg lfarg (pi (arg info dom) (abs s cdom)) =
  do r ← (getListElement cRef lcarg)
     cdom' ← (getTerm R ty inds irefs (suc cRef) lcarg lfarg cdom)
     case! (checkCdmR R dom) of λ
      { true →
        do tm ← (getTermRec ty inds irefs r zero lfarg dom)
           pure (arg info (var r []) ∷ vArg tm ∷ cdom')
      ; false → pure (arg info (var r []) ∷ cdom')
      }
getTerm R ty inds irefs cRef lcarg lfarg x = pure []

getClause' : Nat → Nat → (R : Name) → (ty : Name) → (irefs : List (List Bool)) → (indLs : List Nat) → (lcons : List Name) → TC (List Clause)
getClause' l ref R ty irefs [] [] = pure []
getClause' l ref R ty irefs (i ∷ is) (x ∷ xs) =
  do y ← getType x
     d ← getParameters R
     y' ← rmPars d y
     il ← generateRef i
     argC ← getArgsCount 0 y'
     argC' ← getDiff argC i
     vars' ← getClauseVars zero l
     vars ← reverseTC vars'
     lfargRev ← getRef 0 vars
     lfarg ← reverseTC lfargRev
     lenlfarg ← getLength lfarg
     argInfo ← getHidArgs y'
     laP ← consArgs (suc lenlfarg) argInfo y'
     lcargRev ← getRef (suc lenlfarg) laP
     lcarg ← reverseTC lcargRev
     let inds = map (λ z → z + (argC' + (suc lenlfarg))) il
     Ccon ← getListElement ref lfarg
     xs' ← getClause' l (suc ref) R ty irefs is xs
     lb ← getIndexRef R i x
     case! isMemberBool true lb of λ
      { true →
        do ltm ← getTerm R ty inds irefs zero lcarg (lenlfarg ∷ lfarg) y'
           pure ((clause (vArg (con x laP) ∷ vArg (var (showNat lenlfarg)) ∷ vars) (var Ccon ltm)) ∷ xs')
      ; false →
        do y'' ← rmIndex i y'
           ltm ← getTerm R ty inds irefs zero lcarg (lenlfarg ∷ lfarg) y''
           pure ((clause (vArg (con x laP) ∷ vArg (var (showNat lenlfarg)) ∷ vars) (var Ccon ltm)) ∷ xs')
      }
getClause' l ref R ty irefs x y = pure [] -- Invalid case

getClause : Nat → Nat → (R : Name) → (ty : Name) → (lcons : List Name) → TC (List Clause)
getClause l ref R ty lcons =
  do exp ← getExpRef R
     lbs ← getIndexRefInfo R exp lcons
     getClause' l ref R ty lbs exp lcons


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


-- getRefTypes :

getMapConsTypeList : Name → (Cref : Nat) → (Crefbase : Nat) → (pars : List Nat) → (indexList : List Nat) → (lcons : List Name) → TC Type
getMapConsTypeList R Cref Crefbase pars [] [] = pure (var Crefbase [])
getMapConsTypeList R Cref Crefbase pars (i ∷ is) (x ∷ xs) =
  do let pars' = (map (λ z → z + 1) pars)
     d ← (getParameters R)
     ty ← (getType x)
     x' ← (rmPars d ty)
     lb ← (getIndexRef R i x)
     case! (isMemberBool true lb) of λ
      { true →
        do t ← (getMapConstructorType Cref pars R true x')
           xt ← (getMapConsTypeList R (suc Cref) Crefbase pars' is xs)
           pure (pi (vArg t) (abs "_" xt))
      ; false →
        do x'' ← (rmIndex i x')
           t ← (getMapConstructorType Cref pars R true x'')
           xt ← (getMapConsTypeList R (suc Cref) Crefbase pars' is xs)
           pure (pi (vArg t) (abs "_" xt))
      }
getMapConsTypeList R Cref Crefbase pars x y = pure unknown -- Invalid case

getRtype : (R : Name) → (ref : Nat) → (RTy : Type) → TC Type
getRtype R ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtype R (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtype R ref (agda-sort Level) =
  do cns ← (getConstructors R)
     ty ← (getConsTypes cns)
     lcons ← (getLength cns)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     d ← (getParameters R)
     Rty' ← (getType R)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     pars ← (takeTC d refls)
     exp ← (getExpRef R)
     funType ← (getMapConsTypeList R zero lcons pars exp cns)
     pure (pi (vArg (def R Rargs)) (abs "R" (pi (vArg (agda-sort (lit 0))) (abs "C" funType))))
getRtype R ref x = pure unknown

generateRec : Arg Name → Name → TC ⊤
generateRec (arg i f) t =
  do cns ← getConstructors t
     lcons ← getLength cns
     cls ← getClause lcons zero t f cns
     RTy ← getType t
     funType ← getRtype t zero RTy
     (debugPrint "tc.sample.debug" 20 (strErr "**generateRe [3] ---> " ∷ termErr funType ∷ []))
     declareDef (arg i f) funType
     defineFun f cls
