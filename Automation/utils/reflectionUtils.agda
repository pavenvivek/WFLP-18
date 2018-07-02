-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
{-# OPTIONS --verbose tc.sample.debug:20 #-}
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Data.Bool
open import Data.String renaming (_++_ to _++S_)
open import Data.List
open import Data.Empty
open import Function hiding (flip)

module Automation.utils.reflectionUtils where

pattern vArg y = arg (arg-info visible relevant) y
pattern hArg y = arg (arg-info hidden relevant) y


infix 30 _↦_

postulate  -- HIT
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i

{-# BUILTIN REWRITE _↦_ #-}

_>>=_ : ∀ {α β} {A : Set α} {B : Set β} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_ : ∀ {α} {A : Set α} → TC ⊤ → TC A → TC A
_>>_ a b = bindTC a λ _ → b

pure : ∀ {α} {A : Set α} → A → TC A
pure = returnTC

_<*>_ : ∀ {α β} {A : Set α} {B : Set β} → TC (A → B) → TC A → TC B
f <*> x =
  do f' ← f
     x' ← x
     pure (f' x')

case!_of_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
case! x of f =
  do y ← x
     case y of f


{-- Generator for Recursion Principle --}

getConstructors : Name → TC (List Name)
getConstructors d =
  case! getDefinition d of λ
   { (data-type _ cs) → pure cs
   ; (record-type c _) → pure (c ∷ [])
   ; _ → typeError (strErr "Cannot get constructors of non-data or record type" ∷ nameErr d ∷ [])
   }


getParameters : Name → TC Nat
getParameters d =
  do data-type n _ ← (getDefinition d)
       where _ → pure 0
     pure n


isDefinition : Name → TC Bool
isDefinition d =
  case! getDefinition d of λ
   { (data-type _ cs) → pure true
   ; (record-type c _) → pure true
   ; _ → pure false
   }

{--
map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
--}

checkTrue : List Bool → TC Bool
checkTrue [] = returnTC false
checkTrue (true ∷ bs) = returnTC true
checkTrue (false ∷ bs) = checkTrue bs

eq : Nat → Nat → Bool
eq zero    zero    = true
eq (suc m) (suc n) = eq m n
{-# CATCHALL #-}
eq _       _       = false

isMember : Nat → List Nat → TC Bool
isMember a [] = returnTC false
isMember a (x ∷ xs) =
  if eq a x
    then pure true
    else isMember a xs

_or_ : (b1 : Bool) → (b2 : Bool) → Bool
x or true = true
true or x = true
x or y = false

_and_ : (b1 : Bool) → (b2 : Bool) → Bool
true and true = true
false and x = false
x and false = false

notB : (b : Bool) → Bool
notB true = false
notB false = true

-- [_] : ∀ {a} {A : Set a} → A → List A
-- [ x ] = x ∷ []

_++L_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

_∷L_ : ∀ {a} {A : Set a} → List A → A → List A
xs ∷L x = xs ++L [ x ]

-- foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
-- foldl f z []        = z
-- foldl f z (x ∷ xs) = foldl f (f z x) xs

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x

reverseTC : {A : Set} → List A → TC (List A)
reverseTC xs = returnTC (foldl (flip _∷_) [] xs)

showNat : Nat → String
showNat zero = "Z1"
showNat (suc x) = "S (" ++S showNat x ++S ")"

takeTC : ∀ {a} {A : Set a} → Nat → List A → TC (List A)
takeTC zero    xs       = returnTC []
takeTC (suc n) []       = returnTC []
takeTC (suc n) (x ∷ xs) = bindTC (takeTC n xs)
                                 (λ xs' → returnTC (x ∷ xs'))

{--
take1 : ∀ {a} {A : Set a} → ℕ → List A → (List A)
take1 zero    xs       = []
take1 (suc n) []       = []
take1 (suc n) (x ∷ xs) = x ∷ (take1 n xs)
--}

dropTC : ∀ {a} {A : Set a} → Nat → List A → TC (List A)
dropTC zero    xs       = returnTC xs
dropTC (suc n) []       = returnTC []
dropTC (suc n) (x ∷ xs) = bindTC (dropTC n xs) (λ xs' → returnTC xs')

consArgs : Nat → (vis : List Bool) → Type → TC (List (Arg Pattern))
consArgs ref b (def qn ls) = returnTC []
consArgs ref (b ∷ bs) (pi (arg info dom) (abs s cdom)) = bindTC (consArgs (suc ref) bs cdom)
                                                                (λ y → bindTC (returnTC b) λ
                                                                          { true → returnTC (hArg (var (showNat ref)) ∷ y) ;
                                                                            false → returnTC (vArg (var (showNat ref)) ∷ y) })
consArgs ref b x = returnTC (vArg absurd ∷ [])

getClauseVars : Nat → Nat → TC (List (Arg Pattern))
getClauseVars ref zero = returnTC []
getClauseVars ref (suc x) = bindTC (getClauseVars (suc ref) x)
                                   (λ y → returnTC (vArg (var (showNat ref)) ∷ y))

getClauseVarsHid : Nat → Nat → TC (List (Arg Pattern))
getClauseVarsHid ref zero = returnTC []
getClauseVarsHid ref (suc x) = bindTC (getClauseVarsHid (suc ref) x)
                                      (λ y → returnTC (hArg (var (showNat ref)) ∷ y))

getLength : ∀ {a} {A : Set a} → List A → TC Nat
getLength []       = returnTC 0
getLength (x ∷ xs) = bindTC (getLength xs)
                            (λ y → returnTC (1 + y))

getRef : ∀ {a} {A : Set a} → (ref : Nat) → List A → TC (List Nat)
getRef ref [] = returnTC []
getRef ref (x ∷ xs) = bindTC (getRef (suc ref) xs)
                              (λ y → returnTC (ref ∷ y))

checkCdmR : Name → Type → TC Bool
checkCdmR R (def ty y) = returnTC (primQNameEquality R ty)
checkCdmR R (pi (arg info t1) (abs s t2)) = bindTC (checkCdmR R t2) (λ y → returnTC y)
checkCdmR R y = returnTC false

getListElement : (n : Nat) → List Nat → TC Nat
getListElement 0 (x ∷ xs) = returnTC x
getListElement (suc n) (x ∷ xs) = bindTC (getListElement n xs)
                                         (λ y → returnTC y)
getListElement x y = returnTC x

_$_<or>_ : {A : Set} → Bool → A → A → TC A
b $ x <or> y = returnTC (if b then x else y)

generateRef : (l : Nat) → TC (List Nat)
generateRef 0 = returnTC []
generateRef (suc x) = bindTC (generateRef x)
                             (λ y → returnTC (x ∷ y))

generateRef1 : (l : Nat) → (List Nat)
generateRef1 0 = []
generateRef1 (suc x) = x ∷ (generateRef1 x)

generateMapRef : (f : Nat) → (fargs : List (Arg Term)) → (g : Name) → (gargs : List (Arg Term)) →  Nat → TC Term
generateMapRef f fargs g gargs 0 = returnTC (def g (vArg (var f fargs) ∷ gargs))
generateMapRef f fargs g gargs (suc x) = bindTC (generateMapRef f fargs g gargs x)
                                                (λ y → returnTC (lam visible (abs "lx" y)))

generateRefTerm : List Nat → TC (List (Arg Term))
generateRefTerm [] = returnTC []
generateRefTerm (x ∷ xs) = bindTC (generateRefTerm xs)
                                  (λ xs' → returnTC (vArg (var x []) ∷ xs'))

generateRefTerm' : (argInfo : List Bool) → List Nat → TC (List (Arg Term))
generateRefTerm' b [] = returnTC []
generateRefTerm' (b ∷ bs) (x ∷ xs) = bindTC (generateRefTerm' bs xs)
                                            (λ xs' → bindTC (returnTC b) λ
                                                            { true → returnTC (hArg (var x []) ∷ xs') ;
                                                              false → returnTC (vArg (var x []) ∷ xs') })
generateRefTerm' x y = returnTC [] -- Invalid case

generateRefTermHid : List Nat → TC (List (Arg Term))
generateRefTermHid [] = returnTC []
generateRefTermHid (x ∷ xs) = bindTC (generateRefTermHid xs)
                                     (λ xs' → returnTC (hArg (var x []) ∷ xs'))

changeVisToHid : List (Arg Term) → TC (List (Arg Term))
changeVisToHid [] = returnTC []
changeVisToHid (x ∷ xs) = bindTC (changeVisToHid xs)
                                 (λ xs' → bindTC (returnTC x) λ
                                                  { (arg i term) → returnTC (hArg term ∷ xs') })

generateRefTerm1 : List Nat → (List (Arg Term))
generateRefTerm1 [] = []
generateRefTerm1 (x ∷ xs) = (vArg (var x []) ∷ (generateRefTerm1 xs))

map' : ∀ {a b} {A : Set a} {B : Set b} → (A → TC B) → List A → TC (List B)
map' f []       = returnTC []
map' f (x ∷ xs) = bindTC (map' f xs)
                         (λ xs' → bindTC (f x)
                         (λ x' → returnTC (x' ∷ xs')))

{--
null : ∀ {a} {A : Set a} → List A → Bool
null []       = true
null (x ∷ xs) = false
--}

-- replicate : ∀ {a} {A : Set a} → (n : Nat) → A → List A
-- replicate zero    x = []
-- replicate (suc n) x = x ∷ replicate n x

addToList : Nat → List Nat → TC (List Nat)
addToList n [] = returnTC []
addToList n (x ∷ xs) = bindTC (addToList n xs)
                              (λ xs' → returnTC ((x + n) ∷ xs'))

isHidden : (i : ArgInfo) → TC Bool
isHidden (arg-info hidden r) = returnTC true
isHidden (arg-info vis r) = returnTC false

removeHidden : List (Arg Term) → TC (List (Arg Term))
removeHidden [] = returnTC []
removeHidden ((arg i term) ∷ xs) = bindTC (isHidden i) λ
                                          { true → removeHidden xs ;
                                            false → bindTC (removeHidden xs)
                                                           (λ xs' → returnTC ((arg i term) ∷ xs')) }

getArgsCount : Nat → Type → TC Nat
getArgsCount x (pi (arg info t1) (abs s t2)) = bindTC (getArgsCount (suc x) t2)
                                                      (λ c → returnTC c)
getArgsCount x (agda-sort Level) = returnTC x
getArgsCount x y = returnTC x

getDiff : (lt : Nat) → (pars : Nat) → TC Nat
getDiff 0 0 = returnTC 0
getDiff x 0 = returnTC x
getDiff 0 x = returnTC 0
getDiff (suc x) (suc y) = bindTC (getDiff x y)
                                 (λ n → returnTC n)

getIndexValue : Nat → Nat → Type → TC Nat
getIndexValue ref par (pi (arg info t1) (abs s t2)) = bindTC (getIndexValue (suc ref) par t2)
                                                         (λ n → returnTC n)
getIndexValue ref par (agda-sort Level) = bindTC (getDiff ref par)
                                            (λ i → returnTC i)
getIndexValue ref par x = returnTC ref

getIndex' : Name → TC Nat
getIndex' x = bindTC (getType x)
                    (λ t → bindTC (getParameters x)
                    (λ d → bindTC (getIndexValue zero d t)
                    (λ n → returnTC n)))

getIndex : Name → List Nat → TC (List Nat)
getIndex x indLs =
  case null indLs of λ
   { true →
     do t ← getType x
        d ← getParameters x
        cns ← getConstructors x
        lcons ← getLength cns
        n ← getIndexValue zero d t
        pure (replicate lcons n)
   ; false → returnTC indLs
   }

checkName : Name → List Name → TC Bool
checkName ctr [] = returnTC false
checkName ctr (x ∷ xs) =
 if primQNameEquality ctr x
   then pure true
   else checkName ctr xs

getCtrIndex : (ind : Nat) → Name → List Name → TC Nat
getCtrIndex ind ctr [] = returnTC ind -- Invalid case
getCtrIndex ind ctr (x ∷ xs) =
  if primQNameEquality ctr x
    then pure ind
    else getCtrIndex (suc ind) ctr xs

getListElement' : (n : Nat) → List Name → TC Name
getListElement' 0 (x ∷ xs) = returnTC x
getListElement' (suc n) (x ∷ xs) = getListElement' n xs
getListElement' x y = returnTC (quote ⊥) -- Invalid case

rmPars : (d : Nat) → (ty : Type) → TC Type
rmPars 0 ty = returnTC ty
rmPars (suc x) (pi (arg i t1) (abs s t2)) = bindTC (rmPars x t2)
                                                   (λ t2' → returnTC t2')
rmPars (suc x) ty = returnTC unknown

rmHidPars : (ty : Type) → TC Type
rmHidPars (pi (arg (arg-info hidden rel) t1) (abs s t2)) = bindTC (rmHidPars t2)
                                                                  (λ t2' → returnTC t2')
rmHidPars (pi (arg i t1) (abs s t2)) = bindTC (rmHidPars t2)
                                              (λ t2' → returnTC (pi (arg i t1) (abs s t2')))
rmHidPars ty = returnTC ty

getHidPars : (ty : Type) → TC Nat
getHidPars (pi (arg (arg-info hidden rel) t1) (abs s t2)) = bindTC (getHidPars t2)
                                                                   (λ n → returnTC (suc n))
getHidPars (pi (arg i t1) (abs s t2)) = bindTC (getHidPars t2)
                                               (λ n → returnTC n)
getHidPars ty = returnTC 0

getHidArgs : Term → TC (List Bool) -- true for hidden args and false for visible args
getHidArgs (pi (arg i t1) (abs s t2)) = bindTC (getHidArgs t2)
                                               (λ t2' → bindTC (returnTC i) λ
                                                           { (arg-info hidden rel) → returnTC (true ∷ t2') ;
                                                             (arg-info vis rel) → returnTC (false ∷ t2') })
getHidArgs x = returnTC []

getHidArgs' : List ArgInfo → TC (List Bool) -- true for hidden args and false for visible args
getHidArgs' (x ∷ xs) = bindTC (getHidArgs' xs)
                              (λ xs' → bindTC (returnTC x) λ
                                          { (arg-info hidden rel) → returnTC (true ∷ xs') ;
                                            (arg-info vis rel) → returnTC (false ∷ xs') })
getHidArgs' [] = returnTC []

rmIndex : (indLength : Nat) → Type → TC Type
rmIndex 0 t = returnTC t
rmIndex (suc x) (pi (arg info t1) (abs s t2)) = rmIndex x t2
rmIndex x y = returnTC unknown -- Invalid case

changeCodomain' : Type → TC Type
changeCodomain' (def nm x) = returnTC (def nm [])
changeCodomain' (pi (arg info dom) (abs s cdom)) = bindTC (changeCodomain' cdom)
                                                          (λ cdom' → returnTC (pi (arg info dom) (abs s cdom')))
changeCodomain' x = returnTC unknown

{-# TERMINATING #-}
checkIndexRef : (index : Nat) → Type → TC Bool
checkIndexRef index (pi (arg info t1) (abs s t2)) = bindTC (checkIndexRef index t1)
                                                          (λ b1 → bindTC (checkIndexRef (suc index) t2)
                                                          (λ b2 → returnTC (_or_ b1 b2)))
checkIndexRef index (def x lsargs) = bindTC (map' (λ { (arg i term) → bindTC (checkIndexRef index term)
                                                                             (λ b → returnTC b) }) lsargs)
                                           (λ lb → (checkTrue lb))
checkIndexRef index (var ref lsargs) = bindTC (returnTC (eq ref index)) λ
                                        { true → returnTC true ;
                                          false → bindTC (map' (λ { (arg i term) → bindTC (checkIndexRef index term)
                                                                             (λ b → returnTC b) }) lsargs)
                                                                (λ lb → (checkTrue lb)) }
checkIndexRef index (con cn lsargs) = bindTC (map' (λ { (arg i term) → bindTC (checkIndexRef index term)
                                                                             (λ b → returnTC b) }) lsargs)
                                           (λ lb → (checkTrue lb))
checkIndexRef index x = returnTC false

checkIndexRef' : (cns : Type) → (inds : List Nat) → TC (List Bool)
checkIndexRef' cns [] = returnTC []
checkIndexRef' cns (x ∷ xs) = bindTC (checkIndexRef' cns xs)
                                     (λ xs' → bindTC (changeCodomain' cns)
                                     (λ cns' → bindTC (checkIndexRef x cns')
                                     (λ x' → returnTC (x' ∷ xs'))))

getIndexRef' : (index : List Nat) → (indLength : Nat) → Type → TC (List Bool)
getIndexRef' inds 0 x = checkIndexRef' x inds
getIndexRef' inds (suc x) (pi (arg info t1) (abs s t2)) = bindTC (returnTC (map (λ z → z + 1) inds))
                                                                       (λ index' → bindTC (returnTC (index' ∷L 0))
                                                                       (λ index'' → (getIndexRef' index'' x t2)))
getIndexRef' inds (suc x) (def ty args) = returnTC [] -- cases where cons does not encode index in its type (Vec.[])
getIndexRef' inds x y = returnTC []

getIndexRef : Name → Nat → Name → TC (List Bool)
getIndexRef R ind cn = bindTC (getParameters R)
                        (λ d → bindTC (getType cn)
                        (λ x → bindTC (rmPars d x)
                        (λ x' → (getIndexRef' [] ind x'))))

eqBool : Bool → Bool → Bool
eqBool true    true    = true
eqBool false false = true
{-# CATCHALL #-}
eqBool _       _       = false

isMemberBool : Bool → List Bool → TC Bool
isMemberBool b [] = returnTC false
isMemberBool b (x ∷ xs) = bindTC (returnTC (eqBool b x)) λ
                             { true → returnTC true ;
                               false → (isMemberBool b xs) }

countBool : Bool → List Bool → TC Nat
countBool b [] = returnTC 0
countBool b (x ∷ xs) = bindTC (countBool b xs)
                              (λ xs' → bindTC (returnTC (eqBool b x)) λ
                                               { true → returnTC (suc xs') ;
                                                 false → returnTC xs' })

generateIndexRef-a : (inds : List Nat) → (trls : List Nat) → (ref1 : Nat) → (tref2 : Nat) → (iref : List Bool) → TC (List (Arg Term))
generateIndexRef-a inds trls ref1 ref2 (b ∷ bs) = bindTC (returnTC b) λ
                                                          { false → bindTC (isMemberBool false bs) λ
                                                                           { false → bindTC (getListElement ref1 inds)
                                                                                           (λ i1 → returnTC []) ; -- (hArg (var i1 []) ∷ [])) ; -- no recursive calls if remainder args are only true
                                                                             true → bindTC (generateIndexRef-a inds trls (suc ref1) ref2 bs)
                                                                                           (λ bs' → bindTC (getListElement ref1 inds)
                                                                                           (λ i1 → returnTC bs')) } ; -- (hArg (var i1 []) ∷ bs'))) } ;
                                                            true → bindTC (generateIndexRef-a inds trls (suc ref1) (suc ref2) bs)
                                                                          (λ bs' → bindTC (getListElement ref2 trls)
                                                                                          (λ i2 → returnTC (hArg (var i2 []) ∷ bs'))) }
generateIndexRef-a inds trls ref1 ref2 [] = returnTC []

generateIndexRef-b : (trC : Nat) → (argRef : Nat) → (args : List (Arg Term)) → TC Type
generateIndexRef-b 0 argRef args = returnTC (var argRef args)
generateIndexRef-b (suc x) argRef args = bindTC (generateIndexRef-b x argRef args)
                                               (λ ty → returnTC (lam hidden (abs "_" ty)))

generateIndexRef-c : (inds : List Nat) → (iref : List Bool) → (argRef : Nat) → TC Type
generateIndexRef-c inds bs argRef = bindTC (countBool true bs)
                                        (λ trC → bindTC (generateRef trC)
                                        (λ trls → bindTC (returnTC (map (λ z → z + trC) inds))
                                        (λ inds' → bindTC (generateIndexRef-a inds' trls 0 0 bs)
                                        (λ args' → (generateIndexRef-b trC argRef args')))))

generateIndexRef : (inds : List Nat) → (irefs : List (List Bool)) → (args : List Nat) → TC (List (Arg Term))
generateIndexRef inds (ib ∷ ibs) (x ∷ xs) = bindTC (generateIndexRef inds ibs xs)
                                                   (λ xs' → bindTC (isMemberBool false ib) λ
                                                                   { true → bindTC (generateIndexRef-c inds ib x)
                                                                                   (λ ty → returnTC (vArg ty ∷ xs')) ;
                                                                     false → returnTC (vArg (var x []) ∷ xs') } )
generateIndexRef inds [] [] = returnTC []
generateIndexRef inds x y = returnTC []

getRecArgs : (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → TC (List (Arg Term))
getRecArgs args inds irefs = bindTC (dropTC 1 args) -- drop C
                                    (λ args' → bindTC (takeTC 1 args) -- take C
                                    (λ argC → bindTC (generateRefTerm argC)
                                    (λ argC' → bindTC (generateIndexRef inds irefs args')
                                    (λ argsR → returnTC (argC' ++L argsR)))))

generateMapRefRec : (f : Nat) → (fargs : List (Arg Term)) → (g : Name) → (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → Nat → TC Term
generateMapRefRec f fargs g args inds irefs 0 =  bindTC (getRecArgs args inds irefs)
                                                        (λ largs → returnTC (def g (vArg (var f fargs) ∷ largs)))
generateMapRefRec f fargs g args inds irefs (suc x) = bindTC (generateMapRefRec f fargs g args inds irefs x)
                                                             (λ y → returnTC (lam visible (abs "lx" y)))
getIndexRefInfo : (baseTyp : Name) → (indexList : List Nat) → (cons : List Name) → TC (List (List Bool))
getIndexRefInfo baseTyp [] [] = returnTC []
getIndexRefInfo baseTyp (i ∷ is) (x ∷ xs) = bindTC (getIndexRefInfo baseTyp is xs)
                                                   (λ lbs' → bindTC (getIndexRef baseTyp i x)
                                                   (λ lb → returnTC (lb ∷ lbs')))
getIndexRefInfo baseTyp x y = returnTC [] -- Invalid case

checkCdm : Type → Type → TC Bool
checkCdm (def ty1 x) (def ty2 y) = returnTC (primQNameEquality ty1 ty2)
checkCdm x (pi (arg info t1) (abs s t2)) = bindTC (checkCdm x t2) (λ y → returnTC y)
checkCdm x y = returnTC false

changeCodomain : (Cref : Nat) → Type → TC Type
changeCodomain Cref (def nm x) = returnTC (var Cref [])
changeCodomain Cref (pi (arg info dom) (abs s cdom)) = bindTC (changeCodomain (suc Cref) cdom)
                                                              (λ cdom' → returnTC (pi (arg info dom) (abs s cdom')))
changeCodomain Cref x = returnTC unknown


foldl' : {A B : Set} → (B → A → TC B) → B → List A → TC B
foldl' f z [] = returnTC z
foldl' f z (x ∷ xs) = bindTC (f z x)
                        (λ x' → bindTC (foldl' f x' xs)
                        (λ xs' → returnTC xs'))
-- foldl f (f z x) xs

{-
{-# TERMINATING #-}
retExprRef' : (cons : Type) → TC Nat
retExprRef' (def x lsargs) = do ls ← map' (λ { (arg i term) →
                                             do t ← retExprRef' term
                                                pure t }) lsargs
                                b ← isMember 1 ls
                                case b of λ
                                 { true → pure 1
                                 ; false → pure 0
                                 }
retExprRef' (con x lsargs) = do ls ← map' (λ { (arg i term) →
                                             do t ← retExprRef' term
                                                pure t }) lsargs
                                b ← isMember 1 ls
                                case b of λ
                                 { true → pure 1
                                 ; false → pure 0
                                 }
retExprRef' (var ref lsargs) = pure 1
retExprRef' x = pure 0

retExprRef : (indType : Name) → (cons : Type) → TC Nat
retExprRef ind (pi (arg info t1) (abs s t2)) =
  do t2' ← retExprRef ind t2
     pure t2'
retExprRef ind (def x lsargs) =
  case (primQNameEquality ind x) of λ
   { true →
     do cp ← getParameters ind
        lsargs' ← dropTC cp lsargs
        ln ← foldl' (λ {a (arg i term) →
                           do b' ← (retExprRef' term)
                              pure (a + b') }) zero lsargs'
        pure ln
   ; false → pure 0
   }
retExprRef ind x = pure 0


getExprRef : (indType : Name) → (cons : List Name) → TC (List Nat)
getExprRef ind [] = pure []
getExprRef ind (c ∷ cs) =
  do cTy ← getType c
     l ← retExprRef ind cTy
     ls ← getExprRef ind cs
     pure (l ∷ ls)

getExpRef : (indType : Name) → TC (List Nat)
getExpRef ind =
  do lcons ← (getConstructors ind)
     (getExprRef ind lcons)

-}


getBoolList : {A : Set} → List A → TC (List Bool)
getBoolList [] = pure []
getBoolList (x ∷ xs) = do lb ← getBoolList xs
                          pure (false ∷ lb)

setBl : (d : Nat) → List Bool → TC (List Bool)
setBl d [] = pure []
setBl zero (x ∷ xs) = pure (true ∷ xs)
setBl (suc x) (y ∷ ys) = do lb ← setBl x ys
                            pure (y ∷ lb)

countB : List Bool → TC Nat
countB [] = pure 0
countB (x ∷ xs) = do c ← countB xs
                     case x of λ
                      { true → pure (suc c)
                      ; false → pure c
                      }


{-# TERMINATING #-}
retExprRef' : (refLs : List Nat) → List Bool → (cons : Type) → TC (List Bool)
retExprRef' refLs lb (def x lsargs) = do ls ← foldl' (λ { lb' (arg i term) →
                                                               do lb'' ← retExprRef' refLs lb' term
                                                                  pure lb'' }) lb lsargs
                                         pure ls
retExprRef' refLs lb (con x lsargs) = do ls ← foldl' (λ { lb' (arg i term) →
                                                               do lb'' ← retExprRef' refLs lb' term
                                                                  pure lb'' }) lb lsargs
                                         pure ls
retExprRef' refLs lb (var ref lsargs) = do b ← isMember ref refLs
                                           case b of λ
                                            { true →
                                                 do lb' ← reverseTC lb
                                                    lb'' ← setBl ref lb'
                                                    lb''' ← reverseTC lb''
                                                    pure lb'''
                                            ; false → pure lb
                                            }
retExprRef' refLs lb x = pure []

retExprRef : (indType : Name) → (refLs : List Nat) → (cons : Type) → TC Nat
retExprRef ind ref (pi (arg info t1) (abs s t2)) =
    do let ref' = (map (λ z → z + 1) ref)
           ref'' = (ref' ∷L 0)
       t2' ← retExprRef ind ref'' t2
       pure t2'
retExprRef ind ref (def x lsargs) =
    case (primQNameEquality ind x) of λ
     { true →
       do cp ← getParameters ind
          lsargs' ← dropTC cp lsargs
          ref' ← dropTC cp ref
          lb ← getBoolList ref'
          lb' ← foldl' (λ {lb' (arg i term) →
                           do b' ← (retExprRef' ref' lb' term)
                              pure b' }) lb lsargs'
          ln ← countB lb'
          pure ln
     ; false → pure 0
     }
retExprRef ind ref x = pure 0


getExprRef : (indType : Name) → (cons : List Name) → TC (List Nat)
getExprRef ind [] = pure []
getExprRef ind (c ∷ cs) =
    do cTy ← getType c
       l ← retExprRef ind [] cTy
       ls ← getExprRef ind cs
       pure (l ∷ ls)

getExpRef : (indType : Name) → TC (List Nat)
getExpRef ind =
    do lcons ← (getConstructors ind)
       (getExprRef ind lcons)


{-# TERMINATING #-}
printArgs : List (Arg Term) → TC ⊤
printArgs [] = returnTC tt
printArgs (x ∷ xs) = bindTC (returnTC x) λ
                            { (arg info (var x args)) → bindTC (debugPrint "tc.sample.debug" 12 (strErr (showNat x) ∷ []))
                                                         (λ _ → printArgs xs) ;
                              (arg info (def y args')) → bindTC (debugPrint "tc.sample.debug" 12 (strErr "term is ---> " ∷ []))
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (termErr (def y []) ∷ []))
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (strErr "sub start ---> " ∷ []))
                                                         (λ _ → bindTC (printArgs args')
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (strErr "sub end ---> " ∷ []))
                                                         (λ _ → printArgs xs))))) ;
                              (arg info (con y args')) → bindTC (debugPrint "tc.sample.debug" 12 (strErr "constructor is ---> " ∷ []))
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (termErr (con y []) ∷ []))
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (strErr "sub start ---> " ∷ []))
                                                         (λ _ → bindTC (printArgs args')
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (strErr "sub end ---> " ∷ []))
                                                         (λ _ → printArgs xs))))) ;
                              (arg info term) → bindTC (debugPrint "tc.sample.debug" 12 (termErr term ∷ []))
                                                         (λ _ → printArgs xs) }

printList : List Nat → TC ⊤
printList [] = returnTC tt
printList (x ∷ xs) = bindTC (debugPrint "tc.sample.debug" 20 (strErr "printList **" ∷ strErr (showNat x) ∷ []))
                            (λ _ → printList xs)

{-# TERMINATING #-}
updateArgs : (refList : List Nat) → List (Arg Term) → TC (List (Arg Term))
updateArgs refList [] = returnTC []
updateArgs refList (x ∷ xs) =
  do xs' ← updateArgs refList xs
     case x of λ
       { (arg info (var dis args)) →
         do args' ← updateArgs refList args
            refList' ← reverseTC refList
            x' ← getListElement dis refList'
            -- debugPrint "tc.sample.debug" 12 (strErr "Inside updateAgrs" ∷ [])
            -- printList refList'
            -- debugPrint "tc.sample.debug" 12 (strErr (showNat dis) ∷ strErr " and " ∷ strErr (showNat x') ∷ [])
            pure ((arg info (var x' args')) ∷ xs')
       ; (arg info (def y args)) →
         do args' ← updateArgs refList args
            pure ((arg info (def y args')) ∷ xs')
       ; (arg info (con y args)) →
         do args' ← updateArgs refList args
            pure ((arg info (con y args')) ∷ xs')
       ; (arg info term) →
         do -- debugPrint "tc.sample.debug" 12 (strErr "unmatched case" ∷ [])
            pure ((arg info term) ∷ xs')
       }


changeCodomainInd : (Cref : Nat) → (refL : List Nat) → (pars : Nat) → Type → TC Type
changeCodomainInd Cref refL pars (def nm x) =
  do pars' ← generateRef pars
     pars'' ← generateRefTerm pars'
     d ← getParameters nm
     index ← dropTC d x
     -- debugPrint "tc.sample.debug" 12 (strErr "changeCodomainInd 1 -----> " ∷ [])
     -- printArgs x
     index' ← updateArgs refL index
     indexH ← changeVisToHid index
     -- debugPrint "tc.sample.debug" 12 (strErr "changeCodomainInd -----> " ∷ [])
     -- printList refL
     -- debugPrint "tc.sample.debug" 12 (strErr "ListEnd ----" ∷ [])
     -- debugPrint "tc.sample.debug" 12 (termErr (def nm []) ∷ [])
     -- printArgs indexH
     pure (var Cref (indexH ++L (vArg (var pars pars'') ∷ [])))
changeCodomainInd Cref refL pars (pi (arg info dom) (abs s cdom)) =
  do let refL' = map (λ z → z + 1) refL
     cdom' ← changeCodomainInd (suc Cref) refL' (suc pars) cdom
     pure (pi (arg info dom) (abs s cdom'))
changeCodomainInd Cref refL pars x =
  pure unknown

getTypeLn : Nat → Type → TC Nat
getTypeLn ref (pi (arg info t1) (abs s t2)) = bindTC (getTypeLn (suc ref) t2)
                                                     (λ ref' → returnTC ref')
getTypeLn ref (agda-sort Level) = returnTC ref
getTypeLn ref x = returnTC 0

getBaseType : Type → TC Type
getBaseType (pi (arg info t1) (abs s t2)) = getBaseType t2

getBaseType (def x args) = returnTC (def x args)
getBaseType x = returnTC unknown

getConsTypes : List Name → TC (List Type)
getConsTypes [] = returnTC []
getConsTypes (x ∷ xs) =
  do t ← getType x
     xt ← getConsTypes xs
     pure (t ∷ xt)

{--
_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map _ []       = []
map f (x ∷ xs) = f x ∷ map f xs

length : ∀ {a} {A : Set a} → List A → Nat
length []       = 0
length (x ∷ xs) = 1 + length xs
--}
