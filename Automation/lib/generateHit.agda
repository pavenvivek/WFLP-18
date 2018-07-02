-- {-# OPTIONS --verbose tc.sample.debug:12 #-}
-- {-# OPTIONS --type-in-type #-}

open import Data.List
open import Data.Empty
open import Function hiding (flip)
open import Agda.Builtin.Reflection
open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Automation.utils.reflectionUtils

module Automation.lib.generateHit where

data ArgPath {ℓ₁} : Set (lsuc ℓ₁) where
  argPath : Set ℓ₁ → ArgPath


getHdType : (baseType : Name) → (indType : Name) → (consType : Type) → TC Type
getHdType baseType indType (pi (arg info dom) (abs s cdom)) = do cdom' ← (getHdType baseType indType cdom)
                                                                 dom' ← (getHdType baseType indType dom)
                                                                 pure (pi (arg info dom') (abs s cdom'))
getHdType baseType indType (def ty y) = case (primQNameEquality ty baseType) of λ
                                         { true → pure (def indType y)
                                         ; false → pure (def ty y) }
getHdType baseType indType x = pure unknown 

defineHitCons : Name → Name → List Name → List Name → TC ⊤
defineHitCons base ind (x ∷ xs) (y ∷ ys) = do (defineHitCons base ind xs ys)
                                              ty ← (getType x)
                                              ty' ← (getHdType base ind ty)
                                              (declareDef (vArg y) ty')
                                              (defineFun y (clause [] (con x []) ∷ []))
defineHitCons base ind x y = pure tt

defineHitPathCons : (paths : List Name) → (pathTypes : List Type) → TC ⊤
defineHitPathCons (x ∷ xs) (ty ∷ tys) = do (defineHitPathCons xs tys)
                                           (declarePostulate (vArg x) ty)
defineHitPathCons x ty = pure tt

{-# TERMINATING #-}
changeBaseCtrs : (baseType : Name) → (indType : Name) → (baseCtrs : List Name) → (hindCtrs : List Name) → Term → TC Term
changeBaseCtrs base ind ctrs ictrs (con x args) = case! (checkName x ctrs) of λ
                                                   { true →
                                                       do i ← (getCtrIndex 0 x ctrs)
                                                          ctr' ← (getListElement' i ictrs)
                                                          args' ← (map' (λ { (arg i term) →
                                                                                do term' ← (changeBaseCtrs base ind ctrs ictrs term)
                                                                                   pure (arg i term') })
                                                                         args)
                                                          pure (def ctr' args')
                                                     ; false → pure (con x args) }
changeBaseCtrs base ind ctrs ictrs x = pure x

qualifyPath : (baseType : Name) → (indType : Name) → (baseCtrs : List Name) → (hindCtrs : List Name) → (args : Term) → TC Type
qualifyPath base ind ctrs ictrs (pi (arg info t1) (abs s t2)) = do t2' ← (qualifyPath base ind ctrs ictrs t2)
                                                                   case t1 of λ
                                                                    { (def x args) →
                                                                       case (primQNameEquality x base) of λ
                                                                        { true → pure (pi (arg info (def ind args)) (abs s t2'))
                                                                        ; false → pure (pi (arg info (def x args)) (abs s t2'))
                                                                        }
                                                                    ; term' → pure (pi (arg info term') (abs s t2')) 
                                                                    }
qualifyPath base ind ctrs ictrs (def x args) = case (primQNameEquality x (quote _≡_)) of λ 
                                                { true →
                                                    do args' ← (map' (λ { (arg (arg-info visible relevant) term) →
                                                                             (do term' ← (changeBaseCtrs base ind ctrs ictrs term)
                                                                                 pure (vArg term'))
                                                                           ; argTerm → pure argTerm }) args)
                                                       pure (def x args')
                                                ; false → pure (def x args) }
qualifyPath base ind ctrs ictrs x = pure x

addArgPath : ∀{ℓ₁} → (baseType : Name) → (indType : Name) → (baseCtrs : List Name) → (hindCtrs : List Name) → ArgPath {ℓ₁} → TC Type
addArgPath base ind ctrs ictrs (argPath argType) = do argTyp ← (quoteTC argType)
                                                      qualifyPath base ind ctrs ictrs argTyp

getPathTypes : ∀{ℓ₁} → (baseType : Name) → (indType : Name) → (baseCtrs : List Name) → (hindCtrs : List Name) → List (ArgPath {ℓ₁}) → TC (List Type)
getPathTypes base ind ctrs ictrs [] = pure []
getPathTypes base ind ctrs ictrs (x ∷ xs) = do xs' ← (getPathTypes base ind ctrs ictrs xs)
                                               x' ← (addArgPath base ind ctrs ictrs x)
                                               pure (x' ∷ xs')

defineHindType : (baseType : Name) → (indType : Name) → TC ⊤
defineHindType baseType indType =
  do ty ← (getType baseType)
     (declareDef (vArg indType) ty)
     (defineFun indType (clause [] (def baseType []) ∷ []))

definePointHolder : (pointHolder : Name) → (lcons : List Name) → TC ⊤
definePointHolder pointHolder lcons =
  do LQName ← (quoteTC (List Name))
     (declareDef (vArg pointHolder) LQName)
     lconsQ ← (quoteTC lcons)
     (defineFun pointHolder (clause [] lconsQ ∷ []))

definePathHolder : (pathHolder : Name) → (lpaths : List Name) → TC ⊤
definePathHolder pathHolder lpaths =
  do LQName ← (quoteTC (List Name))
     (declareDef (vArg pathHolder) LQName)
     lpathsQ ← (quoteTC lpaths)
     (defineFun pathHolder (clause [] lpathsQ ∷ []))

data-hit : ∀{ℓ₁} (baseType : Name) → (indType : Name) → (pointHolder : Name) → (lcons : List Name) → (pathHolder : Name) → (lpaths : List Name) →
                  (lpathTypes : (List (ArgPath {ℓ₁}))) → TC ⊤
data-hit baseType indType pointHolder lcons pathHolder lpaths lpathTypes =
  do defineHindType baseType indType
     lcons' ← getConstructors baseType
     defineHitCons baseType indType lcons' lcons
     lpathTypes' ← getPathTypes baseType indType lcons' lcons lpathTypes
     defineHitPathCons lpaths lpathTypes'
     definePointHolder pointHolder lcons
     definePathHolder pathHolder lpaths
