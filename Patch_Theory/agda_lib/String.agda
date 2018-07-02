
{-# OPTIONS --type-in-type --without-K #-}

open import Data.Bool
open import Patch_Theory.agda_lib.List
open import Patch_Theory.agda_lib.Char

module Patch_Theory.agda_lib.String where

  postulate {- Agda Primitive -}
    String : Set
  {-# BUILTIN STRING  String #-}
  {-# COMPILED_TYPE String String #-}
  

  module String where

    private
      primitive
         primStringToList   : String -> List Char
         primStringFromList : List Char -> String
         primStringAppend   : String -> String -> String
         primStringEquality : String -> String -> Bool
  
  
    equal : String -> String -> Bool
    equal = primStringEquality
  
    toList = primStringToList
    fromList = primStringFromList
  
    string-append = primStringAppend

