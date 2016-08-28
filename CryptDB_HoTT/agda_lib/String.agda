
{-# OPTIONS --type-in-type --without-K #-}

open import Data.Bool
open import CryptDB_HoTT.agda_lib.List
open import CryptDB_HoTT.agda_lib.Char

module CryptDB_HoTT.agda_lib.String where

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

