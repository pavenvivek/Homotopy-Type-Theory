{-# OPTIONS --no-termination-check #-}

module CryptDB_HoTT.agda_lib.Integer where

import CryptDB_HoTT.agda_lib.Prelude
import CryptDB_HoTT.agda_lib.Nat as Nat
import Data.Bool

open Nat using (Nat; suc; zero)
         renaming ( _+_  to _+'_
                  ; _*_  to _*'_
                  ; _<_  to _<'_
                  ; _-_  to _-'_
                  ; _==_ to _=='_
                  ; div  to div'
                  ; mod  to mod'
                  ; gcd  to gcd'
                  ; lcm  to lcm'
                  )
open Data.Bool
open CryptDB_HoTT.agda_lib.Prelude

data Int : Set where
  pos : Nat -> Int
  neg : Nat -> Int  -- neg n = -(n + 1)

