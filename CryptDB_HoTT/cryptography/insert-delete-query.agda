{-# OPTIONS --type-in-type --without-K #-}

open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector

module CryptDB_HoTT.cryptography.insert-delete-query where

insert-first : {n : Nat} → (value : Nat) → Vec Int n → Vec Int (suc n)
insert-first value vec = (value :: vec)

insert : {n : Nat} → (value : Nat) → (i : Fin n) → Vec Int n → Vec Int (suc n)
insert value () []
insert value zero (x :: vec) = (value :: (x :: vec))
insert value (suc i) (x :: vec) = x :: insert value i vec

delete : {n : Nat} → (i : Fin (suc n)) → Vec Int (suc n) → Vec Int n
delete {0} zero (x :: []) = []
delete {(suc n)} zero (x :: vec) = vec
delete {0} (suc i) (x :: vec) = vec
delete {(suc n)} (suc i) (x :: vec) = x :: (delete {n} i vec)

