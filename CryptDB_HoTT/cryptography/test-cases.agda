{-# OPTIONS --type-in-type --without-K #-}

open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv

open import CryptDB_HoTT.cryptography.Paillier-Cryptosystem
open import CryptDB_HoTT.cryptography.RSA-Cryptosystem
open import CryptDB_HoTT.cryptography.OPE-Cryptosystem
open import CryptDB_HoTT.cryptography.ElGamal-Cryptosystem
open import CryptDB_HoTT.cryptography.insert-delete-query
open import CryptDB_HoTT.cryptography.increment-path
open import CryptDB_HoTT.cryptography.encrypted-increment
open import CryptDB_HoTT.cryptography.cryptDB

module CryptDB_HoTT.cryptography.test-cases where

{-

-- Definitions of the interpreters

interp#1 : {a b : cryptR} → (p : a ≡ b) → (I-cryptR a) ≃ (I-cryptR b)
interp#1 p = coe-biject (ap I-cryptR p) 

interp#2 : {a b : cryptR} → (p : a ≡ b) → (I-cryptR a) → (I-cryptR b)
interp#2 p = coe' (ap I-cryptR p) 

interp#3 : {a b : cryptR} → {p q : a ≡ b} → (x : p ≡ q) → (I-cryptR a ≡ I-cryptR b) ≃ (I-cryptR a ≡ I-cryptR b)
interp#3 {a} {b} {p} {q} x = coe-biject (apI-path I-cryptR x)

interp#4 : {a b : cryptR} → {p q : a ≡ b} → (x : p ≡ q) → (I-cryptR a ≡ I-cryptR b) → (I-cryptR a ≡ I-cryptR b)
interp#4 x = coe' (apI-path I-cryptR x)

-}

{-- test cases --}

test0-a : Records 2 2
test0-a = (INSERT 200 at zero :: (INSERT-FIRST 100 :: []R))

test0-b : Records 3 1
test0-b = (DELETE zero :: (INSERT 200 at zero :: (INSERT-FIRST 100 :: []R)))

test1-a : Singleton (2868 :: [])
test1-a = to-Singleton (rsa-encrypt 61 53) (inspect (123 :: []))

test1-b : Singleton (123 :: [])
test1-b = to-Singleton (rsa-decrypt 61 53) (inspect (2868 :: []))

test2-a : Singleton (15958 :: [])
test2-a = to-Singleton (paillier-encrypt 13 11) (inspect (123 :: []))

test2-b : Singleton (123 :: [])
test2-b = to-Singleton (paillier-decrypt 13 11) (inspect (15958 :: []))

test3-a : Singleton (41981 :: [])
test3-a = to-Singleton (paillier-encrypt 19 17) (inspect (240 :: []))

test3-b : Singleton (240 :: [])
test3-b = to-Singleton (paillier-decrypt 19 17) (inspect (41981 :: []))

test4-a : Singleton (1058 :: [])
test4-a = to-Singleton (ope-encrypt) (inspect (45 :: []))

test4-b : Singleton (45 :: [])
test4-b = to-Singleton (ope-decrypt) (inspect (1058 :: []))

test5-a : Singleton (((4 , 8) , 69029) :: [])
test5-a = to-Singleton (ElGamal-encrypt 13) (inspect (371 :: []))

test5-b : Singleton (371 :: [])
test5-b = to-Singleton (ElGamal-decrypt 13) (inspect (((4 , 8) , 69029) :: []))

test6-a : Singleton (100 :: [])
test6-a = to-Singleton (insert-first 100) (inspect [])

test6-b : Singleton []
test6-b = to-Singleton (delete zero) (inspect (100 :: []))

test7-a : Singleton (200 :: (100 :: []))
test7-a = to-Singleton (insert 200 zero) (inspect (100 :: []))

test7-b : Singleton (100 :: [])
test7-b = to-Singleton (delete zero) (inspect (200 :: (100 :: [])))

test8 : Singleton (110 :: (20 :: (30 :: [])))
test8 = to-Singleton (increment-100 zero) (inspect (10 :: (20 :: (30 :: []))))

test9 : Singleton (110 :: (20 :: (30 :: [])))
test9 = to-Singleton (paillier-decrypt 13 11)
                     (to-Singleton (crypt-increment-100 13 11 zero)
                                   (to-Singleton (paillier-encrypt 13 11) (inspect (10 :: (20 :: (30 :: []))))))

test10 : Singleton (123 :: (337 :: (348 :: [])))
test10 = to-Singleton (paillier-decrypt 23 19)
                      (to-Singleton (crypt-increment-100 23 19 (suc zero))
                                    (to-Singleton (paillier-encrypt 23 19) (inspect (123 :: (237 :: (348 :: []))))))

{-- test cases for the interpreters --}

test11 : Singleton (execute (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R)))
test11 = interp#2 (rsa-enc 61 53 (INSERT-FIRST 123 :: []R)) (inspect (123 :: []))

test12 : Singleton (execute (RSA-DECRYPT 61 , 53 :: (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R))))
test12 = interp#2 (rsa-dec 61 53 (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R))) (inspect (2868 :: []))

test13 : Singleton (execute (PAILLIER-ENCRYPT 13 , 17 :: (INSERT-FIRST 99 :: []R)))
test13 = interp#2 (paillier-enc 13 17 (INSERT-FIRST 99 :: []R)) (inspect (99 :: []))

test14 : Singleton (execute (INSERT-FIRST 99 :: []R))
test14 = interp#2 (paillier-dec 13 17 (PAILLIER-ENCRYPT 13 , 17 :: (INSERT-FIRST 99 :: []R))) (inspect (execute (PAILLIER-ENCRYPT 13 , 17 :: (INSERT-FIRST 99 :: []R))))

test15 : Singleton (execute (OPE-ENCRYPT:: (INSERT-FIRST 267 :: []R)))
test15 = interp#2 (ope-enc (INSERT-FIRST 267 :: []R)) (inspect (267 :: []))

test16 : Singleton (execute (INSERT-FIRST 267 :: []R))
test16 = interp#2 (ope-dec (OPE-ENCRYPT:: (INSERT-FIRST 267 :: []R))) (inspect (execute (OPE-ENCRYPT:: (INSERT-FIRST 267 :: []R))))

test17 : Singleton (execute (ELGAMAL-ENCRYPT 17 :: (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R))))
test17 = interp#2 (elgamalrsa-enc 17 (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R))) (inspect (execute (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R))))

test18 : Singleton (execute (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R)))
test18 = interp#2 (elgamalrsa-dec 17 (ELGAMAL-ENCRYPT 17 :: (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R))))
                  (inspect (execute (ELGAMAL-ENCRYPT 17 :: (RSA-ENCRYPT 61 , 53 :: (INSERT-FIRST 123 :: []R)))))

test19 : Singleton (execute (ELGAMAL-ENCRYPT 13 :: (OPE-ENCRYPT:: (INSERT-FIRST 23 :: []R))))
test19 = interp#2 (elgamalope-enc 13 (OPE-ENCRYPT:: (INSERT-FIRST 23 :: []R))) (inspect (execute (OPE-ENCRYPT:: (INSERT-FIRST 23 :: []R))))

test20 : Singleton (execute (OPE-ENCRYPT:: (INSERT-FIRST 23 :: []R)))
test20 = interp#2 (elgamalope-dec 13 (ELGAMAL-ENCRYPT 13 :: (OPE-ENCRYPT:: (INSERT-FIRST 23 :: []R)))) (inspect (execute (ELGAMAL-ENCRYPT 13 :: (OPE-ENCRYPT:: (INSERT-FIRST 23 :: []R)))))

{-- test cases for paillier homomorphism homotopy --}

test21-hom : Singleton (execute (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))) ≡
             Singleton (execute (INCREMENT100 zero :: (ID-R:: (ID-R:: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))))
test21-hom = interp#4 (paillier-homotopy 13 11 zero (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R))))
                      (ap I-cryptR
                          ((paillier-enc 13 11 (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))) ∘
                          (crypt-increment-by-100 13 11 zero (PAILLIER-ENCRYPT 13 , 11 :: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R))))) ∘
                          (paillier-dec 13 11 (CRYPT-INCREMENT100 13 , 11 , zero :: (PAILLIER-ENCRYPT 13 , 11 :: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R))))))))

postulate
  test21-hom* : test21-hom ≡ (ap I-cryptR
                                 ((id-cryptR (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))) ∘
                                 (id-cryptR (ID-R:: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R))))) ∘
                                 (increment-by-100 zero (ID-R:: (ID-R:: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))))) 

test22-hom : Singleton (execute (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))) ≡
             Singleton (execute (PAILLIER-DECRYPT 13 , 11 :: (CRYPT-INCREMENT100 13 , 11 , zero :: (PAILLIER-ENCRYPT 13 , 11 :: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))))
test22-hom = interp#4 (! (paillier-homotopy 13 11 zero (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))
                      (ap I-cryptR
                          ((id-cryptR (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))) ∘
                          (id-cryptR (ID-R:: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R))))) ∘
                          (increment-by-100 zero (ID-R:: (ID-R:: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))))) 

postulate
  test22-hom* : test22-hom ≡ (ap I-cryptR
                                  ((paillier-enc 13 11 (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))) ∘
                                  (crypt-increment-by-100 13 11 zero (PAILLIER-ENCRYPT 13 , 11 :: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R))))) ∘
                                  (paillier-dec 13 11 (CRYPT-INCREMENT100 13 , 11 , zero :: (PAILLIER-ENCRYPT 13 , 11 :: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R))))))))

test23-hom : Singleton (execute (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))) →
             Singleton (execute (INCREMENT100 zero :: (ID-R:: (ID-R:: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))))
test23-hom = coe' test21-hom

test24-hom : Singleton (execute (INCREMENT100 zero :: (ID-R:: (ID-R:: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))))
test24-hom = test23-hom (inspect (10 :: (20 :: (30 :: []))))

test25-hom : Singleton (110 :: (20 :: (30 :: [])))
test25-hom = test23-hom (inspect (10 :: (20 :: (30 :: []))))

test26-hom : Singleton (execute (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))) →
             Singleton (execute (PAILLIER-DECRYPT 13 , 11 :: (CRYPT-INCREMENT100 13 , 11 , zero :: (PAILLIER-ENCRYPT 13 , 11 :: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))))
test26-hom = coe' test22-hom

test27-hom : Singleton (execute (PAILLIER-DECRYPT 13 , 11 :: (CRYPT-INCREMENT100 13 , 11 , zero :: (PAILLIER-ENCRYPT 13 , 11 :: (INSERT-FIRST 10 :: (INSERT-FIRST 20 :: (INSERT-FIRST 30 :: []R)))))))
test27-hom = test26-hom (inspect (10 :: (20 :: (30 :: []))))

test28-hom : Singleton (110 :: (20 :: (30 :: [])))
test28-hom = test26-hom (inspect (10 :: (20 :: (30 :: []))))
