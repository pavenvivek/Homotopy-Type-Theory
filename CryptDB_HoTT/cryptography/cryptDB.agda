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

module CryptDB_HoTT.cryptography.cryptDB where

{-- Records : Higher inductive type which stores the instances of all the queries executed --}

private
  data #Records : Nat → Nat → Set where
    #[]R : #Records 0 0
    #ID-R:: : {m n : Nat} → #Records n m → #Records (suc n) m
    #INSERT-FIRST_::_ : {m n : Nat} → (value : Int) → #Records n m → #Records (suc n) (suc m)
    #INSERT_at_::_ : {m n : Nat} → (value : Int) → (i : Fin m) → #Records n m → #Records (suc n) (suc m)
    #DELETE_::_ : {m n : Nat} → (i : Fin (suc m)) → #Records n (suc m) → #Records (suc n) m
    #RSA-ENCRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → #Records n m → #Records (suc n) m
    #RSA-DECRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → #Records n m → #Records (suc n) m
    #PAILLIER-ENCRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → #Records n m → #Records (suc n) m
    #PAILLIER-DECRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → #Records n m → #Records (suc n) m
    #OPE-ENCRYPT::_ : {m n : Nat} → #Records n m → #Records (suc n) m
    #OPE-DECRYPT::_ : {m n : Nat} → #Records n m → #Records (suc n) m
    #ELGAMAL-ENCRYPT_::_ : {m n : Nat} → (p : Nat) → #Records n m → #Records (suc n) m
    #ELGAMAL-DECRYPT_::_ : {m n : Nat} → (p : Nat) → #Records n m → #Records (suc n) m
    #INCREMENT100_::_ : {m n : Nat} → (i : Fin m) → #Records n m → #Records (suc n) m
    #CRYPT-INCREMENT100_,_,_::_ : {m n : Nat} → (p q : Nat) → (i : Fin m) → #Records n m → #Records (suc n) m

  {-- Record representing Paillier homomorphic property --}
  
  postulate
    #PAILLIER-HOMOMORPHISM_,_,_::_ : {m n : Nat} → (p q : Nat) → (i : Fin m) → (r : #Records n m) →
                                     (#PAILLIER-DECRYPT p , q :: (#CRYPT-INCREMENT100 p , q , i :: (#PAILLIER-ENCRYPT p , q :: r))) ≡ (#INCREMENT100 i :: (#ID-R:: (#ID-R:: r)))


Records : Nat → Nat → Set
Records = #Records

{-- Empty Record --}
[]R : Records 0 0
[]R = #[]R

{-- Record for indentity function --}
ID-R:: : {m n : Nat} → #Records n m → #Records (suc n) m
ID-R:: = #ID-R::

{-- Record for insert-first query --}
INSERT-FIRST_::_ : {m n : Nat} → (value : Int) → Records n m → Records (suc n) (suc m)
INSERT-FIRST_::_ = #INSERT-FIRST_::_

{-- Record for insert query --}
INSERT_at_::_ : {m n : Nat} → (value : Int) → (i : Fin m) → Records n m → Records (suc n) (suc m)
INSERT_at_::_ = #INSERT_at_::_

{-- Record for delete query --}
DELETE_::_ : {m n : Nat} → (i : Fin (suc m)) → Records n (suc m) → Records (suc n) m
DELETE_::_ = #DELETE_::_

{-- Record for RSA encryption function --}
RSA-ENCRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → Records n m → Records (suc n) m
RSA-ENCRYPT_,_::_ = #RSA-ENCRYPT_,_::_

{-- Record for RSA decryption function --}
RSA-DECRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → Records n m → Records (suc n) m
RSA-DECRYPT_,_::_ = #RSA-DECRYPT_,_::_

{-- Record for Paillier encryption function --}
PAILLIER-ENCRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → Records n m → Records (suc n) m
PAILLIER-ENCRYPT_,_::_ = #PAILLIER-ENCRYPT_,_::_

{-- Record for Paillier decryption function --}
PAILLIER-DECRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → Records n m → Records (suc n) m
PAILLIER-DECRYPT_,_::_ = #PAILLIER-DECRYPT_,_::_

{-- Record for Order Preserving encryption function --}
OPE-ENCRYPT::_ : {m n : Nat} → Records n m → Records (suc n) m
OPE-ENCRYPT::_ = #OPE-ENCRYPT::_

{-- Record for OPE decryption function --}
OPE-DECRYPT::_ : {m n : Nat} → Records n m → Records (suc n) m
OPE-DECRYPT::_ = #OPE-DECRYPT::_

{-- Record for ElGamal encryption function --}
ELGAMAL-ENCRYPT_::_ : {m n : Nat} → (p : Nat) → Records n m → Records (suc n) m
ELGAMAL-ENCRYPT_::_ = #ELGAMAL-ENCRYPT_::_

{-- Record for ElGamal decryption function --}
ELGAMAL-DECRYPT_::_ : {m n : Nat} → (p : Nat) → Records n m → Records (suc n) m
ELGAMAL-DECRYPT_::_ = #ELGAMAL-DECRYPT_::_

{-- Record for increment function --}
INCREMENT100_::_ : {m n : Nat} → (i : Fin m) → #Records n m → #Records (suc n) m
INCREMENT100_::_ = #INCREMENT100_::_

{-- Record for encrypted increment function --}
CRYPT-INCREMENT100_,_,_::_ : {m n : Nat} → (p q : Nat) → (i : Fin m) → #Records n m → #Records (suc n) m
CRYPT-INCREMENT100_,_,_::_ = #CRYPT-INCREMENT100_,_,_::_

{-- Record for Paillier homomorphism --}
PAILLIER-HOMOMORPHISM_,_,_::_ : {m n : Nat} → (p q : Nat) → (i : Fin m) → (r : Records n m) →
                                     (PAILLIER-DECRYPT p , q :: (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))) ≡ (INCREMENT100 i :: (ID-R:: (ID-R:: r)))
PAILLIER-HOMOMORPHISM_,_,_::_ = #PAILLIER-HOMOMORPHISM_,_,_::_


{-- execute : Invokes the functions corresponding to the query instances in the given record --}

execute : {m n : Nat} → Records n m → Vec Int m
execute #[]R = []
execute (#ID-R:: r) = id (execute r)
execute (#INSERT-FIRST val :: r) = insert-first val (execute r)
execute (#INSERT val at i :: r) = insert val i (execute r)
execute (#DELETE i :: r) = delete i (execute r)
execute (#RSA-ENCRYPT p , q :: r) = rsa-encrypt p q (execute r)
execute (#RSA-DECRYPT p , q :: r) = rsa-decrypt p q (execute r)
execute (#PAILLIER-ENCRYPT p , q :: r) = paillier-encrypt p q (execute r)
execute (#PAILLIER-DECRYPT p , q :: r) = paillier-decrypt p q (execute r)
execute (#OPE-ENCRYPT:: r) = ope-encrypt (execute r)
execute (#OPE-DECRYPT:: r) = ope-decrypt (execute r)
execute (#ELGAMAL-ENCRYPT p :: r) = ElGamal-encrypt2 p (ElGamal-encrypt p (execute r))
execute (#ELGAMAL-DECRYPT p :: r) = ElGamal-decrypt p (ElGamal-decrypt2 p (execute r))
execute (#INCREMENT100 i :: r) = increment-100 i (execute r)
execute (#CRYPT-INCREMENT100 p , q , i :: r) = crypt-increment-100 p q i (execute r)

{-- cryptR : Higher inductive type representing the database tables as points and encryption, decryption functions and queries as paths --}

private
  data #cryptR : Set where
    #ctab_ : {m n : Nat} → Records n m → #cryptR
    #ctabRSA_ : {m n : Nat} → Records n m → #cryptR
    #ctabPL_ : {m n : Nat} → Records n m → #cryptR
    #ctabOPE_ : {m n : Nat} → Records n m → #cryptR
    #ctabEG_ : {m n : Nat} → Records n m → #cryptR


cryptR : Set
cryptR = #cryptR

{-- ctab : Represents plain tables --}
ctab_ : {m n : Nat} → Records n m → cryptR
ctab_ = #ctab_

{-- ctabRSA : Represents RSA encrypted tables --}
ctabRSA_ : {m n : Nat} → Records n m → cryptR
ctabRSA_ = #ctabRSA_

{-- ctabPL : Represents Paillier encrypted tables --}
ctabPL_ : {m n : Nat} → Records n m → cryptR
ctabPL_ = #ctabPL_

{-- ctabOPE : Represents OPE encrypted tables --}
ctabOPE_ : {m n : Nat} → Records n m → cryptR
ctabOPE_ = #ctabOPE_

{-- ctabEG : Represents ElGamal encrypted tables --}
ctabEG_ : {m n : Nat} → Records n m → cryptR
ctabEG_ = #ctabEG_


postulate
  {-- Path representing insert first query --}
  insert-first-query : {m n : Nat} → (value : Int) → (r : Records n m) → (ctab r) ≡ (ctab (INSERT-FIRST value :: r))

  {-- Path representing insert query --}
  insert-query : {m n : Nat} → (value : Int) → (i : Fin m) → (r : Records n m) → (ctab r) ≡ (ctab (INSERT value at i :: r))

  {-- Path representing delete query --}
  delete-query : {m n : Nat} → (i : Fin (suc m)) → (r : Records n (suc m)) → (ctab r) ≡ (ctab (DELETE i :: r))
  
  {-- Path representing RSA encryption function : from plain table (ctab) to rsa encrypted table (ctabRSA) --}
  rsa-enc : {m n : Nat} → (p : Nat) → (q : Nat) → (r : Records n m) → (ctab r) ≡ (ctabRSA (RSA-ENCRYPT p , q :: r))

  {-- Path representing RSA decryption function : from rsa encrypted table (ctabRSA) to plain table (ctab) --}
  rsa-dec : {m n : Nat} → (p : Nat) → (q : Nat) → (r : Records n m) → (ctabRSA r) ≡ (ctab (RSA-DECRYPT p , q :: r))

  {-- Path representing Paillier encryption function : from plain table (ctab) to paillier encrypted table (ctabPL) --}
  paillier-enc : {m n : Nat} → (p : Nat) → (q : Nat) → (r : Records n m) → (ctab r) ≡ (ctabPL (PAILLIER-ENCRYPT p , q :: r))

  {-- Path representing Paillier decryption function : from paillier encrypted table (ctabPL) to plain table (ctab) --}
  paillier-dec : {m n : Nat} → (p : Nat) → (q : Nat) → (r : Records n m) → (ctabPL r) ≡ (ctab (PAILLIER-DECRYPT p , q :: r))

  {-- Path representing OPE encryption function : from plain table (ctab) to OPE encrypted table (ctabOPE) --}
  ope-enc : {m n : Nat} → (r : Records n m) → (ctab r) ≡ (ctabOPE (OPE-ENCRYPT:: r))

  {-- Path representing OPE decryption function : from OPE encrypted table (ctabOPE) to plain table (ctab) --}
  ope-dec : {m n : Nat} → (r : Records n m) → (ctabPL r) ≡ (ctab (OPE-DECRYPT:: r))

  {-- Path representing ElGamal encryption function : from rsa encrypted table (ctabRSA) to ElGamal encrypted table (ctabEG) --}
  elgamalrsa-enc : {m n : Nat} → (p : Nat) → (r : Records n m) → (ctabRSA r) ≡ (ctabEG (ELGAMAL-ENCRYPT p :: r))

  {-- Path representing ElGamal decryption function : from ElGamal encrypted table (ctabEG) to rsa encrypted table (ctabRSA) --}
  elgamalrsa-dec : {m n : Nat} → (p : Nat) → (r : Records n m) → (ctabEG r) ≡ (ctabRSA (ELGAMAL-DECRYPT p :: r))
  
  {-- Path representing ElGamal encryption function : from ope encrypted table (ctabOPE) to ElGamal encrypted table (ctabEG) --}
  elgamalope-enc : {m n : Nat} → (p : Nat) → (r : Records n m) → (ctabOPE r) ≡ (ctabEG (ELGAMAL-ENCRYPT p :: r))

  {-- Path representing ElGamal decryption function : from ElGamal encrypted table (ctabEG) to ope encrypted table (ctabOPE) --}
  elgamalope-dec : {m n : Nat} → (p : Nat) → (r : Records n m) → (ctabEG r) ≡ (ctabOPE (ELGAMAL-DECRYPT p :: r))

  {-- Path representing increment function : it increments the value at given location by 100 --}
  increment-by-100 : {m n : Nat} → (i : Fin m) → (r : Records n m) → (ctab r) ≡ (ctab (INCREMENT100 i :: r))

  {-- Path representing encrypted increment function : it multiplies the encrypted value at the given location by the encrypted value of 100 --}
  crypt-increment-by-100 : {m n : Nat} → (p q : Nat) → (i : Fin m) → (r : Records n m) → (ctabPL r) ≡ (ctabPL (CRYPT-INCREMENT100 p , q , i :: r))

  {-- Path representing identity function --}
  id-cryptR : {m n : Nat} → (r : Records n m) → (ctab r) ≡ (ctab (ID-R:: r))

  {-- Path representing the homotopy of Paillier homomorphic property --}  
  paillier-homotopy : {m n : Nat} → (p q : Nat) (i : Fin m) → (r : Records n m) →
                      transport (λ x → ctab r ≡ ctab x) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                ((paillier-enc p q r) ∘
                                 (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                      ≡ (id-cryptR r) ∘ (id-cryptR (ID-R:: r)) ∘ (increment-by-100 i (ID-R:: (ID-R:: r)))
                    

{-- rec-cryptR : Recursion principle for cryptR mapping out the points in cryptR --}

rec-cryptR : {n : Nat} → {C : Set} →
             (c1 c2 c3 c4 c5 : C) →
             (c-insert-first : c1 ≡ c1) →
             (c-insert : c1 ≡ c1) →
             (c-delete : c1 ≡ c1) →
             (c-rsa-crypto : c1 ≡ c2) →
             (c-paillier-crypto : c1 ≡ c3) →
             (c-ope-crypto : c1 ≡ c4) →
             (c-elgamal-rsa-crypto : c2 ≡ c5) →
             (c-elgamal-ope-crypto : c4 ≡ c5) →
             (c-increment100 : c1 ≡ c1) →
             (c-crypt-increment100 : c3 ≡ c3) →
             (c-paillier-homotopy : (c1 ≡ c1) ≡ (c1 ≡ c1)) →
             cryptR → C
rec-cryptR c1 c2 c3 c4 c5 c-insert-first c-insert c-delete c-rsa-crypto c-paillier-crypto c-ope-crypto
           c-elgamal-rsa-crypto c-elgamal-ope-crypto c-increment100 c-crypt-increment100 c-paillier-homotopy (#ctab r) = c1
rec-cryptR c1 c2 c3 c4 c5 c-insert-first c-insert c-delete c-rsa-crypto c-paillier-crypto c-ope-crypto
           c-elgamal-rsa-crypto c-elgamal-ope-crypto c-increment100 c-crypt-increment100 c-paillier-homotopy (#ctabRSA r) = c2
rec-cryptR c1 c2 c3 c4 c5 c-insert-first c-insert c-delete c-rsa-crypto c-paillier-crypto c-ope-crypto
           c-elgamal-rsa-crypto c-elgamal-ope-crypto c-increment100 c-crypt-increment100 c-paillier-homotopy (#ctabPL r) = c3
rec-cryptR c1 c2 c3 c4 c5 c-insert-first c-insert c-delete c-rsa-crypto c-paillier-crypto c-ope-crypto
           c-elgamal-rsa-crypto c-elgamal-ope-crypto c-increment100 c-crypt-increment100 c-paillier-homotopy (#ctabOPE r) = c4
rec-cryptR c1 c2 c3 c4 c5 c-insert-first c-insert c-delete c-rsa-crypto c-paillier-crypto c-ope-crypto
           c-elgamal-rsa-crypto c-elgamal-ope-crypto c-increment100 c-crypt-increment100 c-paillier-homotopy (#ctabEG r) = c5

{-- βrec-cryptR : Recursion principle for cryptR mapping out the paths (rsa-enc for instance) in cryptR --}

postulate
  βrec-cryptR-rsa : {m n p q : Nat} → {r : Records n m} → {C : Set} →
                    (c1 c2 c3 c4 c5 : C) →
                    (c-insert-first : c1 ≡ c1) →
                    (c-insert : c1 ≡ c1) →
                    (c-delete : c1 ≡ c1) →
                    (c-rsa-crypto : c1 ≡ c2) →
                    (c-paillier-crypto : c1 ≡ c3) →
                    (c-ope-crypto : c1 ≡ c4) →
                    (c-elgamal-rsa-crypto : c2 ≡ c5) →
                    (c-elgamal-ope-crypto : c4 ≡ c5) →
                    (c-increment100 : c1 ≡ c1) →
                    (c-crypt-increment100 : c3 ≡ c3) →
                    (c-paillier-homotopy : (c1 ≡ c1) ≡ (c1 ≡ c1)) →
                    ap (rec-cryptR {n} c1 c2 c3 c4 c5
                                   c-insert-first
                                   c-insert
                                   c-delete
                                   c-rsa-crypto
                                   c-paillier-crypto
                                   c-ope-crypto
                                   c-elgamal-rsa-crypto
                                   c-elgamal-ope-crypto
                                   c-increment100
                                   c-crypt-increment100
                                   c-paillier-homotopy)
                       (rsa-enc p q r) ≡ c-rsa-crypto

  {-- !βrec-cryptR : Recursion principle for cryptR mapping out the inverse paths in cryptR --}

  !βrec-cryptR-rsa : {m n p q : Nat} → {r : Records n m} → {C : Set} →
                     (c1 c2 c3 c4 c5 : C) →
                     (c-insert-first : c1 ≡ c1) →
                     (c-insert : c1 ≡ c1) →
                     (c-delete : c1 ≡ c1) →
                     (c-rsa-crypto : c2 ≡ c1) →
                     (c-paillier-crypto : c3 ≡ c1) →
                     (c-ope-crypto : c4 ≡ c1) →
                     (c-elgamal-rsa-crypto : c5 ≡ c2) →
                     (c-elgamal-ope-crypto : c5 ≡ c4) →
                     (c-increment100 : c1 ≡ c1) →
                     (c-crypt-increment100 : c3 ≡ c3) →
                     (c-paillier-homotopy : (c1 ≡ c1) ≡ (c1 ≡ c1)) →
                     ap (rec-cryptR {n} c1 c2 c3 c4 c5
                                    (! c-insert-first)
                                    (! c-insert)
                                    (! c-delete)
                                    (! c-rsa-crypto)
                                    (! c-paillier-crypto)
                                    (! c-ope-crypto)
                                    (! c-elgamal-rsa-crypto)
                                    (! c-elgamal-ope-crypto)
                                    (! c-increment100)
                                    (! c-crypt-increment100)
                                    (! c-paillier-homotopy))
                        (rsa-dec p q r) ≡ c-rsa-crypto


{-- I-cryptR : Interprets the points in cryptR as Singleton types in the Universe --}

I-cryptR : cryptR → Set
I-cryptR (#ctab r) = Singleton (execute r)
I-cryptR (#ctabRSA r) = Singleton (execute r)
I-cryptR (#ctabPL r) = Singleton (execute r)
I-cryptR (#ctabOPE r) = Singleton (execute r)
I-cryptR (#ctabEG r) = Singleton (execute r)

postulate

  {-- I-cryptR-insert-first-path : Interprets the insert-first-query path in cryptR as a path in the Universe given by insert-first function --}
  I-cryptR-insert-first-path : {m n : Nat} → (value : Int) → (r : Records n m) →
                               ap I-cryptR (insert-first-query value r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int (suc m)} {(insert-first value)} (to-Singleton (insert-first value)))

  {-- I-cryptR-insert-path : Interprets the insert-query path in cryptR as a path in the Universe given by insert function --}
  I-cryptR-insert-path : {m n : Nat} → (value : Int) → (i : Fin m) → (r : Records n m) →
                         ap I-cryptR (insert-query value i r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int (suc m)} {(insert value i)} (to-Singleton (insert value i)))

  {-- I-cryptR-delete-path : Interprets the delete-query path in cryptR as a path in the Universe given by delete function --}
  I-cryptR-delete-path : {m n : Nat} → (i : Fin (suc m)) → (r : Records n (suc m)) →
                         ap I-cryptR (delete-query i r) ≡ ua (singleton-equiv {Vec Int (suc m)} {Vec Int m} {(delete i)} (to-Singleton (delete i)))

  {-- I-cryptR-rsa-path : Interprets the rsa-enc path in cryptR as a path in the Universe given by rsa-encrypt function --}
  I-cryptR-rsa-path : {m n : Nat} → (p q : Nat) → (r : Records n m) →
                      ap I-cryptR (rsa-enc p q r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q)))
                      
  {-- I-cryptR-rsa-path-inv : Interprets the rsa-dec path in cryptR as a path in the Universe given by rsa-decrypt function --}
  I-cryptR-rsa-path-inv : {m n : Nat} → (p q : Nat) → (r : Records n m) →
                          ap I-cryptR (rsa-dec p q r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q)))
                          
  {-- I-cryptR-paillier-path : Interprets the paillier-enc path in cryptR as a path in the Universe given by paillier-encrypt function --}
  I-cryptR-paillier-path : {m n : Nat} → (p q : Nat) → (r : Records n m) →
                           ap I-cryptR (paillier-enc p q r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))

  {-- I-cryptR-paillier-path-inv : Interprets the paillier-dec path in cryptR as a path in the Universe given by paillier-decrypt function --}
  I-cryptR-paillier-path-inv : {m n : Nat} → (p q : Nat) → (r : Records n m) →
                               ap I-cryptR (paillier-dec p q r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))

  {-- I-cryptR-ope-path : Interprets the ope-enc path in cryptR as a path in the Universe given by ope-encrypt function --}
  I-cryptR-ope-path : {m n : Nat} → (r : Records n m) →
                      ap I-cryptR (ope-enc r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {ope-encrypt} (to-Singleton ope-encrypt))

  {-- I-cryptR-ope-path-inv : Interprets the ope-dec path in cryptR as a path in the Universe given by ope-decrypt function --}
  I-cryptR-ope-path-inv : {m n : Nat} → (r : Records n m) →
                          ap I-cryptR (ope-dec r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {ope-decrypt} (to-Singleton ope-decrypt))

  {-- I-cryptR-elgamalrsa-path : Interprets the elgamalrsa-enc path in cryptR as a path in the Universe given by ElGamal-encrypt function --}
  I-cryptR-elgamalrsa-path : {m n : Nat} → (p : Nat) → (r : Records n m) →
                             ap I-cryptR (elgamalrsa-enc p r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p))))

  {-- I-cryptR-elgamalrsa-path-inv : Interprets the elgamalrsa-dec path in cryptR as a path in the Universe given by ElGamal-decrypt function --}
  I-cryptR-elgamalrsa-path-inv : {m n : Nat} → (p : Nat) → (r : Records n m) →
                                 ap I-cryptR (elgamalrsa-dec p r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p))))

  {-- I-cryptR-elgamalope-path : Interprets the elgamalope-enc path in cryptR as a path in the Universe given by ElGamal-encrypt function --}
  I-cryptR-elgamalope-path : {m n : Nat} → (p : Nat) → (r : Records n m) →
                             ap I-cryptR (elgamalope-enc p r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p))))

  {-- I-cryptR-elgamalope-path-inv : Interprets the elgamalope-dec path in cryptR as a path in the Universe given by ElGamal-decrypt function --}
  I-cryptR-elgamalope-path-inv : {m n : Nat} → (p : Nat) → (r : Records n m) →
                                 ap I-cryptR (elgamalope-dec p r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p))))

  {-- I-cryptR-increment100-path : Interprets the increment-by-100 path in cryptR as a path in the Universe given by increment-100 function --}
  I-cryptR-increment100-path : {m n : Nat} → (i : Fin m) → (r : Records n m) →
                               ap I-cryptR (increment-by-100 i r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m} {(increment-100 i)} (to-Singleton (increment-100 i)))

  {-- I-cryptR-crypt-increment100-path : Interprets the crypt-increment-by-100 path in cryptR as a path in the Universe given by crypt-increment-100 function --}
  I-cryptR-crypt-increment100-path : {m n : Nat} → (p q : Nat) → (i : Fin m) → (r : Records n m) →
                                     ap I-cryptR (crypt-increment-by-100 p q i r) ≡ ua (singleton-equiv {Vec Int m} {Vec Int m}
                                                                                                         {(crypt-increment-100 p q i)}
                                                                                                         (to-Singleton (crypt-increment-100 p q i)))

  {-- Paillier homomorphism --}

  paillier-hom* : {m : Nat} → (p q : Nat) → (i : Fin m) → (vec : Vec Int m) →  (Singleton ((paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)) vec)) ≡
                                                                                       (Singleton ((increment-100 i ○ id ○ id) vec))

  {-- I-hom-paillier1 : Maps the part 1 of Paillier homomorphism into the Universe --}
  I-hom-paillier1 : {m n : Nat} → (p q : Nat) → (i : Fin m) → (r : Records n m) →
                    ap I-cryptR (transport (λ x → ctab r ≡ ctab x) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                 ((paillier-enc p q r) ∘
                                 (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))))
                    ≡ (transport (λ x → Path (Singleton (execute r)) x) (paillier-hom* p q i (execute r))
                         (ua (singleton-equiv {Vec Int m} {Vec Int m}
                                           {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                           (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))))))

  {-- I-hom-paillier2 : Maps the part 2 of Paillier homomorphism into the Universe --}
  I-hom-paillier2 : {m n : Nat} → (p q : Nat) → (i : Fin m) → (r : Records n m) →
                    ap I-cryptR ((id-cryptR r) ∘ (id-cryptR (ID-R:: r)) ∘ (increment-by-100 i (ID-R:: (ID-R:: r))))
                    ≡ ua (singleton-equiv {Vec Int m} {Vec Int m}
                                           {(increment-100 i) ○ id ○ id}
                                           (to-Singleton ((increment-100 i) ○ id ○ id)))

  {-- paillier-hom : Representation of Paillier homomorphism in the Universe --}
  paillier-hom : {m : Nat} → (p q : Nat) → (i : Fin m) → (vec : Vec Int m) →
                  (transport (λ x → Path (Singleton vec) x) (paillier-hom* p q i vec)
                      (ua {Singleton vec}
                          {Singleton ((paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)) vec)}
                          (singleton-equiv {Vec Int m} {Vec Int m}
                                           {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                           (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))))))
                 ≡                                                                     
                      (ua {Singleton vec}
                          {Singleton ((increment-100 i ○ id ○ id) vec)}
                          (singleton-equiv {Vec Int m} {Vec Int m}
                                           {(increment-100 i ○ id ○ id)}
                                           (to-Singleton (increment-100 i ○ id ○ id))))

  -- example : {A B : Set} → (a b : A) → (p q : a ≡ b) → (x : p ≡ q) → ap (ap id) x ≡ apfId p ∘ x ∘ ! (apfId q)

  {-- I-cryptR-paillier-homotopy : Mapping of the Paillier homomorphism homotopy in cryptR into the Universe given by paillier-hom --}
  I-cryptR-paillier-homotopy : {m n : Nat} → (p q : Nat) → (i : Fin m) → (r : Records n m) → 
                                 (ap (ap I-cryptR) (paillier-homotopy p q i r)) ≡ I-hom-paillier1 p q i r ∘
                                                                                    paillier-hom p q i (execute r) ∘ ! (I-hom-paillier2 p q i r)


{-- Interpreters which converts the given queries into functions acting on types in the Universe --}

{-- Interpreters to map the paths into the Universe --}

interp#1 : {a b : cryptR} → (p : a ≡ b) → (I-cryptR a) ≃ (I-cryptR b)
interp#1 p = coe-biject (ap I-cryptR p) 

interp#2 : {a b : cryptR} → (p : a ≡ b) → (I-cryptR a) → (I-cryptR b)
interp#2 p = coe' (ap I-cryptR p) 

{-- Interpreters to map the homotopies into the Universe --}

interp#3 : {a b : cryptR} → {p q : a ≡ b} → (x : p ≡ q) → (I-cryptR a ≡ I-cryptR b) ≃ (I-cryptR a ≡ I-cryptR b)
interp#3 {a} {b} {p} {q} x = coe-biject (apI-path I-cryptR x)

interp#4 : {a b : cryptR} → {p q : a ≡ b} → (x : p ≡ q) → (I-cryptR a ≡ I-cryptR b) → (I-cryptR a ≡ I-cryptR b)
interp#4 x = coe' (apI-path I-cryptR x)

