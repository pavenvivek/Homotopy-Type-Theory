{-# OPTIONS --type-in-type --without-K #-}

open import Data.Bool
open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Equiv
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Interval

open import CryptDB_HoTT.cryptography.increment-path
open import CryptDB_HoTT.cryptography.RSA-Cryptosystem
open import CryptDB_HoTT.cryptography.Paillier-Cryptosystem
open import CryptDB_HoTT.cryptography.encrypted-increment
open import CryptDB_HoTT.cryptography.OPE-Cryptosystem
open import CryptDB_HoTT.cryptography.ElGamal-Cryptosystem

module CryptDB_HoTT.cryptography.crypto-onion-old where

  module hit where

    private
      data #R : Set where
        #tab_ : (l : Nat) → #R
        #tabRSA_ : (l : Nat) → #R
        #tabPL_ : (l : Nat) → #R
        #tabOPE_ : (l : Nat) → #R
        #tabEG_ : (l : Nat) → #R

    R : Set
    R = #R

    tab_ : (l : Nat) → R
    tab_ = #tab_
   
    tabRSA_ : (l : Nat) → R
    tabRSA_ = #tabRSA_
   
    tabPL_ : (l : Nat) → R
    tabPL_ = #tabPL_

    tabOPE_ : (l : Nat) → R
    tabOPE_ = #tabOPE_

    tabEG_ : (l : Nat) → R
    tabEG_ = #tabEG_


    postulate
      increment100 : {l : Nat} → (i : Fin l) → (tab l) ≡ (tab l)
      rsa-crypto : {l : Nat} → (tab l) ≡ (tabRSA l)
      paillier-crypto : {l : Nat} → (tab l) ≡ (tabPL l)
      increment100-crypto : {l : Nat} → (i : Fin l) → (tabPL l) ≡ (tabPL l) -- → (pl : (tab l) ≡ (tabPL l))
      ope-crypto : {l : Nat} → (tab l) ≡ (tabOPE l)
      elgamalRSA-crypto : {l : Nat} → (tabRSA l) ≡ (tabEG l)
      elgamalOPE-crypto : {l : Nat} → (tabOPE l) ≡ (tabEG l)

    rec : {l : Nat} → {C : Set} →
          (c1 c2 c3 c4 c5 : C) →
          (c-increment100 : c1 ≡ c1) →
          (c-rsa-crypto : c1 ≡ c2) →
          (c-paillier-crypto : c1 ≡ c3) →
          (c-increment100-crypto : c3 ≡ c3) →
          (c-ope-crypto : c1 ≡ c4) →
          (c-elgamal-rsa-crypto : c2 ≡ c5) →
          (c-elgamal-ope-crypto : c4 ≡ c5) →
          R → C
    rec c1 c2 c3 c4 c5 c-increment100 c-rsa-crypto c-paillier-crypto c-increment100-crypto c-ope-crypto c-elgamal-rsa-crypto c-elgamal-ope-crypto (#tab l) = c1
    rec c1 c2 c3 c4 c5 c-increment100 c-rsa-crypto c-paillier-crypto c-increment100-crypto c-ope-crypto c-elgamal-rsa-crypto c-elgamal-ope-crypto (#tabRSA l) = c2
    rec c1 c2 c3 c4 c5 c-increment100 c-rsa-crypto c-paillier-crypto c-increment100-crypto c-ope-crypto c-elgamal-rsa-crypto c-elgamal-ope-crypto (#tabPL l) = c3
    rec c1 c2 c3 c4 c5 c-increment100 c-rsa-crypto c-paillier-crypto c-increment100-crypto c-ope-crypto c-elgamal-rsa-crypto c-elgamal-ope-crypto (#tabOPE l) = c4
    rec c1 c2 c3 c4 c5 c-increment100 c-rsa-crypto c-paillier-crypto c-increment100-crypto c-ope-crypto c-elgamal-rsa-crypto c-elgamal-ope-crypto (#tabEG l) = c5

    postulate

      βrec-inc-crypto : {l : Nat} → {i : Fin l} → {C : Set} →
                        (c1 c2 c3 c4 c5 : C) →
                        (c-increment100 : c1 ≡ c1) →
                        (c-rsa-crypto : c1 ≡ c2) →
                        (c-paillier-crypto : c1 ≡ c3) →
                        (c-increment100-crypto : c3 ≡ c3) →
                        (c-ope-crypto : c1 ≡ c4) →
                        (c-elgamal-rsa-crypto : c2 ≡ c5) →
                        (c-elgamal-ope-crypto : c4 ≡ c5) →
                        ap (rec {l} c1 c2 c3 c4 c5
                                c-increment100
                                c-rsa-crypto
                                c-paillier-crypto
                                c-increment100-crypto
                                c-ope-crypto
                                c-elgamal-rsa-crypto
                                c-elgamal-ope-crypto)
                                (increment100 {l} i) ≡ c-increment100

      βrec-rsa-crypto : {l : Nat}  → {C : Set} →
                        (c1 c2 c3 c4 c5 : C) →
                        (c-increment100 : c1 ≡ c1) →
                        (c-rsa-crypto : c1 ≡ c2) →
                        (c-paillier-crypto : c1 ≡ c3) →
                        (c-increment100-crypto : c3 ≡ c3) →
                        (c-ope-crypto : c1 ≡ c4) →
                        (c-elgamal-rsa-crypto : c2 ≡ c5) →
                        (c-elgamal-ope-crypto : c4 ≡ c5) →
                        ap (rec {l} c1 c2 c3 c4 c5
                                c-increment100
                                c-rsa-crypto
                                c-paillier-crypto
                                c-increment100-crypto
                                c-ope-crypto
                                c-elgamal-rsa-crypto
                                c-elgamal-ope-crypto)
                                (rsa-crypto {l}) ≡ c-rsa-crypto

      βrec-paillier-crypto : {l : Nat} → {C : Set} →
                             (c1 c2 c3 c4 c5 : C) →
                             (c-increment100 : c1 ≡ c1) →
                             (c-rsa-crypto : c1 ≡ c2) →
                             (c-paillier-crypto : c1 ≡ c3) →
                             (c-increment100-crypto : c3 ≡ c3) →
                             (c-ope-crypto : c1 ≡ c4) →
                             (c-elgamal-rsa-crypto : c2 ≡ c5) →
                             (c-elgamal-ope-crypto : c4 ≡ c5) →
                             ap (rec {l} c1 c2 c3 c4 c5
                                     c-increment100
                                     c-rsa-crypto
                                     c-paillier-crypto
                                     c-increment100-crypto
                                     c-ope-crypto
                                     c-elgamal-rsa-crypto
                                     c-elgamal-ope-crypto)
                                     (paillier-crypto {l}) ≡ c-paillier-crypto

      βrec-crypt-inc-crypto : {l : Nat} → {i : Fin l} → {C : Set} →
                              (c1 c2 c3 c4 c5 : C) →
                              (c-increment100 : c1 ≡ c1) →
                              (c-rsa-crypto : c1 ≡ c2) →
                              (c-paillier-crypto : c1 ≡ c3) →
                              (c-increment100-crypto : c3 ≡ c3) →
                              (c-ope-crypto : c1 ≡ c4) →
                              (c-elgamal-rsa-crypto : c2 ≡ c5) →
                              (c-elgamal-ope-crypto : c4 ≡ c5) →
                              ap (rec {l} c1 c2 c3 c4 c5
                                      c-increment100
                                      c-rsa-crypto
                                      c-paillier-crypto
                                      c-increment100-crypto
                                      c-ope-crypto
                                      c-elgamal-rsa-crypto
                                      c-elgamal-ope-crypto)
                                      (increment100-crypto {l} i) ≡ c-increment100-crypto

      βrec-ope-crypto : {l : Nat} → {C : Set} →
                        (c1 c2 c3 c4 c5 : C) →
                        (c-increment100 : c1 ≡ c1) →
                        (c-rsa-crypto : c1 ≡ c2) →
                        (c-paillier-crypto : c1 ≡ c3) →
                        (c-increment100-crypto : c3 ≡ c3) →
                        (c-ope-crypto : c1 ≡ c4) →
                        (c-elgamal-rsa-crypto : c2 ≡ c5) →
                        (c-elgamal-ope-crypto : c4 ≡ c5) →
                        ap (rec {l} c1 c2 c3 c4 c5
                                c-increment100
                                c-rsa-crypto
                                c-paillier-crypto
                                c-increment100-crypto
                                c-ope-crypto
                                c-elgamal-rsa-crypto
                                c-elgamal-ope-crypto)
                        (ope-crypto {l}) ≡ c-ope-crypto

      βrec-elgamal-rsa-crypto : {l : Nat} → {C : Set} →
                                (c1 c2 c3 c4 c5 : C) →
                                (c-increment100 : c1 ≡ c1) →
                                (c-rsa-crypto : c1 ≡ c2) →
                                (c-paillier-crypto : c1 ≡ c3) →
                                (c-increment100-crypto : c3 ≡ c3) →
                                (c-ope-crypto : c1 ≡ c4) →
                                (c-elgamal-rsa-crypto : c2 ≡ c5) →
                                (c-elgamal-ope-crypto : c4 ≡ c5) →
                                ap (rec {l} c1 c2 c3 c4 c5
                                        c-increment100
                                        c-rsa-crypto
                                        c-paillier-crypto
                                        c-increment100-crypto
                                        c-ope-crypto
                                        c-elgamal-rsa-crypto
                                        c-elgamal-ope-crypto)
                                        (elgamalRSA-crypto {l}) ≡ c-elgamal-rsa-crypto

      βrec-elgamal-ope-crypto : {l : Nat} → {C : Set} →
                                (c1 c2 c3 c4 c5 : C) →
                                (c-increment100 : c1 ≡ c1) →
                                (c-rsa-crypto : c1 ≡ c2) →
                                (c-paillier-crypto : c1 ≡ c3) →
                                (c-increment100-crypto : c3 ≡ c3) →
                                (c-ope-crypto : c1 ≡ c4) →
                                (c-elgamal-rsa-crypto : c2 ≡ c5) →
                                (c-elgamal-ope-crypto : c4 ≡ c5) →
                                ap (rec {l} c1 c2 c3 c4 c5
                                        c-increment100
                                        c-rsa-crypto
                                        c-paillier-crypto
                                        c-increment100-crypto
                                        c-ope-crypto
                                        c-elgamal-rsa-crypto
                                        c-elgamal-ope-crypto)
                                        (elgamalOPE-crypto {l}) ≡ c-elgamal-ope-crypto

--------------------------------------------------------

open hit

coe-equiv : {l : Nat} → (Vec Int l ≡ Vec Int l) → (Vec Int l ≃ Vec Int l)
coe-equiv path with univalence 
... | (f , eq) = f path

coe : {l : Nat} → (Vec Int l ≡ Vec Int l) → (Vec Int l → Vec Int l)
coe path = fst (coe-equiv path)

Interpreter : {p q l : Nat} → {i : Fin l} → R → Set
Interpreter {p} {q} {l} {i} = rec {l}
                                  (Vec Int l) (Vec Int l) (Vec Int l) (Vec Int l)
                                  (Vec ((Int × Int) × Int) l)
                                  (inc-path {l} i)
                                  (rsa-path {p} {q} {l})
                                  (paillier-path {p} {q} {l})
                                  (crypt-inc-path {p} {q} {l} i)
                                  (ope-path {l})
                                  (ElGamal-path {p} {l})
                                  (ElGamal-path {p} {l})

I[rsa-crypto] : {p q l : Nat} → {i : Fin l} → ap (Interpreter {p} {q} {l} {i}) (rsa-crypto {l}) ≡ (rsa-path {p} {q} {l})
I[rsa-crypto] {p} {q} {l} {i} = βrec-rsa-crypto {l}
                                                (Vec Int l) (Vec Int l) (Vec Int l) (Vec Int l)
                                                (Vec ((Int × Int) × Int) l)
                                                (inc-path {l} i)
                                                (rsa-path {p} {q} {l})
                                                (paillier-path {p} {q} {l})
                                                (crypt-inc-path {p} {q} {l} i)
                                                (ope-path {l})
                                                (ElGamal-path {p} {l})
                                                (ElGamal-path {p} {l})

I[paillier-crypto] : {p q l : Nat} → {i : Fin l} → ap (Interpreter {p} {q} {l} {i}) (paillier-crypto {l}) ≡ (paillier-path {p} {q} {l})
I[paillier-crypto] {p} {q} {l} {i} = βrec-paillier-crypto {l}
                                                          (Vec Int l) (Vec Int l) (Vec Int l) (Vec Int l)
                                                          (Vec ((Int × Int) × Int) l)
                                                          (inc-path {l} i)
                                                          (rsa-path {p} {q} {l})
                                                          (paillier-path {p} {q} {l})
                                                          (crypt-inc-path {p} {q} {l} i)
                                                          (ope-path {l})
                                                          (ElGamal-path {p} {l})
                                                          (ElGamal-path {p} {l})

I[ope-crypto] : {p q l : Nat} → {i : Fin l} → ap (Interpreter {p} {q} {l} {i}) (ope-crypto {l}) ≡ (ope-path {l})
I[ope-crypto] {p} {q} {l} {i} = βrec-ope-crypto {l}
                                                (Vec Int l) (Vec Int l) (Vec Int l) (Vec Int l)
                                                (Vec ((Int × Int) × Int) l)
                                                (inc-path {l} i)
                                                (rsa-path {p} {q} {l})
                                                (paillier-path {p} {q} {l})
                                                (crypt-inc-path {p} {q} {l} i)
                                                (ope-path {l})
                                                (ElGamal-path {p} {l})
                                                (ElGamal-path {p} {l})

I[elgamalRSA-crypto] : {p q l : Nat} → {i : Fin l} → ap (Interpreter {p} {q} {l} {i}) (elgamalRSA-crypto {l}) ≡ (ElGamal-path {p} {l})
I[elgamalRSA-crypto] {p} {q} {l} {i} = βrec-elgamal-rsa-crypto {l}
                                                               (Vec Int l) (Vec Int l) (Vec Int l) (Vec Int l)
                                                               (Vec ((Int × Int) × Int) l)
                                                               (inc-path {l} i)
                                                               (rsa-path {p} {q} {l})
                                                               (paillier-path {p} {q} {l})
                                                               (crypt-inc-path {p} {q} {l} i)
                                                               (ope-path {l})
                                                               (ElGamal-path {p} {l})
                                                               (ElGamal-path {p} {l})

I[elgamalOPE-crypto] : {p q l : Nat} → {i : Fin l} → ap (Interpreter {p} {q} {l} {i}) (elgamalOPE-crypto {l}) ≡ (ElGamal-path {p} {l})
I[elgamalOPE-crypto] {p} {q} {l} {i} = βrec-elgamal-ope-crypto {l}
                                                               (Vec Int l) (Vec Int l) (Vec Int l) (Vec Int l)
                                                               (Vec ((Int × Int) × Int) l)
                                                               (inc-path {l} i)
                                                               (rsa-path {p} {q} {l})
                                                               (paillier-path {p} {q} {l})
                                                               (crypt-inc-path {p} {q} {l} i)
                                                               (ope-path {l})
                                                               (ElGamal-path {p} {l})
                                                               (ElGamal-path {p} {l})

I[inc100] : {p q l : Nat} → {i : Fin l} → ap (Interpreter {p} {q} {l} {i}) (increment100 {l} i) ≡ (inc-path {l} i)
I[inc100] {p} {q} {l} {i} = βrec-inc-crypto {l}
                                            (Vec Int l) (Vec Int l) (Vec Int l) (Vec Int l)
                                            (Vec ((Int × Int) × Int) l)
                                            (inc-path {l} i)
                                            (rsa-path {p} {q} {l})
                                            (paillier-path {p} {q} {l})
                                            (crypt-inc-path {p} {q} {l} i)
                                            (ope-path {l})
                                            (ElGamal-path {p} {l})
                                            (ElGamal-path {p} {l})

I[crypt-inc100] : {p q l : Nat} → {i : Fin l} → ap (Interpreter {p} {q} {l} {i}) (increment100-crypto {l} i) ≡ (crypt-inc-path {p} {q} {l} i)
I[crypt-inc100] {p} {q} {l} {i} = βrec-crypt-inc-crypto {l}
                                                        (Vec Int l) (Vec Int l) (Vec Int l) (Vec Int l)
                                                        (Vec ((Int × Int) × Int) l)
                                                        (inc-path {l} i)
                                                        (rsa-path {p} {q} {l})
                                                        (paillier-path {p} {q} {l})
                                                        (crypt-inc-path {p} {q} {l} i)
                                                        (ope-path {l})
                                                        (ElGamal-path {p} {l})
                                                        (ElGamal-path {p} {l})

interp : {p q l : Nat} → {patch-num : Nat} → (patch : (tab l) ≡ (tab l)) → Vec Int l → Vec Int l
interp {p} {q} {l} {patch-num} patch = if 1 == patch-num
                                          then (fst (rsa-equiv≃ {p} {q} {l}))
                                          else if 2 == patch-num
                                                  then (isequiv.g (snd (rsa-equiv≃ {p} {q} {l})))
                                                  else if 3 == patch-num
                                                          then (fst (paillier-equiv≃ {p} {q} {l}))
                                                          else if 4 == patch-num
                                                               then (isequiv.g (snd (paillier-equiv≃ {p} {q} {l})))
                                                               else if 5 == patch-num
                                                                    then (fst (ope-equiv≃ {l}))
                                                                    else if 6 == patch-num
                                                                         then (isequiv.g (snd (ope-equiv≃ {l})))
                                                                         else abort failed

interp-ElGamal-enc : {p l : Nat} → {patch-num : Nat} → (patch : (tab l) ≡ (tabEG l)) → Vec Int l → Vec ((Int × Int) × Int) l
interp-ElGamal-enc {p} {l} {patch-num} patch = (fst (ElGamal-equiv≃ {p} {l}))
                                              
interp-ElGamal-dec : {p l : Nat} → {patch-num : Nat} → (patch : (tabEG l) ≡ (tab l)) → Vec ((Int × Int) × Int) l → Vec Int l
interp-ElGamal-dec {p} {l} {patch-num} patch = (isequiv.g (snd (ElGamal-equiv≃ {p} {l})))

Onion-Eq = (rsa-crypto {3}) ∘ (elgamalRSA-crypto {3})
Onion-Add = (paillier-crypto {3})
Onion-Ord = (ope-crypto {3}) ∘ (elgamalOPE-crypto {3})                                
