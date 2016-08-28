{-# OPTIONS --type-in-type --without-K #-}

open import Function renaming (_∘_ to _○_)
open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv

open import CryptDB_HoTT.cryptography.Paillier-Cryptosystem

module CryptDB_HoTT.cryptography.encrypted-increment where

-- Encrypted increment query

crypt-increment-100 : {l : Nat} → (p q : Nat) → (i : Fin l) → Vec Int l → Vec Int l
crypt-increment-100 p q () []
crypt-increment-100 p q zero (x :: xs) = (x * (paillier-encrypt'' p q 100)) :: xs
crypt-increment-100 p q (suc i) (x :: xs) = x :: (crypt-increment-100 p q i xs)

crypt-decrement-100 : {l : Nat} → (p q : Nat) → (i : Fin l) → Vec Int l → Vec Int l
crypt-decrement-100 p q () []
crypt-decrement-100 p q zero (x :: xs) = (div x (paillier-encrypt'' p q 100)) :: xs
crypt-decrement-100 p q (suc i) (x :: xs) = x :: (crypt-decrement-100 p q i xs)

postulate
  crypt-inc-dec-inv : {p q l : Nat} → (i : Fin l) → (vec : Vec Int l) → (crypt-increment-100 p q i (crypt-decrement-100 p q i vec)) ≡ vec
  crypt-dec-inc-inv : {p q l : Nat} → (i : Fin l) → (vec : Vec Int l) → (crypt-decrement-100 p q i (crypt-increment-100 p q i vec)) ≡ vec

f∘g' : {p q l : Nat} → (i : Fin l) → Vec Int l → Vec Int l
f∘g' {p} {q} {l} i = (crypt-increment-100 p q i) ○ (crypt-decrement-100 p q i)

α' : {p q l : Nat} → (i : Fin l) → (vec : Vec Int l) → (f∘g' {p} {q} {l} i vec) ≡ vec
α' {p} {q} () []
α' {p} {q} zero (x :: xs) = begin
                             f∘g' {p} {q} zero (x :: xs) ≡⟨ refl _ ⟩
                             ((crypt-increment-100 p q zero) ○ (crypt-decrement-100 p q zero)) (x :: xs) ≡⟨ refl _ ⟩
                             (crypt-increment-100 p q zero (crypt-decrement-100 p q zero (x :: xs))) ≡⟨ crypt-inc-dec-inv {p} {q} zero (x :: xs) ⟩
                             (x :: xs ∎) 
α' {p} {q} (suc i) (x :: xs) = ap (λ xs' → x :: xs') (α' i xs)

g∘f' : {p q l : Nat} → (i : Fin l) → Vec Int l → Vec Int l
g∘f' {p} {q} {l} i = (crypt-decrement-100 p q i) ○ (crypt-increment-100 p q i)

β' : {p q l : Nat} → (i : Fin l) → (vec : Vec Int l) → (g∘f' {p} {q} {l} i vec) ≡ vec
β' {p} {q} () []
β' {p} {q} zero (x :: xs) = begin
                              g∘f' {p} {q} zero (x :: xs) ≡⟨ refl _ ⟩
                              ((crypt-decrement-100 p q zero) ○ (crypt-increment-100 p q zero)) (x :: xs) ≡⟨ refl _ ⟩
                              (crypt-decrement-100 p q zero (crypt-increment-100 p q zero (x :: xs))) ≡⟨ crypt-dec-inc-inv {p} {q} zero (x :: xs) ⟩
                              (x :: xs ∎)
β' {p} {q} (suc i) (x :: xs) = ap (λ xs' → x :: xs') (β' i xs)


crypt-inc-equiv≃ : {p q l : Nat} → (i : Fin l) → (Vec Int l ≃ Vec Int l)
crypt-inc-equiv≃ {p} {q} {l} i = crypt-increment-100 p q i , equiv₁ (mkqinv (crypt-decrement-100 p q i) (α' i) (β' i))

crypt-inc-path : {p q l : Nat} → (i : Fin l) → (Vec Int l ≡ Vec Int l)
crypt-inc-path {p} {q} {l} i with univalence 
... | (_ , eq) = isequiv.g eq (crypt-inc-equiv≃ {p} {q} {l} i)
