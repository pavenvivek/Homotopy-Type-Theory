{-# OPTIONS --type-in-type --without-K --no-termination-check #-}

open import Function renaming (_∘_ to _○_)

open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv

module CryptDB_HoTT.cryptography.OPE-Cryptosystem where

-- Order-Preserving Encryption (OPE)

ope-keygen-symmetric : Nat
ope-keygen-symmetric = 23

ope-encrypt' : (plain-text : Int) → Int
ope-encrypt' 0 = ope-keygen-symmetric
ope-encrypt' (suc n) = (ope-encrypt' n) + suc n

ope-encrypt : {l : Nat} → (plain-text : Vec Int l) → Vec Int l
ope-encrypt {l} plain-text = loop {Int} l ope-encrypt' plain-text

ope-decrypt' : {sub-val : Int} → (cipher-text : Int) → Int
ope-decrypt' {sub-val} 0 = (sub-val - 1)
ope-decrypt' {sub-val} (suc n) = ope-decrypt' {(sub-val + 1)} ((suc n) - sub-val)

ope-decrypt'' : (cipher-text : Int) → Int
ope-decrypt'' cipher-text = ope-decrypt' {1} (cipher-text - ope-keygen-symmetric)

ope-decrypt : {l : Nat} → (cipher-text : Vec Int l) → Vec Int l
ope-decrypt {l} cipher-text = loop {Int} l ope-decrypt'' cipher-text

postulate
  ope-dec-enc-inv : {l : Nat} → (message : Vec Int l) → (ope-decrypt (ope-encrypt message)) ≡ message
  ope-enc-dec-inv : {l : Nat} → (cipher : Vec Int l) → (ope-encrypt (ope-decrypt cipher)) ≡ cipher

f∘g[ope] : {l : Nat} → Vec Int l → Vec Int l
f∘g[ope] = ope-encrypt ○ ope-decrypt

α-ope : {l : Nat} → f∘g[ope] {l} ∼ id
α-ope {l} = indVec (λ v → f∘g[ope] v ≡ v)
                       (refl _)
                       (λ x xs p1 → indNat (λ x1 → f∘g[ope] (x1 :: xs) ≡ x1 :: xs)
                                      (begin
                                       f∘g[ope] (0 :: xs) ≡⟨ refl _ ⟩
                                       (ope-encrypt ○ ope-decrypt) (0 :: xs) ≡⟨ refl _ ⟩
                                       ope-encrypt (ope-decrypt (0 :: xs)) ≡⟨ ope-enc-dec-inv (0 :: xs) ⟩
                                       (0 :: xs ∎))
                                      (λ n pn →
                                         begin
                                         f∘g[ope] (suc n :: xs) ≡⟨ refl _ ⟩
                                         (ope-encrypt ○ ope-decrypt) (suc n :: xs) ≡⟨ refl _ ⟩
                                         ope-encrypt (ope-decrypt (suc n :: xs)) ≡⟨ ope-enc-dec-inv (suc n :: xs) ⟩
                                         (suc n :: xs ∎))
                                      x)


g∘f[ope] : {l : Nat} → Vec Int l → Vec Int l
g∘f[ope] = ope-decrypt ○ ope-encrypt

β-ope : {l : Nat} → g∘f[ope] {l} ∼ id
β-ope {l} = indVec (λ v → g∘f[ope] v ≡ v)
                           (refl _)
                           (λ x xs p1 → indNat (λ x₁ → g∘f[ope] (x₁ :: xs) ≡ x₁ :: xs)
                                          (begin
                                           g∘f[ope] (0 :: xs) ≡⟨ refl _ ⟩
                                           (ope-decrypt ○ ope-encrypt) (0 :: xs) ≡⟨ refl _ ⟩
                                           ope-decrypt (ope-encrypt (0 :: xs)) ≡⟨ ope-dec-enc-inv (0 :: xs) ⟩
                                           (0 :: xs ∎))
                                          (λ n pn →
                                             begin
                                             g∘f[ope] (suc n :: xs) ≡⟨ refl _ ⟩
                                             (ope-decrypt ○ ope-encrypt) (suc n :: xs) ≡⟨ refl _ ⟩
                                             ope-decrypt (ope-encrypt (suc n :: xs)) ≡⟨ ope-dec-enc-inv (suc n :: xs) ⟩
                                             (suc n :: xs ∎))
                                          x)


ope-equiv≃ : {l : Nat} → (Vec Int l ≃ Vec Int l)
ope-equiv≃ {l} = ope-encrypt , equiv₁ (mkqinv ope-decrypt α-ope β-ope)

ope-path : {l : Nat} → (Vec Int l ≡ Vec Int l)
ope-path {l} with univalence 
... | (_ , eq) = isequiv.g eq (ope-equiv≃ {l})
