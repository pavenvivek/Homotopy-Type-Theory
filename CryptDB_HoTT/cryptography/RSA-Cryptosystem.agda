{-# OPTIONS --type-in-type --without-K #-}

open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv

module CryptDB_HoTT.cryptography.RSA-Cryptosystem where

-- RSA Crypto-system

rsa-keygen-public : (p : Nat) → (q : Nat) → (Nat × Nat)
rsa-keygen-public p q = let euler-totient : Nat
                            euler-totient = (p - 1) * (q - 1)

                            n : Nat
                            n = p * q
                            
                        in coprime euler-totient , n


rsa-keygen-private : (p : Nat) → (q : Nat) → (Nat × Nat)
rsa-keygen-private p q =  let e : Nat
                              e = (proj₁ (rsa-keygen-public p q))

                              n : Nat
                              n = p * q

                              euler-totient : Nat
                              euler-totient = (p - 1) * (q - 1)
                              
                          in mod*-inv e euler-totient ,  p * q


rsa-encrypt' : (plain-text : Int) → (public-key : Nat × Nat) → Int
rsa-encrypt' plain-text (e , n) = mod (plain-text ^ e) n

rsa-encrypt'' : Nat → Nat → (plain-text : Int) → Int
rsa-encrypt'' p q plain-text = let public-key : Nat × Nat
                                   public-key = (rsa-keygen-public p q)
                               in (rsa-encrypt' plain-text public-key)
    
rsa-encrypt : {l : Nat} → Nat → Nat → (plain-text : Vec Int l) → Vec Int l
rsa-encrypt {l} p q plain-text = loop {Int} l (rsa-encrypt'' p q) plain-text

rsa-decrypt' : (cipher-text : Int) → (private-key : Nat × Nat) → Int
rsa-decrypt' cipher-text (d , n) = mod (cipher-text ^ d) n

rsa-decrypt'' : Nat → Nat → (cipher-text : Int) → Int
rsa-decrypt'' p q cipher-text = let private-key : Nat × Nat
                                    private-key = (rsa-keygen-private p q)
                                in (rsa-decrypt' cipher-text private-key) 

rsa-decrypt : {l : Nat} → Nat → Nat → (cipher-text : Vec Int l) → Vec Int l
rsa-decrypt {l} p q cipher-text = loop {Int} l (rsa-decrypt'' p q) cipher-text

postulate
  rsa-dec-enc-inv : {p q : Nat} {l : Nat} → (message : Vec Int l) → (rsa-decrypt p q (rsa-encrypt p q message)) ≡ message
  rsa-enc-dec-inv : {p q : Nat} {l : Nat} → (cipher : Vec Int l) → (rsa-encrypt p q (rsa-decrypt p q cipher)) ≡ cipher

f∘g[rsa] : {p q l : Nat} → Vec Int l → Vec Int l
f∘g[rsa] {p} {q} = (rsa-encrypt p q) ○ (rsa-decrypt p q)


α-rsa : {p q l : Nat} → f∘g[rsa] {p} {q} {l} ∼ id
α-rsa {p} {q} {l} = indVec (λ v → f∘g[rsa] {p} {q} v ≡ v)
                       (refl _)
                       (λ x xs p1 → indNat (λ x1 → f∘g[rsa] {p} {q} (x1 :: xs) ≡ x1 :: xs)
                                      (begin
                                       f∘g[rsa] {p} {q} (0 :: xs) ≡⟨ refl _ ⟩
                                       (rsa-encrypt p q ○ rsa-decrypt p q) (0 :: xs) ≡⟨ refl _ ⟩
                                       rsa-encrypt p q (rsa-decrypt p q (0 :: xs)) ≡⟨
                                       rsa-enc-dec-inv {p} {q} (0 :: xs) ⟩ (0 :: xs ∎))
                                      (λ n pn →
                                         begin
                                         f∘g[rsa] {p} {q} (suc n :: xs) ≡⟨ refl _ ⟩
                                         (rsa-encrypt p q ○ rsa-decrypt p q) (suc n :: xs) ≡⟨ refl _ ⟩
                                         rsa-encrypt p q (rsa-decrypt p q (suc n :: xs)) ≡⟨
                                         rsa-enc-dec-inv {p} {q} (suc n :: xs) ⟩ (suc n :: xs ∎))
                                      x)

g∘f[rsa] : {p q l : Nat} → Vec Int l → Vec Int l
g∘f[rsa] {p} {q} = (rsa-decrypt p q) ○ (rsa-encrypt p q)

β-rsa : {p q l : Nat} → g∘f[rsa] {p} {q} {l} ∼ id
β-rsa {p} {q} {l} = indVec (λ v → g∘f[rsa] {p} {q} v ≡ v)
                           (refl _)
                           (λ x xs p1 → indNat (λ x₁ → g∘f[rsa] {p} {q} (x₁ :: xs) ≡ x₁ :: xs)
                                          (begin
                                           g∘f[rsa] {p} {q} (0 :: xs) ≡⟨ refl _ ⟩
                                           (rsa-decrypt p q ○ rsa-encrypt p q) (0 :: xs) ≡⟨ refl _ ⟩
                                           rsa-decrypt p q (rsa-encrypt p q (0 :: xs)) ≡⟨
                                           rsa-dec-enc-inv {p} {q} (0 :: xs) ⟩ (0 :: xs ∎))
                                          (λ n pn →
                                             begin
                                             g∘f[rsa] {p} {q} (suc n :: xs) ≡⟨ refl _ ⟩
                                             (rsa-decrypt p q ○ rsa-encrypt p q) (suc n :: xs) ≡⟨ refl _ ⟩
                                             rsa-decrypt p q (rsa-encrypt p q (suc n :: xs)) ≡⟨
                                             rsa-dec-enc-inv {p} {q} (suc n :: xs) ⟩ (suc n :: xs ∎))
                                          x)


rsa-equiv≃ : {p q l : Nat} → (Vec Int l ≃ Vec Int l)
rsa-equiv≃ {p} {q} {l} = rsa-encrypt p q , equiv₁ (mkqinv (rsa-decrypt p q) (α-rsa {p} {q}) (β-rsa {p} {q}))

rsa-path : {p q l : Nat} → (Vec Int l ≡ Vec Int l)
rsa-path {p} {q} {l} with univalence 
... | (_ , eq) = isequiv.g eq (rsa-equiv≃ {p} {q} {l})
