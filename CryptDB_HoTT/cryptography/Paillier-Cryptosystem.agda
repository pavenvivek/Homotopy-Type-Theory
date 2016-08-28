{-# OPTIONS --type-in-type --without-K #-}

open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv

module CryptDB_HoTT.cryptography.Paillier-Cryptosystem where

-- Paillier Crypto-system

paillier-keygen-public : (p : Nat) → (q : Nat) → Nat × Nat
paillier-keygen-public p q = (p * q) , (p * q) + 1

calculateL : Nat → Nat → Nat
calculateL u n = div (u - 1) n

paillier-keygen-private : (p : Nat) → (q : Nat) → Nat × Nat
paillier-keygen-private p q = let λ' : Nat
                                  λ' = lcm (p - 1) (q - 1)

                                  n :  Nat
                                  n = p * q

                                  g : Nat
                                  g = proj₂ (paillier-keygen-public p q)
                                  
                              in (λ' , (mod*-inv (calculateL (mod (g ^ λ') (n ^ 2)) n) n))


paillier-encrypt' : (plain-text : Int) → (random : Nat) → (public-key : Nat × Nat) → Int
paillier-encrypt' plain-text r (n , g) = mod (g ^ plain-text * r ^ n) (n ^ 2)

paillier-encrypt'' :  Nat → Nat → (plain-text : Int) → Int
paillier-encrypt'' p q plain-text = let public-key : Nat × Nat
                                        public-key = (paillier-keygen-public p q)

                                        r : Nat
                                        r = (getRand p)

                                    in (paillier-encrypt' plain-text r public-key) 

paillier-encrypt : {l : Nat} → Nat → Nat → (plain-text : Vec Int l) → Vec Int l
paillier-encrypt {l} p q plain-text = loop {Int} l (paillier-encrypt'' p q) plain-text

paillier-decrypt' : (cipher-text : Int) → (n : Nat) → (private-key : Nat × Nat) → Int
paillier-decrypt' cipher-text n (λ' , μ) = let L : Nat
                                               L = calculateL (mod (cipher-text ^ λ') (n ^ 2)) n
                                           in mod (L * μ) n

paillier-decrypt'' : Nat → Nat → (cipher-text : Int) → Int
paillier-decrypt'' p q cipher-text = let private-key : Nat × Nat
                                         private-key = (paillier-keygen-private p q)
                                     in (paillier-decrypt' cipher-text (p * q) private-key) 


paillier-decrypt : {l : Nat} → Nat → Nat → (cipher-text : Vec Int l) → Vec Int l
paillier-decrypt {l} p q cipher-text = loop {Int} l (paillier-decrypt'' p q) cipher-text

postulate
  paillier-dec-enc-inv : {p q : Nat} {l : Nat} → (message : Vec Int l) → (paillier-decrypt p q (paillier-encrypt p q message)) ≡ message
  paillier-enc-dec-inv : {p q : Nat} {l : Nat} → (cipher : Vec Int l) → (paillier-encrypt p q (paillier-decrypt p q cipher)) ≡ cipher

f∘g[paillier] : {p q l : Nat} → Vec Int l → Vec Int l
f∘g[paillier] {p} {q} = (paillier-encrypt p q) ○ (paillier-decrypt p q)

α-paillier : {p q l : Nat} → f∘g[paillier] {p} {q} {l} ∼ id
α-paillier {p} {q} {l} = indVec (λ v → f∘g[paillier] {p} {q} v ≡ v)
                       (refl _)
                       (λ x xs p1 → indNat (λ x1 → f∘g[paillier] {p} {q} (x1 :: xs) ≡ x1 :: xs)
                                      (begin
                                       f∘g[paillier] {p} {q} (0 :: xs) ≡⟨ refl _ ⟩
                                       (paillier-encrypt p q ○ paillier-decrypt p q) (0 :: xs) ≡⟨ refl _ ⟩
                                       paillier-encrypt p q (paillier-decrypt p q (0 :: xs)) ≡⟨ paillier-enc-dec-inv {p} {q} (0 :: xs) ⟩
                                       (0 :: xs ∎))
                                      (λ n pn →
                                         begin
                                         f∘g[paillier] {p} {q} (suc n :: xs) ≡⟨ refl _ ⟩
                                         (paillier-encrypt p q ○ paillier-decrypt p q) (suc n :: xs) ≡⟨ refl _ ⟩
                                         paillier-encrypt p q (paillier-decrypt p q (suc n :: xs)) ≡⟨ paillier-enc-dec-inv {p} {q} (suc n :: xs) ⟩
                                         (suc n :: xs ∎))
                                      x)


g∘f[paillier] : {p q l : Nat} → Vec Int l → Vec Int l
g∘f[paillier] {p} {q} = (paillier-decrypt p q) ○ (paillier-encrypt p q)

β-paillier : {p q l : Nat} → g∘f[paillier] {p} {q} {l} ∼ id
β-paillier {p} {q} {l} = indVec (λ v → g∘f[paillier] {p} {q} v ≡ v)
                           (refl _)
                           (λ x xs p1 → indNat (λ x₁ → g∘f[paillier] {p} {q} (x₁ :: xs) ≡ x₁ :: xs)
                                          (begin
                                           g∘f[paillier] {p} {q} (0 :: xs) ≡⟨ refl _ ⟩
                                           (paillier-decrypt p q ○ paillier-encrypt p q) (0 :: xs) ≡⟨ refl _ ⟩
                                           paillier-decrypt p q (paillier-encrypt p q (0 :: xs)) ≡⟨ paillier-dec-enc-inv {p} {q} (0 :: xs) ⟩
                                           (0 :: xs ∎))
                                          (λ n pn →
                                             begin
                                             g∘f[paillier] {p} {q} (suc n :: xs) ≡⟨ refl _ ⟩
                                             (paillier-decrypt p q ○ paillier-encrypt p q) (suc n :: xs) ≡⟨ refl _ ⟩
                                             paillier-decrypt p q (paillier-encrypt p q (suc n :: xs)) ≡⟨ paillier-dec-enc-inv {p} {q} (suc n :: xs) ⟩
                                             (suc n :: xs ∎))
                                          x)


paillier-equiv≃ : {p q l : Nat} → (Vec Int l ≃ Vec Int l)
paillier-equiv≃ {p} {q} {l} = paillier-encrypt p q , equiv₁ (mkqinv (paillier-decrypt p q) (α-paillier {p} {q}) (β-paillier {p} {q}))

paillier-path : {p q l : Nat} → (Vec Int l ≡ Vec Int l)
paillier-path {p} {q} {l} with univalence 
... | (_ , eq) = isequiv.g eq (paillier-equiv≃ {p} {q} {l})
