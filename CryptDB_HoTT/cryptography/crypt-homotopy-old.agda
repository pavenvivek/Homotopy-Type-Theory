{-# OPTIONS --type-in-type --without-K #-}

open import Data.Bool
open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv
open import CryptDB_HoTT.agda_lib.Interval

open import CryptDB_HoTT.cryptography.crypto-onion-old
open import CryptDB_HoTT.cryptography.Paillier-Cryptosystem
open import CryptDB_HoTT.cryptography.increment-path
open import CryptDB_HoTT.cryptography.encrypted-increment

module CryptDB_HoTT.cryptography.crypt-homotopy-old where

open hit

postulate -- homotopies
   paillier-hom : {l : Nat} {i : Fin l} → Path ((paillier-crypto {l}) ∘ (increment100-crypto {l} i) ∘ ! (paillier-crypto {l})) (increment100 {l} i)
   paillier-hom' : {l : Nat} {i : Fin l} → Path {I × ((tab l) ≡ (tab l))} (zer , ((paillier-crypto {l}) ∘ (increment100-crypto {l} i) ∘ ! (paillier-crypto {l}))) (one , (increment100 {l} i))
   R-homotopy : {l : Nat} {i : Fin l} → (p1 p2 : (tab l) ≡ (tab l)) → Path {(tab l) ≡ (tab l)} p1 p2

prod-path : {A B : Set} → (a1 a2 : A) → (b1 b2 : B) → (pair : (Path a1 a2) × (Path b1 b2)) → Path {A × B} (a1 , b1) (a2 , b2)
prod-path {A} {B} a1 a2 b1 b2 pair = ind× {(Path a1 a2)} {(Path b1 b2)}
                                          (λ p → Path {A × B} (a1 , b1) (a2 , b2)) 
                                          (λ a-path b-path → pathInd {A} (λ {a1'} {a2'} a-path' → Path {A × B} (a1' , b1) (a2' , b2))
                                                                          (λ x → (pathInd {B} (λ {b1'} {b2'} b-path' → Path {A × B} (x , b1') (x , b2'))
                                                                                               (λ y → refl _)
                                                                                               {b1} {b2} b-path))
                                                                          {a1} {a2} a-path) pair 

path-prod : {A B : Set} → (a1 a2 : A) → (b1 b2 : B) → (path : Path {A × B} (a1 , b1) (a2 , b2)) → (Path a1 a2) × (Path b1 b2) 
path-prod {A} {B} a1 a2 b1 b2 path = pathInd {A × B}
                                             (λ {x} {y} p → Path (proj₁ x) (proj₁ y) × Path (proj₂ x) (proj₂ y))
                                             (λ x → refl _ , refl _) 
                                             path

f-hom-eq : {l : Nat} {i : Fin l} → (p1 p2 : (tab l ≡ tab l)) → (Path zer one) × (Path p1 p2)  → Path {I × ((tab l) ≡ (tab l))} (zer , p1) (one , p2)
f-hom-eq {l} {i} p1 p2 (seg , path) = prod-path zer one p1 p2 (seg , R-homotopy {l} {i} p1 p2)

g-hom-eq : {l : Nat} {i : Fin l} → {p1 p2 : (tab l ≡ tab l)} → Path {I × ((tab l) ≡ (tab l))} (zer , p1) (one , p2) → Path zer one × Path p1 p2
g-hom-eq {l} {i} {p1} {p2} path = path-prod zer one p1 p2 path -- ap proj₂ path


postulate
  seg-singleton : (x : Path zer one) → x ≡ seg


f-hom : {l : Nat} {i : Fin l} → (p1 p2 : (tab l ≡ tab l)) → (Path p1 p2) → (Path zer one) × (Path p1 p2)
f-hom {l} {i} p1 p2 path = seg , path

g-hom : {l : Nat} {i : Fin l} → (p1 p2 : (tab l ≡ tab l)) → (Path zer one) × (Path p1 p2) → Path p1 p2
g-hom {l} {i} p1 p2 (seg , path) = path

α-hom : {l : Nat} {i : Fin l} → (p1 p2 : (tab l ≡ tab l)) → (pair : (Path zer one) × (Path p1 p2)) → (f-hom {l} {i} p1 p2 (g-hom {l} {i} p1 p2 (pair))) ≡ pair
α-hom {l} {i} p1 p2 (s , path) = begin
                                   f-hom {l} {i} p1 p2 (g-hom {l} {i} p1 p2 (s , path)) ≡⟨ refl _ ⟩
                                   f-hom {l} {i} p1 p2 path ≡⟨ refl _ ⟩
                                   (seg , path) ≡⟨ ! (ap (λ x → x , path) (seg-singleton s)) ⟩
                                   (s , path ∎)

β-hom : {l : Nat} {i : Fin l} → (p1 p2 : (tab l ≡ tab l)) → (path : Path p1 p2) → (g-hom {l} {i} p1 p2 (f-hom {l} {i} p1 p2 (path))) ≡ path
β-hom {l} {i} p1 p2 path = begin
                             g-hom {l} {i} p1 p2 (f-hom {l} {i} p1 p2 path) ≡⟨ refl _ ⟩
                             g-hom {l} {i} p1 p2 (seg , path) ≡⟨ refl _ ⟩
                             (path ∎)

hom-equiv≃ : {l : Nat} → {i : Fin l} → {p1 p2 : (tab l ≡ tab l)} → (Path p1 p2) ≃ ((Path zer one) × (Path p1 p2))
hom-equiv≃ {l} {i} {p1} {p2} =  (f-hom {l} {i} p1 p2) , (equiv₁ (mkqinv (g-hom {l} {i} p1 p2) (α-hom {l} {i} p1 p2) (β-hom {l} {i} p1 p2)))

hom-path : {l : Nat} → {i : Fin l} → {p1 p2 : (tab l ≡ tab l)} → (Path p1 p2) ≡ ((Path zer one) × (Path p1 p2))
hom-path {l} {i} {p1} {p2} with univalence 
... | (_ , eq) = isequiv.g eq (hom-equiv≃ {l} {i} {p1} {p2})

----------------------------------

-- Recursor to map the homotopy in the higher inductive type R to the Universe

rec-hom : {l : Nat} → {i : Fin l} →
          {C : Set} →
          (c : C) →
          (p q : c ≡ c) →
          (c-paillier-hom : p ≡ q) → (d : I × ((tab l) ≡ (tab l))) → c ≡ c
rec-hom {l} {i} c p q c-paillier-hom (s , x) = if s ==I zer then p else q


postulate
  βrec-hom : {l : Nat}  → {i : Fin l} →
             {C : Set} →
             (c : C) →
             (p q : c ≡ c) →
             (c-paillier-hom : (p ≡ q)) →
             ap (rec-hom {l} {i} c p q c-paillier-hom) (paillier-hom' {l} {i}) ≡ c-paillier-hom

-- homotopies :

{-
  Let f : paillier-encrypt
      g : crypt-increment-100
      ! f : paillier-decrypt
      h : increment-100

  To prove:
      ∀(x : A) → (f ∘ g ∘ (! f)) x ≡ h x
-}

postulate
  paillier-homomorphism : {p q l : Nat} → (i : Fin l) → (v : Vec Int l) → (paillier-decrypt p q (crypt-increment-100 p q i (paillier-encrypt p q v))) ≡ (increment-100 i v)
  !paillier-homomorphism : {p q l : Nat} → (i : Fin l) → (v : Vec Int l) → (paillier-decrypt p q (crypt-decrement-100 p q i (paillier-encrypt p q v))) ≡ (decrement-100 i v)


f-pail-hom : {p q l : Nat} → (i : Fin l) → Vec Int l → Vec Int l
f-pail-hom {p} {q} {l} i = (paillier-decrypt p q) ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)

g-pail-hom : {p q l : Nat} → (i : Fin l) → Vec Int l → Vec Int l
g-pail-hom {p} {q} {l} i = (paillier-decrypt p q) ○ (crypt-decrement-100 p q i) ○ (paillier-encrypt p q)


postulate
  α-pail-hom : {p q l : Nat} → (i : Fin l) → (v : Vec Int l) → (f-pail-hom {p} {q} {l} i (g-pail-hom {p} {q} {l} i v)) ≡ v
  β-pail-hom : {p q l : Nat} → (i : Fin l) → (v : Vec Int l) → (g-pail-hom {p} {q} {l} i (f-pail-hom {p} {q} {l} i v)) ≡ v


pail-hom-equiv≃ : {p q l : Nat} → (i : Fin l) → (Vec Int l) ≃ (Vec Int l)
pail-hom-equiv≃ {p} {q} {l} i = f-pail-hom {p} {q} i , equiv₁ (mkqinv (g-pail-hom {p} {q} i) (α-pail-hom {p} {q} i) (β-pail-hom {p} {q} i))

pail-hom-path : {p q l : Nat} → {i : Fin l} → (Vec Int l) ≡ (Vec Int l)
pail-hom-path {p} {q} {l} {i} with univalence 
... | (_ , eq) = isequiv.g eq (pail-hom-equiv≃ {p} {q} {l} i)

----------------------------------------------

f-eq-hom : {p q l : Nat} → (i : Fin l) → (v : Vec Int l) → (f-pail-hom {p} {q} {l} i v) ≡ (increment-100 i v)
f-eq-hom {p} {q} () []
f-eq-hom {p} {q} zero (x :: xs) = (begin
                                  f-pail-hom {p} {q} zero (x :: xs) ≡⟨ refl _ ⟩
                                  ((paillier-decrypt p q) ○ (crypt-increment-100 p q zero) ○ (paillier-encrypt p q)) (x :: xs) ≡⟨ refl _ ⟩
                                  (paillier-decrypt p q (crypt-increment-100 p q zero (paillier-encrypt p q (x :: xs)))) ≡⟨ paillier-homomorphism {p} {q} zero (x :: xs) ⟩
                                  (increment-100 zero (x :: xs)) ∎) 
f-eq-hom {p} {q} (suc i) (x :: xs) = (begin
                                  f-pail-hom {p} {q} (suc i) (x :: xs) ≡⟨ refl _ ⟩
                                  ((paillier-decrypt p q) ○ (crypt-increment-100 p q (suc i)) ○ (paillier-encrypt p q)) (x :: xs) ≡⟨ refl _ ⟩
                                  (paillier-decrypt p q (crypt-increment-100 p q (suc i) (paillier-encrypt p q (x :: xs)))) ≡⟨ paillier-homomorphism {p} {q} (suc i) (x :: xs) ⟩
                                  (increment-100 (suc i) (x :: xs)) ∎)


g-eq-hom : {p q l : Nat} → (i : Fin l) → (v : Vec Int l) → (g-pail-hom {p} {q} {l} i v) ≡ (decrement-100 i v)
g-eq-hom {p} {q} () []
g-eq-hom {p} {q} zero (x :: xs) = (begin
                                  g-pail-hom {p} {q} zero (x :: xs) ≡⟨ refl _ ⟩
                                  ((paillier-decrypt p q) ○ (crypt-decrement-100 p q zero) ○ (paillier-encrypt p q)) (x :: xs) ≡⟨ refl _ ⟩
                                  (paillier-decrypt p q (crypt-decrement-100 p q zero (paillier-encrypt p q (x :: xs)))) ≡⟨ !paillier-homomorphism {p} {q} zero (x :: xs) ⟩
                                  (decrement-100 zero (x :: xs)) ∎)
g-eq-hom {p} {q} (suc i) (x :: xs) = (begin
                                  g-pail-hom {p} {q} (suc i) (x :: xs) ≡⟨ refl _ ⟩
                                  ((paillier-decrypt p q) ○ (crypt-decrement-100 p q (suc i)) ○ (paillier-encrypt p q)) (x :: xs) ≡⟨ refl _ ⟩
                                  (paillier-decrypt p q (crypt-decrement-100 p q (suc i) (paillier-encrypt p q (x :: xs)))) ≡⟨ !paillier-homomorphism {p} {q} (suc i) (x :: xs) ⟩
                                  (decrement-100 (suc i) (x :: xs)) ∎)

-----------------------------------------------

postulate
  paillier-homomorphism-path : {p q l : Nat} → (i : Fin l) → (pail-hom-path {p} {q} {l} {i}) ≡ (inc-path i)


I-hom : {p q l : Nat} → {i : Fin l} → I × ((tab l) ≡ (tab l)) → Vec Int l ≡ Vec Int l
I-hom {p} {q} {l} {i} = rec-hom {l} {i}
                                (Vec Int l)
                                (pail-hom-path {p} {q} {l} {i})
                                (inc-path i)
                                (paillier-homomorphism-path {p} {q} {l} i)

I-hom[paillier] : {p q l : Nat} → {i : Fin l} → ap (I-hom {p} {q} {l} {i}) (paillier-hom' {l} {i}) ≡ (paillier-homomorphism-path {p} {q} {l} i)
I-hom[paillier] {p} {q} {l} {i} = βrec-hom {l} {i}
                                           (Vec Int l)
                                           (pail-hom-path {p} {q} {l} {i})
                                           (inc-path i)
                                           (paillier-homomorphism-path {p} {q} {l} i)
