{-# OPTIONS --type-in-type --without-K #-}

open import Function renaming (_∘_ to _○_)
open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv

module CryptDB_HoTT.cryptography.increment-path where

--  increments the given vector by 100

increment-100 : {l : Nat} → (i : Fin l) → Vec Int l → Vec Int l
increment-100 () []
increment-100 zero (x :: xs) = (x + 100) :: xs
increment-100 (suc i) (x :: xs) = x :: (increment-100 i xs)

decrement-100 : {l : Nat} → (i : Fin l) → Vec Int l → Vec Int l
decrement-100 () []
decrement-100 zero (x :: xs) = (x - 100) :: xs
decrement-100 (suc i) (x :: xs) = x :: (decrement-100 i xs)

postulate
  sub-add-assoc : (x y : Nat) → ((x - y) + y) ≡ (x + (y - y))
  add-sub-assoc : (x y : Nat) → ((x + y) - y) ≡ (x + (y - y))
  sub-0 : (x : Nat) → x - 0 ≡ x
  sub-n : (x : Nat) → x - x ≡ 0

add-0 : (x : Nat) → x + 0 ≡ x
add-0 = indNat (λ x → (x + 0) ≡ x)
               (refl _)
               (λ x p → ap suc p)


add-sub-n : (y x : Nat) → ((x - y) + y) ≡ x
add-sub-n = indNat (λ y → (x : Nat) → ((x - y) +  y) ≡ x)
                    (λ x → (begin
                              x - 0 + 0 ≡⟨ ap (λ x1 → x1 + 0) (sub-0 x) ⟩
                              x + 0 ≡⟨ add-0 x ⟩
                              x ∎))
                    (λ y p x → (begin
                                  x - suc y + suc y ≡⟨ sub-add-assoc x (suc y) ⟩
                                  x + (suc y - suc y) ≡⟨ ap (λ y1 → x + y1) (sub-n (suc y)) ⟩
                                  x + 0 ≡⟨ add-0 x ⟩
                                  x ∎))


inc-dec-inv : {l : Nat} → (i : Fin l) → (vec : Vec Int l) → (increment-100 i (decrement-100 i vec) ≡ vec)
inc-dec-inv () []
inc-dec-inv zero (x :: xs) = (begin
                               (increment-100 zero (decrement-100 zero (x :: xs))) ≡⟨ refl _ ⟩
                               (increment-100 zero ((x - 100) :: xs)) ≡⟨ refl _ ⟩
                               (x - 100 + 100) :: xs ≡⟨ ap (λ x1 → x1 :: xs) (add-sub-n 100 x) ⟩
                               (x :: xs) ∎)
inc-dec-inv (suc i) (x :: xs) = ap (λ xs' → x :: xs') (inc-dec-inv i xs)

dec-inc-inv : {l : Nat} → (i : Fin l) → (vec : Vec Int l) → (decrement-100 i (increment-100 i vec) ≡ vec)
dec-inc-inv () []
dec-inc-inv zero (x :: xs) = (begin
                               (decrement-100 zero (increment-100 zero (x :: xs))) ≡⟨ refl _ ⟩
                               (decrement-100 zero ((x + 100) :: xs)) ≡⟨ refl _ ⟩
                               (x + 100 - 100) :: xs ≡⟨ ap (λ x1 → x1 :: xs) (add-sub-assoc x 100) ⟩
                               (x + (100 - 100)) :: xs ≡⟨ refl _ ⟩
                               (x + 0) :: xs ≡⟨ ap (λ x1 → x1 :: xs) (add-0 x) ⟩
                               (x :: xs) ∎)
dec-inc-inv (suc i) (x :: xs) = ap (λ xs' → x :: xs') (dec-inc-inv i xs)

f∘g : {l : Nat} → (i : Fin l) → Vec Int l → Vec Int l
f∘g {l} i = (increment-100 i) ○ (decrement-100 i)

α : {l : Nat} → (i : Fin l) → (vec : Vec Int l) → (f∘g {l} i vec) ≡ vec
α () []
α zero (x :: xs) = begin
                     f∘g zero (x :: xs) ≡⟨ refl _ ⟩
                     ((increment-100 zero) ○ (decrement-100 zero)) (x :: xs) ≡⟨ refl _ ⟩
                     (increment-100 zero (decrement-100 zero (x :: xs))) ≡⟨ inc-dec-inv zero (x :: xs) ⟩
                     (x :: xs ∎) 
α (suc i) (x :: xs) = ap (λ xs' → x :: xs') (α i xs)

g∘f : {l : Nat} → (i : Fin l) → Vec Int l → Vec Int l
g∘f {l} i = (decrement-100 i) ○ (increment-100 i)

β : {l : Nat} → (i : Fin l) → (vec : Vec Int l) → (g∘f {l} i vec) ≡ vec
β () []
β zero (x :: xs) = begin
                     g∘f zero (x :: xs) ≡⟨ refl _ ⟩
                     ((decrement-100 zero) ○ (increment-100 zero)) (x :: xs) ≡⟨ refl _ ⟩
                     (decrement-100 zero (increment-100 zero (x :: xs))) ≡⟨ dec-inc-inv zero (x :: xs) ⟩
                     (x :: xs ∎)
β (suc i) (x :: xs) = ap (λ xs' → x :: xs') (β i xs)


inc-equiv≃ : {l : Nat} → (i : Fin l) → (Vec Int l ≃ Vec Int l)
inc-equiv≃ {l} i = increment-100 i , equiv₁ (mkqinv (decrement-100 i) (α i) (β i))

inc-path : {l : Nat} → (i : Fin l) → (Vec Int l ≡ Vec Int l)
inc-path {l} i with univalence 
... | (_ , eq) = isequiv.g eq (inc-equiv≃ {l} i)
