{-# OPTIONS --type-in-type --without-K #-}

open import Data.Bool
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv

module CryptDB_HoTT.bool_hit where

  module hit where

    data #R : Set where
      #tab_ : (l : Nat) → #R

    R : Set
    R = #R

    tab_ : (l : Nat) → R
    tab_ = #tab_

    postulate
      switch : {l : Nat} → (tab l) ≡ (tab l)

    switchB : {m : Nat} → Vec Bool m → Vec Bool m
    switchB [] = [] 
    switchB (c :: vec) = (if c then false else true) :: vec 

    switch-inv : {m : Nat} → (vec : Vec Bool m) → (switchB (switchB vec) ≡ vec)
    switch-inv {m} = indVec (λ v → (switchB (switchB v) ≡ v))
                                     (refl _)
                                     (λ b vecb p → indBool (λ b1 → switchB (switchB (b1 :: vecb)) ≡ b1 :: vecb)
                                                            ( switchB (switchB (false :: vecb)) ≡⟨ refl _ ⟩
                                                              switchB (true :: vecb) ≡⟨ refl _ ⟩
                                                              (false :: vecb ∎))
                                                            ( switchB (switchB (true :: vecb)) ≡⟨ refl _ ⟩
                                                              switchB (false :: vecb) ≡⟨ refl _ ⟩
                                                              (true :: vecb ∎))
                                                             b)
                                     
    
    switch-bij≃ : {m : Nat} → (Vec Bool m) ≃ (Vec Bool m)
    switch-bij≃ = switchB , equiv₁ (mkqinv switchB switch-inv switch-inv)

    switch-path : {m : Nat} → (Vec Bool m) ≡ (Vec Bool m)
    switch-path {m} with univalence
    ... | (_ , eq) = isequiv.g eq (switch-bij≃ {m})

  open hit

  rec : {l : Nat} → {C : Set} → (c : C) → (cswitch : c ≡ c) → R → C
  rec c cswitch (#tab l) = c

  postulate
    βrec-switch : {l : Nat} → {C : Set} → (c : C) → (cswitch : c ≡ c) → 
      ap (rec {l} c cswitch) (switch {l}) ≡ cswitch

  {-
  ind : {l : Nat} → {C : R → Set} → 
        (c : C (tab l)) →
        (cswitch : transport C (switch {l}) c ≡ c) →
        (a : R) → C a
  ind {l} c cswitch (#tab _) = c

  postulate
    βindS¹ : {C : S¹ → Set} → 
      (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
      apd (indS¹ {C} cbase cloop) loop ≡ cloop
  -}

  I : {l : Nat} → R → Set
  I {l} = rec {l} (Vec Bool l) (switch-path {l})

  I[switch] : {l : Nat} → ap (I {l}) (switch {l}) ≡ (switch-path {l})
  I[switch] {l} = βrec-switch {l} (Vec Bool l) (switch-path {l})
  
  
  interp : {m : Nat} → (patch : (tab m) ≡ (tab m)) → (Vec Bool m) → (Vec Bool m)
  interp {m} switch = coe' (ap (I {m}) switch)

  interp' : {m : Nat} → (patch : (tab m) ≡ (tab m)) → (Vec Bool m) → (Vec Bool m)
  interp' {m} switch = switchB
  

  example : Vec Bool 3
  example = true :: (false :: (true :: []))

  patch1 = (switch {3})

  {-
     run commands:
     ------------
       - (interp' patch1) example
  -} 
