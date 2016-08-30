{-# OPTIONS --type-in-type --without-K #-}

open import Data.Bool
open import Function renaming (_∘_ to _○_)
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

  example : Vec Bool 3
  example = true :: (false :: (true :: []))

  test-1 : Vec Bool 3
  test-1 = interp (switch {3}) example

  postulate
    by-defn : (coe-biject (switch-path {3})) ≡ (switch-bij≃ {3})

  test-1-pf : test-1 ≡ (false :: (false :: (true :: [])))
  test-1-pf = (begin
                test-1 ≡⟨ refl _ ⟩
                interp (switch {3}) (true :: (false :: (true :: []))) ≡⟨ refl _ ⟩
                (coe' (ap (I {3}) (switch {3}))) (true :: (false :: (true :: []))) ≡⟨ ap (λ x → coe' x (true :: (false :: (true :: [])))) (I[switch] {3}) ⟩
                (coe' (switch-path {3})) (true :: (false :: (true :: []))) ≡⟨ refl _ ⟩
                (fst (coe-biject (switch-path {3}))) (true :: (false :: (true :: []))) ≡⟨ ap (λ x → fst x (true :: (false :: (true :: [])))) by-defn ⟩
                (fst (switch-bij≃ {3})) (true :: (false :: (true :: []))) ≡⟨ refl _ ⟩
                (switchB {3}) (true :: (false :: (true :: []))) ≡⟨ refl _ ⟩
                (false :: (false :: (true :: []))) ∎)
                
  interp' : {m : Nat} → (query : (tab m) ≡ (tab m)) → (Vec Bool m) ≃ (Vec Bool m)
  interp' {m} switch = coe-biject (ap (I {m}) switch)

  postulate
    α3 : {A B C : Set} → (f1 : A → B) → (f2 : B → C) → (g1 : B → A) → (g2 : C → B) → ((f2 ○ f1) ○ (g1 ○ g2)) ∼ id
    β3 : {A B C : Set} → (f1 : A → B) → (f2 : B → C) → (h1 : B → A) → (h2 : C → B) → ((h1 ○ h2) ○ (f2 ○ f1)) ∼ id

  _∘E_ : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
  _∘E_ (f1 , mkisequiv g1 α1 h1 β1) (f2 , mkisequiv g2 α2 h2 β2)  = f2 ○ f1 , mkisequiv (g1 ○ g2) (α3 f1 f2 g1 g2) (h1 ○ h2) (β3 f1 f2 h1 h2)

  postulate
    coe-biject-comp : {m : Nat} → (p q : (tab m) ≡ (tab m)) → coe-biject (ap (I {m}) p ∘ ap I q) ≡ coe-biject (ap I p) ∘E coe-biject (ap I q)

  interp'-eqpf : {m : Nat} → (p q : (tab m) ≡ (tab m)) → interp' (p ∘ q) ≡ (interp' p) ∘E (interp' q)
  interp'-eqpf {m} p q = begin
                           interp' (p ∘ q) ≡⟨ refl _ ⟩
                           coe-biject (ap I (p ∘ q)) ≡⟨ ap (λ x → coe-biject x) (apfTrans I p q) ⟩
                           coe-biject (ap I p ∘ ap I q) ≡⟨ coe-biject-comp p q ⟩
                           coe-biject (ap I p) ∘E coe-biject (ap I q) ≡⟨ refl _ ⟩
                           (interp' p ∘E interp' q ∎)
