{-# OPTIONS --type-in-type --without-K #-}

open import lib.Char --hiding (id ; _∘_ ; !)
open import lib.String
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import lib.Nat --Data.Nat using (ℕ; suc; _+_; _*_)
-- open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product using (_×_; _,_)
open import lib.First2

module programming.test_str where


  data Vec (A : Set) : Nat → Set where
    []   : Vec A 0
    _::_ : {n : Nat} → A → Vec A n → Vec A (S n)

  module R (n : Nat) where

    data Patch : Set where
      addP_  : String → Patch

    prj₁ : ∀ {A B : Set} → A × B → A
    prj₁ (a , b) = a

    prj₂ : ∀ {A B : Set} → A × B → B
    prj₂ (a , b) = b

    add-bj : {m : Nat} → (String × Vec String m) → Vec String (S m)
    add-bj (c , vec) = c :: vec 

    add : {m : Nat} → String → Vec String m → Vec String (S m)
    add c vec = add-bj (c , vec) 

    head : {m : Nat} → Vec String (S m) → String
    head (a :: as) = a

    rm-bj : {m : Nat} → Vec String (S m) → String × Vec String m
    rm-bj (a :: as) = (a , as)

    rm : {m : Nat} → Vec String (S m) → Vec String m
    rm vec = prj₂ (rm-bj vec)


    add-rm-inv : {m : Nat} → (vec1 : Vec String (S m)) → (add-bj (rm-bj vec1) == vec1)
    add-rm-inv {m} (a :: as)  = ( add-bj (rm-bj (a :: as)) ≡⟨ id ⟩
                                  add-bj (a , as) ≡⟨ id ⟩
                                  (a :: as) ∎)
    
    rm-add-inv : {m : Nat} → (vec : String × Vec String m) → rm-bj (add-bj vec) == vec
    rm-add-inv (c , []) = ( rm-bj (add-bj (c , [])) ≡⟨ id ⟩
                            rm-bj (c :: []) ≡⟨ id ⟩
                            (c , []) ∎)
    rm-add-inv (c , (a :: as))  = ( rm-bj (add-bj (c , (a :: as))) ≡⟨ id ⟩
                                    rm-bj (c :: (a :: as)) ≡⟨ id ⟩
                                    (c , (a :: as)) ∎)
    
    -- add-rm-bij≃ : {m : Nat} → (c : Char) → Equiv (Vec Char m) (Vec Char (S m))
    -- add-rm-bij≃ c = improve (hequiv (add c) rm (rm-add-inv c) add-rm-inv)

    add-rm-bij≃ : {m : Nat} → Equiv (String × Vec String m) (Vec String (S m))
    add-rm-bij≃ = improve (hequiv add-bj rm-bj rm-add-inv add-rm-inv)

    add-rm-ua : {m : Nat} → Equiv (String × Vec String m) (Vec String (S m)) → Path (String × Vec String m) (Vec String (S m))
    add-rm-ua add-rm-bij≃ = ua add-rm-bij≃

    interp : {m : Nat} → Patch → (Vec String m → Vec String (S m)) × 
                                    (Vec String (S m) → Vec String m)
    interp (addP a) = add a , rm

  module Test where
    module TestR = R 4
    open TestR public

    example : Vec String 3
    example = "god" :: ("agda" :: ("you" :: []))

    patch = addP "hello"

  {-
    run commands:
    ------------
      - prj₁ (interp patch) example
      - prj₂ (interp patch) example
      - prj₂ (interp patch) (prj₁ (interp patch) example)
  -}

  open Test


