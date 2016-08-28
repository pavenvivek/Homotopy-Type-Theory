{-# OPTIONS --type-in-type --without-K #-}

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import CryptDB_HoTT.agda_lib.Char
open import CryptDB_HoTT.agda_lib.String
open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Equiv
open import CryptDB_HoTT.agda_lib.Vector

module CryptDB_HoTT.partial_equiv_old where
  
  module hit where

    private
      data #R : Set where
        #tab_ : (l : Nat) → #R
        #tab_↔_ : (l : Nat) → (s : String) → #R

    R : Set
    R = #R

    tab_ : (l : Nat) → R
    tab_ = #tab_

    tab_↔_ : (l : Nat) → (s : String) → R
    tab_↔_ = #tab_↔_

    postulate
      addP2 : {l : Nat} → (str : String) → (tab l ↔ str) ≡ tab (suc l)
      rmP2 : {l : Nat} → (str : String) → tab (suc l) ≡ (tab l ↔ str)
      enc : {l : Nat} → (str : String) → tab l ≡ (tab l ↔ str)
      dec : {l : Nat} → (str : String) → (tab l ↔ str) ≡ tab l

    rec : {l : Nat} → {C : Set} → (c1 : C) → (c2 : C) → (cadd : c1 ≡ c2) → (crm : c2 ≡ c1) → R → C
    rec c1 c2 cadd crm (#tab l ↔ s) = c1
    rec c1 c2 cadd crm (#tab l) = c2

    postulate
      βrec-add : {l : Nat} {s : String} → {C : Set} → (c1 : C) → (c2 : C) → (cadd : c1 ≡ c2) → 
        ap (rec {l} c1 c2 cadd (! cadd)) (addP2 {l} s) ≡ cadd
      βrec-rm : {l : Nat} {s : String} → {C : Set} → (c1 : C) → (c2 : C) → (crm : c2 ≡ c1) →
        ap (rec {l} c1 c2 (! crm) crm) (rmP2 {l} s) ≡ crm

      βrec-dec : {l : Nat} {s : String} → {C : Set} → (c1 : C) → (c2 : C) → (cdec : c1 ≡ c2) → 
        ap (rec {l} c1 c2 cdec (! cdec)) (dec {l} s) ≡ cdec
      βrec-enc : {l : Nat} {s : String} → {C : Set} → (c1 : C) → (c2 : C) → (cenc : c2 ≡ c1) →
        ap (rec {l} c1 c2 (! cenc) cenc) (enc {l} s) ≡ cenc

    {-
    ind : {l : Nat} {s : String} → {C : R' → Set} → 
      (c1 : C (tab' l)) → (c2 : C (tab' (S l))) →
      (cadd : transport C (addP1 {l} {s}) c1 ≡ c2) →
      (crm : transport C (rmP1 {l} {s}) c2 ≡ c1) →
      (c : R') → C c
    ind c1 c2 cadd crm (tab' l) = c1

    postulate
      βindS¹ : {C : S¹ → Set} → 
        (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
        apd (indS¹ {C} cbase cloop) loop ≡ cloop

    postulate
      βrec'-add : {l : Nat} {s : String} → {C : Set} → (c1 : C) → (c2 : C) → (cadd : c1 == c2) → 
        ap (rec {l} c1 c2 cadd (! cadd)) (addP2 {l} s) == cadd
      βrec'-rm : {l : Nat} {s : String} → {C : Set} → (c1 : C) → (c2 : C) → (crm : c2 == c1) →
        ap (rec {l} c1 c2 (! crm) crm) (rmP2 {l} s) == crm
    -}

    data R' : Set where
      tab'_ : (l : Nat) → R'

    postulate
      addP1 : {l : Nat} → {s : String} → (tab' l) ≡ tab' (suc l)
      rmP1 : {l : Nat} → {s : String} → tab' (suc l) ≡ (tab' l)

    data Patch : Set where
      addP_  : String → Patch

    add-bj : {m : Nat} → (String × Vec String m) → Vec String (suc m)
    add-bj (c , vec) = c :: vec 

    add : {m : Nat} → String → Vec String m → Vec String (suc m)
    add c vec = add-bj (c , vec) 

    head : {m : Nat} → Vec String (suc m) → String
    head (a :: as) = a

    rm-bj : {m : Nat} → Vec String (suc m) → String × Vec String m
    rm-bj (a :: as) = (a , as)

    rm : {m : Nat} → Vec String (suc m) → Vec String m
    rm vec = proj₂ (rm-bj vec)


    add-rm-inv : {m : Nat} → (vec1 : Vec String (suc m)) → (add-bj (rm-bj vec1) ≡ vec1)
    add-rm-inv {m} (a :: as)  = ( add-bj (rm-bj (a :: as)) ≡⟨ refl _ ⟩
                                  add-bj (a , as) ≡⟨ refl _ ⟩
                                  (a :: as) ∎)
    
    rm-add-inv : {m : Nat} → (vec : String × Vec String m) → rm-bj (add-bj vec) ≡ vec
    rm-add-inv (c , []) = ( rm-bj (add-bj (c , [])) ≡⟨ refl _ ⟩
                            rm-bj (c :: []) ≡⟨ refl _ ⟩
                            (c , []) ∎)
    rm-add-inv (c , (a :: as))  = ( rm-bj (add-bj (c , (a :: as))) ≡⟨ refl _ ⟩
                                    rm-bj (c :: (a :: as)) ≡⟨ refl _ ⟩
                                    (c , (a :: as)) ∎)
    
    add-rm-bij≃ : {m : Nat} → (String × Vec String m) ≃ (Vec String (suc m))
    add-rm-bij≃ = add-bj , equiv₁ (mkqinv rm-bj add-rm-inv rm-add-inv)

    add-rm-path : {m : Nat} → (String × Vec String m) ≡ (Vec String (suc m))
    add-rm-path {m} with univalence
    ... | (_ , eq) = isequiv.g eq (add-rm-bij≃ {m})


    rm-add-bij≃ : {m : Nat} → (Vec String (suc m)) ≃ (String × Vec String m)
    rm-add-bij≃ = rm-bj , equiv₁ (mkqinv add-bj rm-add-inv add-rm-inv)

    rm-add-path : {m : Nat} → (Vec String (suc m)) ≡ (String × Vec String m)
    rm-add-path {m} with univalence
    ... | (_ , eq) = isequiv.g eq (rm-add-bij≃ {m})


  open hit

  {-
  I : R → Set
  I (tab l) = Vec String l 
  I (tab l ↔ s) = String × Vec String l
  -}

  I : {l : Nat} {s : String} → R → Set
  I {l} {s} = rec {l} (String × Vec String l) (Vec String (suc l)) (add-rm-path) (rm-add-path)

  I[addP2] : {l : Nat} {s : String} → ap (I {l} {s}) (addP2 {l} s) ≡ (add-rm-path)
  I[addP2] {l} {s} = βrec-add {l} {s} (String × Vec String l) (Vec String (suc l)) (add-rm-path)
  
  I[rmP2] : {l : Nat} {s : String} → ap (I {l} {s}) (rmP2 {l} s) ≡ (rm-add-path)
  I[rmP2] {l} {s} = βrec-rm {l} {s} (String × Vec String l) (Vec String (suc l)) (rm-add-path)

  f : {l : Nat} {s : String} → R → R'
  f {l} {s} = rec {l} (tab' l) (tab' (suc l)) (addP1 {l} {s}) (rmP1 {l} {s})

  f[addP2] : {l : Nat} {s : String} → ap (f {l} {s}) (addP2 {l} s) ≡ (addP1 {l} {s})
  f[addP2] {l} {s} = βrec-add {l} {s} (tab' l) (tab' (suc l)) (addP1 {l} {s})
  
  f[rmP2] : {l : Nat} {s : String} → ap (f {l} {s}) (rmP2 {l} s) ≡ (rmP1 {l} {s})
  f[rmP2] {l} {s} = βrec-rm {l} {s} (tab' l) (tab' (suc l)) (rmP1 {l} {s})


  --- Partial Bijection -start-
  
  encode : {m : Nat} → String → Vec String m → (String × Vec String m)
  encode s vec = (s , vec) 

  decode : {m : Nat} → String × Vec String m → Vec String m
  decode (s , vec) = vec

  postulate -- Assuming (String × Vec String m) and (Vec String m) as Singleton types
    enc-dec-inv' : {m : Nat} → (s : String) → (vec : String × Vec String m) → (encode s (decode vec) ≡ vec)

  enc-dec-inv : {m : Nat} → (vec : String × Vec String m) → (encode (proj₁ vec) (decode vec) ≡ vec)
  enc-dec-inv {m} (a , as)  = ( encode a (decode (a , as)) ≡⟨ refl _ ⟩
                                encode a as ≡⟨ refl _ ⟩
                                (a , as) ∎)

  dec-enc-inv : {m : Nat} → (s : String) → (vec : Vec String m) → decode (encode s vec) ≡ vec
  dec-enc-inv s vec = ( decode (encode s vec) ≡⟨ refl _ ⟩
                        decode (s , vec) ≡⟨ refl _ ⟩
                        vec ∎)

  -- Work around for partial bijection
  enc-dec-bij≃ : {m : Nat} {s : String} → (Vec String m) ≃ (String × Vec String m)
  enc-dec-bij≃ {m} {s} = (encode s) , equiv₁ (mkqinv decode (enc-dec-inv' s) (dec-enc-inv s))

  enc-dec-path : {m : Nat} {s : String} → (Vec String m) ≡ (String × Vec String m)
  enc-dec-path {m} {s} with univalence
  ... | (_ , eq) = isequiv.g eq (enc-dec-bij≃ {m} {s})

  dec-enc-bij≃ : {m : Nat} {s : String} → (String × Vec String m) ≃ (Vec String m)
  dec-enc-bij≃ {m} {s} = decode , equiv₁ (mkqinv (encode s) (dec-enc-inv s) (enc-dec-inv' s))

  dec-enc-path : {m : Nat} {s : String} → (String × Vec String m) ≡ (Vec String m)
  dec-enc-path {m} {s} with univalence
  ... | (_ , eq) = isequiv.g eq (dec-enc-bij≃ {m} {s})


  IPBij : {l : Nat} {s : String} → R → Set
  IPBij {l} {s} = rec {l} (Vec String l) (String × Vec String l) (enc-dec-path {l} {s}) (dec-enc-path {l} {s})

  IPBij[enc] : {l : Nat} {s : String} → ap (IPBij {l} {s}) (enc {l} s) ≡ (dec-enc-path {l} {s})
  IPBij[enc] {l} {s} = βrec-enc {l} {s} (Vec String l) (String × Vec String l) (dec-enc-path {l} {s}) 

  IPBij[dec] : {l : Nat} {s : String} → ap (IPBij {l} {s}) (dec {l} s) ≡ (enc-dec-path {l} {s})
  IPBij[dec] {l} {s} = βrec-dec {l} {s} (Vec String l) (String × Vec String l) (enc-dec-path {l} {s})

  --- Partial Bijection -end-
  
  interp-add : {m : Nat} {s : String} → (patch : (tab m ↔ s) ≡ (tab (suc m))) → (String × Vec String m) → (Vec String (suc m))
  interp-add {m} {s} addP2 = coe' (ap (I {m} {s}) addP2)

  interp-add' : {m : Nat} {s : String} → (patch : (tab m ↔ s) ≡ (tab (suc m))) → (Vec String m → Vec String (suc m))
  interp-add' {m} {s} addP2 = add s
  
  coe-biject' : {A : Set} {l : Nat} → (Vec A (suc l) ≡ (String × Vec A l)) → (Vec A (suc l) ≃ (String × Vec A l) )
  coe-biject' path with univalence 
  ... | (f , eq) = f path

  coe'' : {A : Set} {l : Nat} → ((Vec A (suc l)) ≡ (String × Vec A l)) → (Vec A (suc l) → (String × Vec A l))
  coe'' path = fst (coe-biject' path)

  interp-rm : {m : Nat} {s : String} → (patch : (tab (suc m)) ≡ (tab m ↔ s)) → (Vec String (suc m)) → (String × Vec String m)
  interp-rm {m} {s} rmP2 = coe'' (ap (I {m} {s}) rmP2)

  interp-rm' : {m : Nat} {s : String} → (patch : (tab (suc m)) ≡ (tab m ↔ s)) → (Vec String (suc m) → Vec String m)
  interp-rm' {m} {s} rmP2 = rm

  example : Vec String 3
  example = ("god" :: ("agda" :: ("you" :: [])))

  add-rm : {m : Nat} {s : String} → Vec String m → Vec String m
  add-rm {m} {s} vec = rm (add s vec)
  
  interp-add-rm' : {m : Nat} {s : String} → (patch : (tab m ↔ s) ≡ (tab m ↔ s)) → Vec String m → Vec String m
  interp-add-rm' {m} {s} patch vec = (rm (add s vec)) -- add s

  fpatch4 : {m : Nat} {s1 s2 : String} → Vec String m → Vec String (suc (suc m))
  fpatch4 {m} {s1} {s2} vec = (add s2 (add s1 vec))

  interp-patch4 : {m : Nat} {s1 s2 : String} → (patch : (tab m ↔ s1) ≡ (tab (suc (suc m)))) → Vec String m → Vec String (suc (suc m))
  interp-patch4 {m} {s1} {s2} patch vec = fpatch4 {m} {s1} {s2} vec

  patch1 = (addP2 {3} "hello") ∘ (rmP2 {3} "hello") ∘ (dec {3} "hello") ∘ (enc {3} "hai") ∘ (addP2 {3} "hai")
  patch2 = rmP2 {2} ""
  patch3 = (addP2 {3} "hello") ∘ (rmP2 {3} "hello")
  patch4 = (addP2 {3} "hello") ∘ (enc {4} "hai") ∘ (addP2 {4} "hai")

  {-
     run commands:
     ------------
       - (interp-add' patch1) example
       - (interp-rm' patch2) example
       - (interp-add-rm' patch3) example
  -} 

