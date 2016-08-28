{-# OPTIONS --type-in-type --without-K #-}

open import Data.Product using (_×_; _,_)

open import CryptDB_HoTT.agda_lib.Char
open import CryptDB_HoTT.agda_lib.String
open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Equiv
open import CryptDB_HoTT.agda_lib.Vector

module CryptDB_HoTT.db_homotopy_old where

  idp = \{A}{x} → refl {A} x
   
  data Fin : Nat → Set where
    Z : ∀ {n} → Fin (suc n) 
    S : ∀ {n} → Fin n → Fin (suc n)
    -- fin-abort : Fin 0

  data _≤'_ : {l : Nat} → Fin l → Fin l → Set where
    z≤n : ∀ {l : Nat} {n : Fin (suc l)}                 → Z ≤' n
    s≤s : ∀ {l : Nat} {m n : Fin l} (m≤n : m ≤' n) → (S m) ≤' (S n)

  data _≤_ : Nat → Nat → Set where
    z≤n : ∀ {n : Nat}                 → 0 ≤ n
    s≤s : ∀ {m n : Nat} (m≤n : m ≤ n) → (suc m) ≤ (suc n)
  
  module hit where

    _≥_ : Nat → Nat → Set
    m ≥ n = n ≤ m

    _<'_ : {l : Nat} → Fin l → Fin (suc l) → Set
    m <' n = (S m) ≤' n

    _<s_ : Nat → Nat → Set
    m <s n = suc m ≤ n

    _>s_ : Nat → Nat → Set
    m >s n = n <s m

    toNat : ∀ {n} → Fin n → Nat
    toNat Z    = 0
    toNat (S i) = suc (toNat i)

    data ⊥ : Set where 

    abort : {A : Set} → ⊥ → A
    abort ()

    data Bool : Set where
      true false : Bool

    postulate
      fin0 : ⊥
      
    fromNat : {m : Nat} → (n : Nat) → Fin m
    fromNat {0} _ = (abort fin0)
    fromNat {suc m} 0 = Z
    fromNat {suc m} (suc n) = S (fromNat {m} n)

    Fin′ : ∀ {n} → Fin n → Set
    Fin′ i = Fin (toNat i)
{-
    _-_ : Nat → Nat → Nat
    m  - Z  = m
    Z  - S n = Z
    S m - S n = m - n
-}

{-    infixl 6 _-_

    _-_ : ∀ {m} (i : Fin m) (j : Fin′ (S i)) → Fin (m ∸ toNat j)
    i     - Z   = i
    Z  - S ()
    S i - S j  = i - j

    _+_ : Nat → Nat → Nat
    0  + n = n
    (S m) + n = S (m + n)
-}
    raise : ∀ {m} n → Fin m → Fin (n + m)
    raise 0    i = i
    raise (suc n) i = S (raise n i)

    reduce≥ : ∀ {m n} (i : Fin (m + n)) (i≥m : toNat i ≥ m) → Fin n
    reduce≥ {0}  i       i≥m       = i
    reduce≥ {suc m} Z    ()
    reduce≥ {suc m} (S i) (s≤s i≥m) = reduce≥ i i≥m

    reduce1 : ∀ {n} (i : Fin (1 + n)) (i≥1 : toNat i ≥ 1) → Fin n
    reduce1 i i≥1 = reduce≥ i i≥1

    pred : Nat → Nat
    pred 0    = 0
    pred (suc n) = n

    private
      data #R : Set where
        #tab_ : (l : Nat) → #R
        #tab_↔_↔_ : (l : Nat) → (s : String) → (n : Fin l) → #R

    R : Set
    R = #R

    tab_ : (l : Nat) → R
    tab_ = #tab_

    tab_↔_↔_ : (l : Nat) → (s : String) → (n : Fin l) → R
    tab_↔_↔_ = #tab_↔_↔_

    postulate
      addP2 : {l : Nat} → (n : Fin l) → (str : String) → (tab l ↔ str ↔ n) ≡ tab (suc l)
      rmP2 : {l : Nat} → (n : Fin l) → (str : String) → tab (suc l) ≡ (tab l ↔ str ↔ n)
      enc : {l : Nat} → (n : Fin l) → (str : String) → tab l ≡ (tab l ↔ str ↔ n)
      dec : {l : Nat} → (n : Fin l) → (str : String) → (tab l ↔ str ↔ n) ≡ tab l


    rec : {l : Nat} → {C : Set} → (c1 : C) → (c2 : C) → (cadd : c1 ≡ c2) → (crm : c2 ≡ c1) → R → C
    rec c1 c2 cadd crm (#tab l ↔ s ↔ n) = c1
    rec c1 c2 cadd crm (#tab l) = c2

    postulate
      βrec-add : {l : Nat} {s : String} → (n : Fin l) → {C : Set} → (c1 : C) → (c2 : C) → (cadd : c1 ≡ c2) → 
        ap (rec {l} c1 c2 cadd (! cadd)) (addP2 {l} n s) ≡ cadd
      βrec-rm : {l : Nat} {s : String} → (n : Fin l) → {C : Set} → (c1 : C) → (c2 : C) → (crm : c2 ≡ c1) →
        ap (rec {l} c1 c2 (! crm) crm) (rmP2 {l} n s) ≡ crm

   
      βrec-dec : {l : Nat} {s : String} → (n : Fin l) → {C : Set} → (c1 : C) → (c2 : C) → (cdec : c1 ≡ c2) → 
        ap (rec {l} c1 c2 cdec (! cdec)) (dec {l} n s) ≡ cdec
      βrec-enc : {l : Nat} {s : String} → (n : Fin l) → {C : Set} → (c1 : C) → (c2 : C) → (cenc : c2 ≡ c1) →
        ap (rec {l} c1 c2 (! cenc) cenc) (enc {l} n s) ≡ cenc
   
    
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

    -- patch law
    
    postulate
      -- (l1 < l2) → (add l2 str2) ∘ (add l1 str1) ≡ (add l1 str1) ∘ (add (l2 - 1) str2) 
      add-patch-commute1 : {l : Nat} → (l1 : Fin l) → (l2 : Fin (suc l)) → (str1 str2 : String) → (p : (toNat l1) <s (toNat l2)) →
                           (enc {l} l1 str1) ∘ (addP2 {l} l1 str1) ∘ (enc {suc l} l2 str2) ∘ (addP2 {(suc l)} l2 str2)   ≡
                           ((enc {l} (fromNat {l} ((toNat {suc l} l2) - 1)) str2) ∘ (addP2 {l} (fromNat {l} ((toNat {suc l} l2) - 1)) str2) ∘
                           (enc {suc l} (fromNat {suc l} (toNat {l} l1)) str1) ∘ (addP2 {(suc l)} (fromNat {suc l} (toNat {l} l1)) str1))

      -- (l1 > l2) → (add l2 str2) ∘ (add l1 str1) ≡ (add (l1 + 1) str1) ∘ (add l2 str2)
      add-patch-commute2 : {l : Nat} → (l1 : Fin l) → (l2 : Fin (suc l)) → (str1 str2 : String) → (p : (toNat l1) >s (toNat l2)) →
                           (enc {l} l1 str1) ∘ (addP2 {l} l1 str1) ∘ (enc {suc l} l2 str2) ∘ (addP2 {(suc l)} l2 str2)  ≡
                           ((enc {l} (fromNat {l} (toNat {suc l} l2)) str2) ∘ (addP2 {l} (fromNat {l} (toNat {suc l} l2)) str2) ∘
                           (enc {suc l} (fromNat {suc l} ((toNat {l} l1) + 1)) str1) ∘ (addP2 {(suc l)} (fromNat {suc l} ((toNat {l} l1) + 1)) str1))

      -- (rm l1 str1) ∘ (add l1 str1) ≡ (rm l1 str2) ∘ (add l1 str2)
      add-rm-patch-commute : {l : Nat} → (l1 : Fin l) → (str1 str2 : String) →
                             (enc {l} l1 str1) ∘ (addP2 {l} l1 str1) ∘ (rmP2 {l} l1 str1) ∘ (dec {(l)} l1 str1) ≡
                             (enc {l} l1 str2) ∘ (addP2 {l} l1 str2) ∘ (rmP2 {l} l1 str2) ∘ (dec {(l)} l1 str2)
                              
    prj₁ : ∀ {A B : Set} → A × B → A
    prj₁ (a , b) = a

    prj₂ : ∀ {A B : Set} → A × B → B
    prj₂ (a , b) = b

    add-bj' : {m : Nat} → ((String × Fin m) × Vec String m) →  Vec String (suc m)
    add-bj' ((s , _) , []) = s :: []
    add-bj' ((s , Z) , (a :: as)) = (s :: (a :: as))
    add-bj' ((s , (S i)) , (a :: as)) = (a :: (add-bj' ((s , i) , as)))

    add-bj : {m : Nat} → ((String × Fin m) × Vec String m) →  (Fin m × Vec String (suc m))
    add-bj vec  = ((prj₂ (prj₁ vec)) , add-bj' vec)

    add : {m : Nat} → (i : Fin m) → String → Vec String m → Vec String (suc m)
    add i s vec = prj₂ (add-bj ((s , i) , vec)) 

    head : {m : Nat} → Vec String (suc m) → String
    head (a :: as) = a

    rm-bj' : {m : Nat} → Fin m → Vec String (suc m) → (String × Vec String m)
    rm-bj' Z (a :: as) = (a , as)
    rm-bj' (S i) (a :: as) = ((prj₁ (rm-bj' i as)) , (a :: (prj₂ (rm-bj' i as))))

    rm-bj : {m : Nat} → (Fin m × Vec String (suc m)) → ((String × Fin m) × Vec String m)
    rm-bj vec = (((prj₁ (rm-bj' (prj₁ vec) (prj₂ vec))) , (prj₁ vec)) , (prj₂ (rm-bj' (prj₁ vec) (prj₂ vec))))

    rm : {m : Nat} → (i : Fin m) → Vec String (suc m) → Vec String m
    rm i vec = prj₂ (rm-bj (i , vec))

    add-rm-inv : {m : Nat} → (vec1 : Fin m × Vec String (suc m)) → (add-bj (rm-bj vec1) ≡ vec1)
    add-rm-inv (Z , (a :: (a1 :: as)))  = ( add-bj (rm-bj (Z , (a :: (a1 :: as)))) ≡⟨ refl _ ⟩
                                            add-bj ((a , Z) , (a1 :: as)) ≡⟨ refl _ ⟩
                                            (Z , (a :: (a1 :: as))) ∎)
    add-rm-inv ((S i) , (a :: (a1 :: as))) = ap (λ x → ((S (prj₁ x)) , (a :: (prj₂ x)))) (add-rm-inv (i , (a1 :: as)))

    rm-add-inv : {m : Nat} → (vec : ((String × Fin m) × Vec String m)) → (rm-bj (add-bj vec) ≡ vec)
    rm-add-inv ((c , Z) , (a :: as)) = ( rm-bj (add-bj ((c , Z) , (a :: as))) ≡⟨ refl _ ⟩
                                         rm-bj (Z , (c :: (a :: as))) ≡⟨ refl _ ⟩
                                         ((c , Z) , (a :: as)) ∎)
    rm-add-inv ((c , (S i)) , (a :: as))  = ap (λ x → (((prj₁ (prj₁ x)) , (S (prj₂ (prj₁ x)))) , (a :: (prj₂ x)))) (rm-add-inv ((c , i) , as))
    

    add-rm-bij≃ : {m : Nat} → ((String × Fin m) × Vec String m) ≃ (Fin m × Vec String (suc m))
    add-rm-bij≃ = add-bj , equiv₁ (mkqinv rm-bj add-rm-inv rm-add-inv)

    add-rm-path : {m : Nat} → ((String × Fin m) × Vec String m) ≡ (Fin m × Vec String (suc m))
    add-rm-path {m} with univalence
    ... | (_ , eq) = isequiv.g eq (add-rm-bij≃ {m})

    rm-add-bij≃ : {m : Nat} → (Fin m × Vec String (suc m)) ≃ ((String × Fin m) × Vec String m)
    rm-add-bij≃ = rm-bj , equiv₁ (mkqinv add-bj rm-add-inv add-rm-inv)

    rm-add-path : {m : Nat} → (Fin m × Vec String (suc m)) ≡ ((String × Fin m) × Vec String m)
    rm-add-path {m} with univalence
    ... | (_ , eq) = isequiv.g eq (rm-add-bij≃ {m})
 

  open hit

  {-
  I : R → Set₁
  I (tab l) = Vec String l 
  I (tab l ↔ s) = String × Vec String l
  -}

  I : {l : Nat} {s : String} → R → Set
  I {l} {s} = rec {l} ((String × Fin l) × Vec String l) (Fin l × (Vec String (suc l))) (add-rm-path) (rm-add-path)

  I[addP2] : {l : Nat} {s : String} → {m : Fin l} → ap (I {l} {s}) (addP2 {l} m s) ≡ (add-rm-path)
  I[addP2] {l} {s} {m} = βrec-add {l} {s} m ((String × Fin l) × Vec String l) (Fin l × (Vec String (suc l))) (add-rm-path)
  
  I[rmP2] : {l : Nat} {s : String} → {m : Fin l} → ap (I {l} {s}) (rmP2 {l} m s) ≡ (rm-add-path)
  I[rmP2] {l} {s} {m} = βrec-rm {l} {s} m ((String × Fin l) × Vec String l) (Fin l × Vec String (suc l)) (rm-add-path)
  
  --- Partial Bijection -start-
  
  encode : {m : Nat} → (i : Fin m) → String → Vec String m → ((String × Fin m) × Vec String m)
  encode {m} i s vec = ((s , i) , vec) 

  decode : {m : Nat} → ((String × Fin m) × Vec String m) → Vec String m
  decode ((s , i) , vec) = vec

  postulate -- Assuming (String × Vec String m) and (Vec String m) as Singleton types
    enc-dec-inv' : {m : Nat} → (i : Fin m) → (s : String) → (vec : ((String × Fin m) × Vec String m)) → (encode i s (decode vec) ≡ vec)

  enc-dec-inv : {m : Nat} → (vec : ((String × Fin m) × Vec String m)) → (encode (prj₂ (prj₁ vec)) (prj₁ (prj₁ vec)) (decode vec) ≡ vec)
  enc-dec-inv {m} ((a , i) , as) = ( encode i a (decode ((a , i) , as)) ≡⟨ refl _ ⟩
                                encode i a as ≡⟨ refl _ ⟩
                                ((a , i) , as) ∎)
  
  dec-enc-inv : {m : Nat} → (i : Fin m) → (s : String) → (vec : Vec String m) → decode (encode i s vec) ≡ vec
  dec-enc-inv i s vec = ( decode (encode i s vec) ≡⟨ refl _ ⟩
                        decode ((s , i) , vec) ≡⟨ refl _ ⟩
                        vec ∎)
  
  -- Work around for partial bijection
  enc-dec-bij≃ : {m : Nat} {s : String} → (i : Fin m) → (Vec String m) ≃ ((String × Fin m) × Vec String m)
  enc-dec-bij≃ {m} {s} i = (encode i s) , equiv₁ (mkqinv decode (enc-dec-inv' i s) (dec-enc-inv i s))

  enc-dec-path : {m : Nat} {s : String} → (i : Fin m) → (Vec String m) ≡ ((String × Fin m) × Vec String m)
  enc-dec-path {m} {s} i with univalence
  ... | (_ , eq) = isequiv.g eq (enc-dec-bij≃ {m} {s} i)

  dec-enc-bij≃ : {m : Nat} {s : String} → (i : Fin m) → ((String × Fin m) × Vec String m) ≃ (Vec String m)
  dec-enc-bij≃ {m} {s} i = decode , equiv₁ (mkqinv (encode i s) (dec-enc-inv i s) (enc-dec-inv' i s))

  dec-enc-path : {m : Nat} {s : String} → (i : Fin m) → ((String × Fin m) × Vec String m) ≡ (Vec String m)
  dec-enc-path {m} {s} i with univalence
  ... | (_ , eq) = isequiv.g eq (dec-enc-bij≃ {m} {s} i)


  IPBij : {l : Nat} {s : String} → (i : Fin l) → R → Set
  IPBij {l} {s} i = rec {l} (Vec String l) ((String × Fin l) × Vec String l) (enc-dec-path {l} {s} i) (dec-enc-path {l} {s} i)

  IPBij[enc] : {l : Nat} {s : String} → (i : Fin l) → ap (IPBij {l} {s} i) (enc {l} i s) ≡ (dec-enc-path {l} {s} i)
  IPBij[enc] {l} {s} i = βrec-enc {l} {s} i (Vec String l) ((String × Fin l) × Vec String l) (dec-enc-path {l} {s} i)

  IPBij[dec] : {l : Nat} {s : String} → (i : Fin l) → ap (IPBij {l} {s} i) (dec {l} i s) ≡ (enc-dec-path {l} {s} i)
  IPBij[dec] {l} {s} i = βrec-dec {l} {s} i (Vec String l) ((String × Fin l) × Vec String l) (enc-dec-path {l} {s} i)
  

  --- Partial Bijection -end-


  interp-add : {m : Nat} {s : String} → (i : Fin m) → (patch : (tab m ↔ s ↔ i) ≡ (tab (suc m))) → ((String × Fin m) × Vec String m) → (Fin m × (Vec String (suc m)))
  interp-add {m} {s} i addP2 = coe' (ap (I {m} {s}) addP2)
  
  interp-add' : {m : Nat} {s : String} → (i : Fin m) → (patch : (tab m ↔ s ↔ i) ≡ (tab (suc m))) → (Vec String m → Vec String (suc m))
  interp-add' {m} {s} i addP2 = add i s

  {-
  interp-rm : {m : Nat} {s : String} → (patch : (tab (S m)) == (tab m ↔ s)) → (Vec String (S m)) → (String × Vec String m)
  interp-rm {m} {s} rmP2 = coe (ap (I {m} {s}) rmP2)

  interp-rm' : {m : Nat} {s : String} → (patch : (tab (S m)) == (tab m ↔ s)) → (Vec String (S m) → Vec String m)
  interp-rm' {m} {s} rmP2 = rm

  add-rm : {m : Nat} {s : String} → Vec String m → Vec String m
  add-rm {m} {s} vec = rm (add s vec)
  
  interp-add-rm' : {m : Nat} {s : String} → (patch : (tab m ↔ s) == (tab m ↔ s)) → Vec String m → Vec String m
  interp-add-rm' {m} {s} patch vec = (rm (add s vec)) -- add s

  fpatch4 : {m : Nat} {s1 s2 : String} → Vec String m → Vec String (S (S m))
  fpatch4 {m} {s1} {s2} vec = (add s2 (add s1 vec))

  interp-patch4 : {m : Nat} {s1 s2 : String} → (patch : (tab m ↔ s1) == (tab (S (S m)))) → Vec String m → Vec String (S (S m))
  interp-patch4 {m} {s1} {s2} patch vec = fpatch4 {m} {s1} {s2} vec
  -}

  example : Vec String 3
  example = "god" :: ("agda" :: ("you" :: []))

  patch1 = (addP2 {3} Z "hello") ∘ (rmP2 {3} Z "hello") ∘ (dec {3} Z "hello") ∘ (enc {3} (S (S Z)) "hai") ∘ (addP2 {3} (S (S Z)) "hai")
  patch2 = rmP2 {2} (S Z) "you"
  patch3 = (addP2 {3} (S (S Z)) "hello") ∘ (rmP2 {3} (S Z) "hello")
  patch4 = (addP2 {4} (S Z) "hello") ∘ (enc {5} (S (S (S Z))) "hai") ∘ (addP2 {5} (S (S (S Z))) "hai") 
  patch5 = (addP2 {3} (S (S Z)) "hai")
  patch6 = (addP2 {4} (S (S (S Z))) "hai") ∘ (enc {5} (S Z) "hello") ∘ (addP2 {5} (S Z) "hello")
  patch7 = (addP2 {3} (S Z) "pen")
  patch8 = (addP2 {3} Z "book")
  patch9 = (addP2 {4} (S (S (S Z))) "nope")

  {-
     run commands:
     ------------
       - (interp-add' (S (S Z)) patch5) example
       -- (interp-rm' patch2) example
       -- (interp-add-rm' patch3) example
  -} 

