
open import Data.Bool
open import Data.Product using (_×_; _,_)
open import CryptDB_HoTT.agda_lib.Nat
open import CryptDB_HoTT.agda_lib.Vector
open import CryptDB_HoTT.agda_lib.Equiv

module CryptDB_HoTT.agda_lib.Utils where

  data Singleton {A : Set} (x : A) : Set where
    _with≡_ : (y : A) → x ≡ y → Singleton x

  to-Singleton : {A B : Set} {a : A} → (f : A → B) → Singleton a → Singleton (f a)
  to-Singleton {a} f (x with≡ p) = (f x with≡ ap f p)

  inspect : {A : Set} (x : A) → Singleton x
  inspect x = x with≡ (refl x)

  postulate
    singleton-equiv : {A B : Set} {f : A → B} {m : A} → (Singleton m → Singleton (f m)) → Singleton m ≃ Singleton (f m)

  data Void : Set where

  data _⊎_ (a : Set) (b : Set) : Set where
    Inl : a -> a ⊎ b
    Inr : b -> a ⊎ b

  data Fin : Nat → Set where
    zero : ∀ {n} → Fin (suc n) 
    suc : ∀ {n} → Fin n → Fin (suc n)

  data ⊥ : Set where 

  abort : {A : Set} → ⊥ → A
  abort ()

  postulate
      failed : ⊥

  Int : Set
  Int = Nat

  rec× : {A : Set} {B : Set} →
        (C : Set) → (A → B → C) → A × B → C
  rec× C g (a , b) = g a b

  ind× : {A : Set} {B : Set} → (C : A × B → Set) → 
         ((a : A) → (b : B) → C (a , b)) → (p : A × B) → C p
  ind× C g ( a , b ) = g a b

  recBool : (C : Set) → C → C → Bool → C
  recBool C el th false = el
  recBool C el th true = th

  indBool : (C : Bool → Set) → C false → C true → (b : Bool) → C b
  indBool C el th false = el
  indBool C el th true = th

  mod*-inv' : Nat → Nat → Nat → Nat
  mod*-inv' a 0 c = mod 0 c
  mod*-inv' a (suc b) c = if (1 == (mod (a * b) c)) then b else (mod*-inv' a b c)

  mod*-inv : Nat → Nat → Nat
  mod*-inv a c = mod*-inv' a c c

  coprime' : (index1 : Nat) → (index2 : Nat) → (euler-totient : Nat) → Nat
  coprime' 0 index2 euler-totient = (abort failed)
  coprime' (suc index1) index2 euler-totient = if (index2 > 1)
                                                  then if (index2 < euler-totient)
                                                          then if (1 == (gcd euler-totient index2))
                                                                  then index2
                                                                  else (coprime' index1 (suc index2) euler-totient)
                                                               else (abort failed)
                                                  else (abort failed)

  coprime : (euler-totient : Nat) → Nat
  coprime euler-totient = coprime' euler-totient 2 euler-totient

  getRand : (p : Int) → Int
  getRand p = if (2 == p)
                 then 1
                 else 2

  loop : {A B : Set} (n : Nat) → (f : A → B) → Vec A n → Vec B n
  loop {A} {B} 0 f [] = []
  loop {A} {B} (suc n) f (x :: xs) = (f x) :: (loop {A} n f xs)
