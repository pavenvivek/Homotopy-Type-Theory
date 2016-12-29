{-# OPTIONS --without-K #-}

module Circle-Suspension where

open import Level using (_⊔_)
open import Data.Product using (Σ; _,_)
open import Function renaming (_∘_ to _○_)
open import Agda.Primitive

infixr 8  _∘_     -- path composition
infix  4  _≡_     -- propositional equality
infix  4  _∼_     -- homotopy between two functions 
infix  4  _≃_     -- type of equivalences

-- Equational Reasoning

infix  2  begin_
infix  3  _∎  
infixr 3  _≡⟨_⟩_

------------------------------------------------------------------------------
-- A few HoTT primitives

data Bool : Set where
  true : Bool
  false : Bool

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

pathInd : ∀ {u ℓ} → {A : Set u} → 
          (C : {x y : A} → x ≡ y → Set ℓ) → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

--

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

_∘_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {u} {A} {x} {y} {z} p q = 
  pathInd {u}
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

--

unitTransR : ∀ {u} {A : Set u} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y) 
unitTransR {u} {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ p ∘ (refl y)) 
    (λ x → refl (refl x))
    {x} {y} p 

unitTransL : ∀ {u} {A : Set u} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL {u} {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p 

invTransL : ∀ {u} {A : Set u} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL {u} {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ! p ∘ p ≡ refl y)
    (λ x → refl (refl x))
    {x} {y} p

invTransR : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (p ∘ ! p ≡ refl x)
invTransR {ℓ} {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ∘ ! p ≡ refl x)
    (λ x → refl (refl x))
    {x} {y} p

invId : ∀ {u} {A : Set u} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {u} {A} {x} {y} p =
  pathInd 
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

assocP : ∀ {u} {A : Set u} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP {u} {A} {x} {y} {z} {w} p q r =
  pathInd
    (λ {x} {y} p → (z : A) → (w : A) → (q : y ≡ z) → (r : z ≡ w) → 
      p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
    (λ x z w q r → 
      pathInd
        (λ {x} {z} q → (w : A) → (r : z ≡ w) → 
          (refl x) ∘ (q ∘ r) ≡ ((refl x) ∘ q) ∘ r)
        (λ x w r → 
          pathInd
            (λ {x} {w} r → 
              (refl x) ∘ ((refl x) ∘ r) ≡ 
              ((refl x) ∘ (refl x)) ∘ r)
            (λ x → (refl (refl x)))
            {x} {w} r)
        {x} {z} q w r)
    {x} {y} p z w q r

invComp : ∀ {u} {A : Set u} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → 
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp {u} {A} {x} {y} {z} p q = 
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p)
    (λ x z q → 
      pathInd 
        (λ {x} {z} q → ! (refl x ∘ q) ≡ ! q ∘ ! (refl x))
        (λ x → refl (refl x)) 
        {x} {z} q)
    {x} {y} p z q

-- Equational Reasoning operators

begin_ : ∀ {ℓ} → {A : Set ℓ} → {x y : A} → x ≡ y → x ≡ y
begin_ p1 = p1

_≡⟨_⟩_ : ∀ {ℓ} → {A : Set ℓ} → (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p1 ⟩ p2 = p1 ∘ p2

_∎ : ∀ {ℓ} → {A : Set ℓ} → (a : A) → a ≡ a
_∎ a = refl a

--

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

apfTrans : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y z : A} → 
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans {ℓ} {ℓ'} {A} {B} {x} {y} {z} f p q = 
  pathInd {ℓ}
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → 
      ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q))
    (λ x z q → 
      pathInd {ℓ}
        (λ {x} {z} q → 
          ap f (refl x ∘ q) ≡ (ap f (refl x)) ∘ (ap f q))
        (λ x → refl (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

apfInv : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → (f : A → B) → (p : x ≡ y) → 
         ap f (! p) ≡ ! (ap f p) 
apfInv {ℓ} {ℓ'} {A} {B} {x} {y} f p =
  pathInd {ℓ}
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    {x} {y} p

apfComp : ∀ {ℓ ℓ' ℓ''} → {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ○ f) p 
apfComp {ℓ} {ℓ'} {ℓ''} {A} {B} {C} {x} {y} f g p =
  pathInd 
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ○ f) p)
    (λ x → refl (ap g (ap f (refl x))))
    {x} {y} p

apfId : ∀ {u} → {A : Set u} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {u} {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ap id p ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

--

transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} → 
  (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} {x} {y} P p = 
  pathInd -- on p
    (λ {x} {y} p → (P x → P y))
    (λ _ → id)
    {x} {y} p

apd : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : A → Set ℓ'} {x y : A} → (f : (a : A) → B a) → 
  (p : x ≡ y) → (transport B p (f x) ≡ f y)
apd {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → transport B p (f x) ≡ f y)
    (λ x → refl (f x))
    {x} {y} p

-- Homotopies and equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ
       
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

postulate 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

-- Identity type Transport theorem 
transportIdRefl : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {y z : A} → (f g : A → B) → (p : y ≡ z) → (q : f y ≡ g y) → transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ (q ∘ (ap g p))
transportIdRefl {ℓ} {ℓ'} {A} {B} {y} {z} f g p q = pathInd (λ {y} {z} p → (q : f y ≡ g y) → transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ (q ∘ (ap g p)))
                                                  (λ p q →  transport (λ x → f x ≡ g x) (refl p) q   ≡⟨ refl _ ⟩
                                                             q   ≡⟨ unitTransR q ⟩
                                                             q ∘ (ap g (refl p))   ≡⟨ unitTransL (q ∘ ap g (refl p)) ⟩ 
                                                             (ap f (refl p)) ∘ q ∘ (ap g (refl p))    ≡⟨ refl _ ⟩
                                                             (! (ap f (refl p)) ∘ (q ∘ (ap g (refl p)))) ∎)
                                                  p q

------------------------------------------------------------------------------

module Circle where 

  private 
    data S¹* : Set where
      base* : S¹*

  S¹ : Set
  S¹ = S¹*

  base : S¹
  base = base*

  postulate 
    loop : base ≡ base

  recS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → S¹ → C
  recS¹ cbase cloop base* = cbase

  postulate
    βrecS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → 
      ap (recS¹ cbase cloop) loop ≡ cloop

  indS¹ : {C : S¹ → Set} → 
    (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
    (circle : S¹) → C circle
  indS¹ cbase cloop base* = cbase

  postulate
    βindS¹ : {C : S¹ → Set} → 
      (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
      apd (indS¹ {C} cbase cloop) loop ≡ cloop
  

open Circle public

module Susp where

  private
    data Σₛ* (A : Set) : Set where
      N* : Σₛ* A
      S* : Σₛ* A
  
  Σₛ : (A : Set) → Set
  Σₛ = Σₛ*

  N : {A : Set} → Σₛ A
  N = N*

  S : {A : Set} → Σₛ A
  S = S*

  postulate
    merid : {A : Set} → (a : A) → (N {A} ≡ S {A})

  recₛ : {A : Set} → {B : Set} → (n s : B) → (m : A → (n ≡ s)) → Σₛ A → B
  recₛ n s m N* = n
  recₛ n s m S* = s

  postulate
    βrecₛ : {A : Set} → {B : Set} → (n s : B) → (m : A → (n ≡ s)) →
            {a : A} → ap (recₛ n s m) (merid a) ≡ m a
  
  indₛ : {A : Set} → {B : Σₛ A → Set} → (n : B (N {A})) → (s : B (S {A})) → (m : (a : A) → (transport B (merid a) n ≡ s)) → (x : Σₛ A) → B x
  indₛ n s m N* = n
  indₛ n s m S* = s

  postulate
    βindₛ : {A : Set} → {B : Σₛ A → Set} → (n : B N) → (s : B S) → (m : (a : A) → (transport B (merid a) n ≡ s)) →
            {a : A} → apd (indₛ n s m) (merid a) ≡ m a  


open Susp public

merid1 : Bool → base ≡ base
merid1 false = loop
merid1 true = refl base

-- g N ≡ base
-- g S ≡ base

g : (Σₛ Bool) → S¹
g = recₛ base base merid1

-- g (false) = loop

g[false] : ap g (merid false) ≡ loop
g[false] = βrecₛ base base merid1

-- g (true) = (refl base)

g[true] : ap g (merid true) ≡ (refl base)
g[true] = βrecₛ base base merid1

-- g (base) = N

f : S¹ → (Σₛ Bool)
f = recS¹ N (merid false ∘ ! (merid true)) 

-- f (loop) = (merid false ∘ ! (merid true))

f[loop] : ap f loop ≡ (merid false ∘ ! (merid true))
f[loop] = βrecS¹ N (merid false ∘ ! (merid true)) 

--  g∘f (base) = base

g∘f : S¹ → S¹
g∘f = g ○ f

--  g∘f (loop) = loop

g∘f[loop] : ap g∘f loop ≡ loop
g∘f[loop] = begin
            ap g∘f loop ≡⟨ ! (apfComp f g loop) ⟩
            ap g (ap f loop) ≡⟨ ap (λ x → ap g x) f[loop] ⟩
            ap g (merid false ∘ ! (merid true)) ≡⟨ apfTrans g (merid false) (! (merid true)) ⟩
            (ap g (merid false)) ∘ (ap g (! (merid true))) ≡⟨ ap (λ x → x ∘ ap g (! (merid true))) g[false] ⟩
            loop ∘ (ap g (! (merid true))) ≡⟨ ap (λ x → loop ∘ x) (apfInv g (merid true)) ⟩
            loop ∘ ! (ap g (merid true)) ≡⟨ ap (λ x → loop ∘ ! x) g[true] ⟩
            loop ∘ ! (refl base) ≡⟨ refl _ ⟩
            loop ∘ (refl base) ≡⟨ ! (unitTransR loop) ⟩
            loop ∎


{-
    f∘g (false) = N
    f∘g (true) = N
-}

f∘g : (Σₛ Bool) → (Σₛ Bool)
f∘g = f ○ g

--  f∘g (false) = loop

f∘g[false] : ap f∘g (merid false) ≡ (merid false ∘ ! (merid true))
f∘g[false] = ap f∘g (merid false) ≡⟨ ! (apfComp g f (merid false)) ⟩
             ap f (ap g (merid false)) ≡⟨ ap (λ x → ap f x) g[false] ⟩
             ap f loop ≡⟨ f[loop] ⟩
             ((merid false) ∘ ! (merid true)) ∎

--  f∘g (true) = refl base

f∘g[true] : ap f∘g (merid true) ≡ refl N
f∘g[true] = ap f∘g (merid true) ≡⟨ ! (apfComp g f (merid true)) ⟩
            ap f (ap g (merid true)) ≡⟨ ap (λ x → ap f x) g[true] ⟩
            ap f (refl base) ≡⟨ refl _ ⟩
            refl N ∎

α[false] : transport (λ x → f∘g x ≡ x) (merid false) (refl N) ≡ (merid true)
α[false] = begin
           transport (λ x → f∘g x ≡ x) (merid false) (refl N) ≡⟨ transportIdRefl f∘g id (merid false) (refl N) ⟩
           ! (ap f∘g (merid false)) ∘ ((refl N) ∘ (ap id (merid false))) ≡⟨ ap (λ x → ! (ap f∘g (merid false)) ∘ x)
                                                                                               (! (unitTransL (ap id (merid false)))) ⟩
           ! (ap f∘g (merid false)) ∘ (ap id (merid false)) ≡⟨ ap (λ x → ! (ap f∘g (merid false)) ∘ x)
                                                                           (apfId (merid false)) ⟩
           ! (ap f∘g (merid false)) ∘ (merid false) ≡⟨ ap (λ x → ! x ∘ merid false)
                                                                   (! (apfComp g f (merid false))) ⟩
           ! (ap f (ap g (merid false))) ∘ (merid false) ≡⟨ ap (λ x → ! (ap f x) ∘ merid false) g[false] ⟩
           ! (ap f loop) ∘ (merid false) ≡⟨ ap (λ x → ! x ∘ merid false) f[loop] ⟩
           ! ((merid false) ∘ ! (merid true)) ∘ (merid false) ≡⟨ ap (λ x → x ∘ (merid false)) (invComp (merid false) (! (merid true))) ⟩
           (! (! (merid true)) ∘ ! (merid false)) ∘ (merid false) ≡⟨ ap (λ x → (x ∘ ! (merid false)) ∘ merid false)
                                                                                      (invId (merid true)) ⟩
           ((merid true) ∘ ! (merid false)) ∘ (merid false) ≡⟨ ! (assocP (merid true) (! (merid false))
                                                                                 (merid false)) ⟩
           (merid true) ∘ (! (merid false) ∘ (merid false)) ≡⟨ ap (λ x → merid true ∘ x) (invTransL (merid false)) ⟩
           (merid true) ∘ (refl _) ≡⟨ ! (unitTransR (merid true)) ⟩
           (merid true) ∎

α[true] : transport (λ x → f∘g x ≡ x) (merid true) (refl N) ≡ (merid true)
α[true] = begin
          transport (λ x → f∘g x ≡ x) (merid true) (refl N) ≡⟨ transportIdRefl f∘g id (merid true) (refl N) ⟩
          ! (ap f∘g (merid true)) ∘ ((refl N) ∘ (ap id (merid true))) ≡⟨ ap (λ x → ! (ap f∘g (merid true)) ∘ x)
                                                                                             (! (unitTransL (ap id (merid true)))) ⟩
          ! (ap f∘g (merid true)) ∘ (ap id (merid true)) ≡⟨ ap (λ x → ! (ap f∘g (merid true)) ∘ x)
                                                                         (apfId (merid true)) ⟩
          ! (ap f∘g (merid true)) ∘ (merid true) ≡⟨ ap (λ x → ! x ∘ merid true)
                                                                (! (apfComp g f (merid true))) ⟩
          ! (ap f (ap g (merid true))) ∘ (merid true) ≡⟨ ap (λ x → ! (ap f x) ∘ merid true) g[true] ⟩
          ! (ap f (refl base)) ∘ (merid true) ≡⟨ refl _ ⟩
          ! (refl N) ∘ (merid true) ≡⟨ refl _ ⟩
          (refl N) ∘ (merid true) ≡⟨ ! (unitTransL (merid true)) ⟩
          (merid true) ∎

merid2 : (b : Bool) → transport (λ x → f∘g x ≡ x) (merid b) (refl N) ≡ (merid true)
merid2 false = α[false]
merid2 true = α[true]

α : f∘g ∼ id
α = indₛ {Bool} {λ x → f∘g x ≡ x} (refl N) (merid true) merid2

α[loop] : transport (λ x → g∘f x ≡ x) loop (refl base) ≡ refl base
α[loop] = begin
          transport (λ x → g∘f x ≡ x) loop (refl base) ≡⟨ transportIdRefl g∘f id loop (refl base) ⟩
          ! (ap g∘f loop) ∘ (refl base) ∘ (ap id loop) ≡⟨ ap (λ x → ! (ap g∘f loop) ∘ x) (! (unitTransL (ap id loop))) ⟩
          ! (ap g∘f loop) ∘ (ap id loop) ≡⟨ ap (λ x → ! (ap g∘f loop) ∘ x) (apfId loop) ⟩
          ! (ap g∘f loop) ∘ loop ≡⟨ ap (λ x → ! x ∘ loop) g∘f[loop] ⟩
          ! loop ∘ loop ≡⟨ invTransL loop ⟩
          refl base ∎

β : g∘f ∼ id
β = indS¹ {λ x → g∘f x ≡ x} (refl base) α[loop]

Lemma-6-5-1 : S¹ ≃ (Σₛ Bool)
Lemma-6-5-1 = (f , equiv₁ (mkqinv g α β))

ua[Lemma-6-5-1] : S¹ ≡ (Σₛ Bool)
ua[Lemma-6-5-1] with univalence 
... | (_ , eq) = isequiv.g eq Lemma-6-5-1

----------------------------------------------------------------------------------------------------------------------


-- Chapter 6.8

module Pushout where

  private
    data Pushout* {A B C : Set} (f : C → A) (g : C → B) : Set where
      inl* : A → Pushout* f g 
      inr* : B → Pushout* f g

  Pushout : {A B C : Set} → (f : C → A) → (g : C → B) → Set
  Pushout = Pushout*

  inl : {A B C : Set} → {f : C → A} → {g : C → B} → A → Pushout f g
  inl = inl*

  inr : {A B C : Set} → {f : C → A} → {g : C → B} → B → Pushout f g
  inr = inr*

  postulate
    glue : {A B C : Set} → {f : C → A} → {g : C → B} → (c : C) → (inl {A} {B} {C} {f} {g} (f c)) ≡ (inr (g c))

  recPush : {A B C : Set} → {f : C → A} → {g : C → B} →
            {D : Set} → (f1 : A → D) → (f2 : B → D) →
            (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) →
            Pushout f g → D
  recPush f1 f2 dglue (inl* a) = (f1 a)
  recPush f1 f2 dglue (inr* b) = (f2 b)

  postulate
    βrecPush : {A B C : Set} → {f : C → A} → {g : C → B} →
               {D : Set} → (f1 : A → D) → (f2 : B → D) →
               (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) →
               {c : C} → ap (recPush f1 f2 dglue) (glue c) ≡ (dglue c)

  indPush : {A B C : Set} → {f : C → A} → {g : C → B} →
            {D : Pushout f g → Set} → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
            (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) →
            (p : Pushout f g) → D p
  indPush f1 f2 dglue (inl* a) = (f1 a)
  indPush f1 f2 dglue (inr* b) = (f2 b)

  postulate
    βindPush : {A B C : Set} → {f : C → A} → {g : C → B} →
               {D : Pushout f g → Set} → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
               (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) →
               {c : C} → apd (indPush f1 f2 dglue) (glue c) ≡ (dglue c)
               


open Pushout public

module Join where

  data _×_ (A : Set) (B : Set) : Set where
    _,_ : A → B → A × B

  fst : {A : Set} {B : Set} → A × B → A
  fst (a , b) = a

  snd : {A : Set} {B : Set} → A × B → B
  snd (a , b) = b

  -- Join operation defined as a pushout on (A, B, A × B, fst, snd) span type
  
  _*_ : (A : Set) → (B : Set) → Set
  _*_ A B = Pushout {A} {B} {A × B} fst snd

  rec* : {A B : Set} → {f : A × B → A} → {g : A × B → B} →
         {D : Set} → (f1 : A → D) → (f2 : B → D) →
         (dglue : (c : A × B) → (f1 (f c)) ≡ (f2 (g c))) →
         Pushout f g → D
  rec* {A} {B} {f} {g} {D} f1 f2 dglue = recPush {A} {B} {A × B} {f} {g} {D} f1 f2 dglue

  postulate
    βrec* : {A B : Set} → {f : A × B → A} → {g : A × B → B} →
            {D : Set} → (f1 : A → D) → (f2 : B → D) →
            (dglue : (c : A × B) → (f1 (f c)) ≡ (f2 (g c))) →
            {c : A × B} → ap (rec* f1 f2 dglue) (glue c) ≡ (dglue c)
            
  ind* : {A B : Set} → {f : A × B → A} → {g : A × B → B} →
         {D : Pushout f g → Set} → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
         (dglue : (c : A × B) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) →
         (p : Pushout f g) → D p
  ind* {A} {B} {f} {g} {D} f1 f2 dglue = indPush {A} {B} {A × B} {f} {g} {D} f1 f2 dglue 

  postulate
    βind* : {A B : Set} → {f : A × B → A} → {g : A × B → B} →
            {D : Pushout f g → Set} → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
            (dglue : (c : A × B) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) →
            {c : A × B} → apd (ind* f1 f2 dglue) (glue c) ≡ (dglue c)
               

open Join public

-- Alternate Notations for Thm 8.5.11 Proof

Σ2 = Σₛ Bool

2' = Bool
ΣS¹ = Σₛ S¹
ΣΣS¹ = Σₛ ΣS¹ 

-- Defn-6.5.2

S² = Σₛ S¹
S³ = Σₛ S²

-- Univalence axiom

postulate
  ua : {A B : Set} → (A ≃ B) → A ≡ B

-- Lemma-8.5.10

postulate
   Lemma-8-5-10 : (A : Set) → (Σₛ A) ≃ (2' * A) 

-- Lemma-8.5.9

postulate
   Lemma-8-5-9 : (A B C : Set) → (A * B) * C ≃ A * (B * C)


-- Theorem 8.5.11

Hopf-fibration : S¹ * S¹ ≡ S³
Hopf-fibration = begin
                 S¹ * S¹ ≡⟨ ap (λ x → x * S¹) ua[Lemma-6-5-1] ⟩
                 (Σ2) * S¹ ≡⟨ ap (λ x → x * S¹) (ua {Σ2} {2' * 2'} (Lemma-8-5-10 2')) ⟩
                 (2' * 2') * S¹ ≡⟨ ua {(2' * 2') * S¹} {2' * (2' * S¹)} (Lemma-8-5-9 2' 2' S¹) ⟩
                 2' * (2' * S¹) ≡⟨ ap (λ x → 2' * x) (! (ua {ΣS¹} {2' * S¹} (Lemma-8-5-10 S¹))) ⟩
                 2' * ΣS¹ ≡⟨ ! (ua {ΣΣS¹} {2' * ΣS¹} (Lemma-8-5-10 ΣS¹)) ⟩
                 ΣΣS¹ ≡⟨ refl _ ⟩ -- By Defn-6.5.2
                 S³ ∎

--------------------------------------------------------------------------------------------------------------
