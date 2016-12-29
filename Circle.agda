{-# OPTIONS --without-K #-}

module Circle where

open import Level using (_⊔_)
open import Data.Product using (Σ; _,_)
open import Function renaming (_∘_ to _○_)

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

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y) 
unitTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ p ∘ (refl y)) 
    (λ x → refl (refl x))
    {x} {y} p 

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p 

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL {A} {x} {y} p = 
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

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd 
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP {A} {x} {y} {z} {w} p q r =
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

invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → 
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp {A} {x} {y} {z} p q = 
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p)
    (λ x z q → 
      pathInd 
        (λ {x} {z} q → ! (refl x ∘ q) ≡ ! q ∘ ! (refl x))
        (λ x → refl (refl x)) 
        {x} {z} q)
    {x} {y} p z q

-- Equational Reasoning operators

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin_ p1 = p1

_≡⟨_⟩_ : {A : Set} → (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p1 ⟩ p2 = p1 ∘ p2

_∎ : {A : Set} → (a : A) → a ≡ a
_∎ a = refl a

--

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

apfTrans : ∀ {u} → {A B : Set u} {x y z : A} → 
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans {u} {A} {B} {x} {y} {z} f p q = 
  pathInd {u}
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → 
      ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q))
    (λ x z q → 
      pathInd {u}
        (λ {x} {z} q → 
          ap f (refl x ∘ q) ≡ (ap f (refl x)) ∘ (ap f q))
        (λ x → refl (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

apfInv : ∀ {u} → {A B : Set u} {x y : A} → (f : A → B) → (p : x ≡ y) → 
         ap f (! p) ≡ ! (ap f p) 
apfInv {u} {A} {B} {x} {y} f p =
  pathInd {u}
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    {x} {y} p

apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ○ f) p 
apfComp {A} {B} {C} {x} {y} f g p =
  pathInd 
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ○ f) p)
    (λ x → refl (ap g (ap f (refl x))))
    {x} {y} p

apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {A} {x} {y} p = 
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
transportIdRefl : {A B : Set} {y z : A} → (f g : A → B) → (p : y ≡ z) → (q : f y ≡ g y) → transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ (q ∘ (ap g p))
transportIdRefl {A} {B} {y} {z} f g p q = pathInd (λ {y} {z} p → (q : f y ≡ g y) → transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ (q ∘ (ap g p)))
                                                  (λ p q →  transport (λ x → f x ≡ g x) (refl p) q   ≡⟨ refl _ ⟩
                                                             q   ≡⟨ unitTransR q ⟩
                                                             q ∘ (ap g (refl p))   ≡⟨ unitTransL (q ∘ (ap g (refl p))) ⟩ 
                                                             (ap f (refl p)) ∘ q ∘ (ap g (refl p))    ≡⟨ refl _ ⟩
                                                             (! (ap f (refl p)) ∘ (q ∘ (ap g (refl p)))) ∎)
                                                  p q

------------------------------------------------------------------------------
-- Exercise: let's show that the following two definitions of the
-- circle are "the same"

module Circle1 where
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

open Circle1 public

module Circle2 where
  private 
    data S¹'* : Set where
      south* : S¹'*
      north* : S¹'*

  S¹' : Set
  S¹' = S¹'*

  south : S¹'
  south = south*

  north : S¹'
  north = north*

  postulate 
    east : south ≡ north
    west : south ≡ north

  recS¹' : {C : Set} → 
    (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → S¹' → C
  recS¹' csouth cnorth ceast cwest south* = csouth
  recS¹' csouth cnorth ceast cwest north* = cnorth

  postulate
    βreceastS¹' : {C : Set} → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (recS¹' csouth cnorth ceast cwest) east ≡ ceast
    βrecwestS¹' : {C : Set} → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (recS¹' csouth cnorth ceast cwest) west ≡ cwest
 
  indS¹' : {C : S¹' → Set} → 
    (csouth : C south) → (cnorth : C north) → 
    (ceast : transport C east csouth ≡ cnorth) → 
    (cwest : transport C west csouth ≡ cnorth) → 
    (circle : S¹') → C circle
  indS¹' csouth cnorth ceast cwest south* = csouth
  indS¹' csouth cnorth ceast cwest north* = cnorth

  postulate
    βindeastS¹' : {C : S¹' → Set} → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (indS¹' {C} csouth cnorth ceast cwest) east ≡ ceast
    βindwestS¹' : {C : S¹' → Set} → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (indS¹' {C} csouth cnorth ceast cwest) west ≡ cwest

open Circle2 public


--  f (base) = north

f : S¹ → S¹'
f = recS¹ north (! east ∘ west)

--  f (loop) = ! east ∘ west

f[loop] : ap f loop ≡ (! east ∘ west)
f[loop] = βrecS¹ north (! east ∘ west)

{-
    g (south) = base
    g (north) = base
-}

g : S¹' → S¹
g = recS¹' base base (refl base) loop

--  g (east)  = refl base

g[east] : ap g east ≡ (refl base)
g[east] = βreceastS¹' base base (refl base) loop

--  g (west)  = loop

g[west] : ap g west ≡ loop
g[west] = βrecwestS¹' base base (refl base) loop

--  g∘f (base) = base

g∘f : S¹ → S¹
g∘f = g ○ f

--  g∘f (loop) = loop

g∘f[loop] : ap g∘f loop ≡ loop
g∘f[loop] = begin
         ap g∘f loop ≡⟨ ! (apfComp f g loop) ⟩
         ap g (ap f loop) ≡⟨ ap (λ x → ap g x) f[loop] ⟩
         ap g (! east ∘ west) ≡⟨ apfTrans g (! east) west ⟩
         (ap g (! east)) ∘ (ap g west) ≡⟨ ap (λ x → x ∘ ap g west) (apfInv g east) ⟩
         ! (ap g east) ∘ (ap g west) ≡⟨ ap (λ x → ! x ∘ ap g west) g[east] ⟩
         ! (refl base) ∘ (ap g west) ≡⟨ refl _ ⟩
         (refl base) ∘ (ap g west) ≡⟨ ! (unitTransL (ap g west)) ⟩
         ap g west ≡⟨ g[west] ⟩
         loop ∎

{-
    f∘g (south) = north
    f∘g (north) = north
-}

f∘g : S¹' → S¹'
f∘g = f ○ g

--  f∘g (east) = refl north

f∘g[east] : ap f∘g east ≡ (refl north)
f∘g[east] = begin
         ap f∘g east ≡⟨ ! (apfComp g f east) ⟩
         ap f (ap g east) ≡⟨ ap (λ x → ap f x) g[east] ⟩
         ap f (refl base) ≡⟨ refl _ ⟩
         (refl north) ∎

--  f∘g (west) = (! east ∘ west)

f∘g[west] : ap f∘g west ≡ (! east ∘ west)
f∘g[west] = begin
         ap f∘g west ≡⟨ ! (apfComp g f west) ⟩
         ap f (ap g west) ≡⟨ ap (λ x → ap f x) g[west] ⟩
         ap f loop ≡⟨ f[loop] ⟩
         (! east ∘ west) ∎


α[east] : transport (λ x → f∘g x ≡ x) east (! east) ≡ (refl north)
α[east] = begin
        transport (λ x → f∘g x ≡ x) east (! east) ≡⟨ transportIdRefl f∘g id east (! east) ⟩
        ! (ap f∘g east) ∘ (! east) ∘ (ap id east) ≡⟨ ap (λ x → ! (ap f∘g east) ∘ ! east ∘ x) (apfId east) ⟩
        ! (ap f∘g east) ∘ (! east) ∘ east ≡⟨ ap (λ x → ! (ap f∘g east) ∘ x) (invTransL east) ⟩
        ! (ap f∘g east) ∘ (refl north) ≡⟨ ! (unitTransR (! (ap f∘g east))) ⟩
        ! (ap f∘g east) ≡⟨ ap (λ x → ! x) (! (apfComp g f east)) ⟩
        ! (ap f (ap g east)) ≡⟨ ap (λ x → ! (ap f x)) g[east] ⟩
        ! (ap f (refl base)) ≡⟨ refl _ ⟩
        ! (refl north) ≡⟨ refl _ ⟩
        (refl north) ∎


α[west] : transport (λ x → f∘g x ≡ x) west (! east) ≡ (refl north)
α[west] = begin
        transport (λ x → f∘g x ≡ x) west (! east) ≡⟨ transportIdRefl f∘g id west (! east) ⟩
        ! (ap f∘g west) ∘ (! east) ∘ (ap id west) ≡⟨ ap (λ x → ! (ap f∘g west) ∘ ! east ∘ x) (apfId west) ⟩
        ! (ap f∘g west) ∘ (! east) ∘ west ≡⟨ ap (λ x → ! x ∘ ! east ∘ west) f∘g[west] ⟩
        ! (! east ∘ west) ∘ (! east) ∘ west ≡⟨ ap (λ x → x ∘ ! east ∘ west) (invComp (! east) west) ⟩
        (! west ∘ ! (! east)) ∘ (! east) ∘ west ≡⟨ ap (λ x → (! west ∘ x) ∘ ! east ∘ west) (invId east) ⟩
        (! west ∘ east) ∘ ((! east) ∘ west) ≡⟨ assocP (! west ∘ east) (! east) west ⟩
        ((! west ∘ east) ∘ ! east) ∘ west ≡⟨ ap (λ x → x ∘ west) (! (assocP (! west) east (! east))) ⟩
        (! west ∘ (east ∘ ! east)) ∘ west ≡⟨ ap (λ x → (! west ∘ x) ∘ west) (invTransR east) ⟩
        (! west ∘ (refl _)) ∘ west ≡⟨ ap (λ x → x ∘ west) (! (unitTransR (! west))) ⟩
        (! west ∘ west) ≡⟨ invTransL west ⟩
        (refl north) ∎


α : f∘g ∼ id
α = indS¹' {λ x → f∘g x ≡ x} (! east) (refl north) α[east] α[west]

α[loop] : transport (λ x → g∘f x ≡ x) loop (refl base) ≡ refl base
α[loop] = begin
        transport (λ x → g∘f x ≡ x) loop (refl base) ≡⟨ transportIdRefl g∘f id loop (refl base) ⟩
        ! (ap g∘f loop) ∘ (refl base) ∘ (ap id loop) ≡⟨ ap (λ x → ! (ap g∘f loop) ∘ x) (! (unitTransL (ap id loop))) ⟩
        ! (ap g∘f loop) ∘ (ap id loop) ≡⟨ ap (λ x → ! (ap g∘f loop) ∘ x) (apfId loop) ⟩
        ! (ap g∘f loop) ∘ loop ≡⟨ ap (λ x → ! x ∘ loop) g∘f[loop] ⟩
        ! loop ∘ loop ≡⟨ invTransL loop ⟩
        (refl base) ∎

β : g∘f ∼ id
β = indS¹ {λ x → g∘f x ≡ x} (refl base) α[loop]

sequiv : S¹ ≃ S¹'
sequiv = (f , equiv₁ (mkqinv g α β))

spath : S¹ ≡ S¹'
spath with univalence 
... | (_ , eq) = isequiv.g eq sequiv

------------------------------------------------------------------------------

