module Chapter1_Exercise where

import Level
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Function using (id)
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Chapter 1

-- Ex 1.1

data Id {A : Set} : A -> A -> Set where
    refl : {a : A} -> Id a a

_∘_ : {A : Set}
      {B : A → Set}
      {C : (x : A) → B x → Set}
      →
      (g : {x : A} (y : B x) → C x y)
      (f : (x : A) → B x)
      →
      (x : A) → C x (f x)
(g ∘ f) x = g (f x)


associativity-∘ : {A B C D : Set} → (f : A → B) → (g : B → C) → (h : C → D) → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
associativity-∘ f g h = refl


-- Ex 1.2

-- data _×_ (A : Set) (B : Set) : Set where
  -- _,_ : A → B → A × B
  
fst : ∀ {A B : Set} -> A × B → A
fst (a , b) = a

snd : ∀ {A B : Set} → A × B → B
snd (a , b) = b

rec×2 : {A : Set} {B : Set} → (C : Set) → (A → B → C) → (p : A × B) → C
rec×2 C g p = g (fst p) (snd p)

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,₁_  -- constructor clashing with product pair type
  field
    proj₁ : A
    proj₂ : B proj₁

recΣ₂ : {A : Set} {B : A → Set} → (C : Set) → ((a : A) → B a → C) → (p : Σ A B) → C
recΣ₂ C g p = g (Σ.proj₁ p) (Σ.proj₂ p)

-- Ex 1.3

ind×2 : {A : Set} {B : Set} → (C : A × B → Set) → 
       ((a : A) → (b : B) → C (a , b)) → (p : A × B) → C p
ind×2 C g p = g (fst p) (snd p)

indΣ₂ : {A : Set} {B : A → Set} → (C : Σ A B → Set) → 
        ((a : A) → (b : B a) → C (a ,₁ b)) → (p : Σ A B) → C p
indΣ₂ C g p = g (Σ.proj₁ p) (Σ.proj₂ p)

-- Ex 1.4

iterℕ : ∀ {ℓ} → (C : Set ℓ) → C → (C → C) → ℕ → C
iterℕ C z f 0 = z
iterℕ C z f (suc n) = f (iterℕ C z f n)

myrecℕ : ∀ {ℓ} → (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
myrecℕ C c f n = iterℕ C c (λ x → f n x) n 

recℕ : ∀ {ℓ} → (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
recℕ C z f 0 = z
recℕ C z f (suc n) = f n (recℕ C z f n)

indℕ : ∀ {ℓ} → (C : ℕ → Set ℓ) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indℕ C z f 0 = z
indℕ C z f (suc n) = f n (indℕ C z f n)

{-
myrecℕ≡recℕ : (n : ℕ) → (C : Set) → (c : C) → (f : ℕ → C → C) → (myrecℕ C c f n ≡ recℕ C c f n)
myrecℕ≡recℕ = indℕ
                 (λ n → (C : Set) (c : C) (f : ℕ → C → C)  → (myrecℕ C c f n) ≡ (recℕ C c f n))
                 (λ C c f → refl)
                 (λ n x C c f → (begin
                                 myrecℕ C c f (suc n) ≡⟨ refl ⟩
                                 iterℕ C c (λ x → (f (suc n) x)) (suc n) ≡⟨ {!!} ⟩ -- Trying to get this working
                                 iterℕ C c (λ x → (f n x)) (suc n) ≡⟨ refl ⟩
                                 (λ x → f n x) (iterℕ C c (λ x → (f n x)) n) ≡⟨ refl ⟩
                                 (f n) (iterℕ C c (λ x → (f n x)) n) ≡⟨ refl ⟩
                                 (f n) (myrecℕ C c f n) ≡⟨ cong (f n) (x C c f) ⟩
                                 f n (recℕ C c f n) ∎))
-}


-- Ex 1.5

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

rec⊎ : {A : Set} {B : Set} →
       (C : Set) → (A → C) → (B → C) → (A ⊎ B → C)
rec⊎ C f g (inj₁ a) = f a
rec⊎ C f g (inj₂ b) = g b


data Bool : Set where
  false : Bool
  true : Bool

recBool : ∀ {ℓ} → (C : Set ℓ) → C → C → Bool → C
recBool C el th false = el
recBool C el th true = th

indBool : ∀ {ℓ} → (C : Bool → Set ℓ) → C false → C true → (b : Bool) → C b
indBool C el th false = el
indBool C el th true = th

_⊎₂_ : Set → Set → Set
A ⊎₂ B = Σ Bool (λ b → recBool Set A B b)

inl : {A B : Set} → A → A ⊎₂ B
inl a = (false ,₁ a)

inr : {A B : Set} → B → A ⊎₂ B
inr b = (true ,₁ b)

rec⊎₂ : {A : Set} {B : Set} →
       (C : Set) → (A → C) → (B → C) → (A ⊎₂ B → C)
rec⊎₂ C f g (false ,₁ a) = f a
rec⊎₂ C f g (true ,₁ b) = g b

indΣ : {A : Set} {B : A → Set} → (C : Σ A B → Set) → 
        ((a : A) → (b : B a) → C (a ,₁ b)) → (p : Σ A B) → C p
indΣ C g ( a ,₁ b ) = g a b

ind⊎₂ : {A : Set} {B : Set}
        → (C : A ⊎₂ B → Set)
        → ((a : A) → C (inl a))
        → ((b : B) → C (inr b))
        → ((x : A ⊎₂ B) → C x)
ind⊎₂ {A} {B} C f g x = indΣ C (indBool (λ b → (y : recBool Set A B b) → C (b ,₁ y)) f g) x

{- 
ind⊎₂ C f g (false , a) = f a
ind⊎₂ C f g (true , b) = g b
-}


-- Ex 1.6

_×₂_ : Set → Set → Set
A ×₂ B = (b : Bool) → recBool Set A B b

_,₂_ : {A B : Set} → A → B → A ×₂ B
_,₂_ {A} {B} a b = indBool
              (λ b → recBool Set A B b)
              a b

prj₁ : {A B : Set} → (p : A ×₂ B) → A
prj₁ x = x false

prj₂ : {A B : Set} → (p : A ×₂ B) → B
prj₂ x = x true

rec×₂ : {A : Set} {B : Set}→
      (C : Set) → (A → B → C) → A ×₂ B → C
rec×₂ C g x = g (prj₁ x) (prj₂ x)

postulate
  funext : {A : Set} {B : A → Set} → {f g : (x : A) → B x} → ((x : A) →  f x ≡ g x) → f ≡ g

uppt_arg : {A B : Set} → (p : A ×₂ B) → (b : Bool) → (prj₁ p ,₂ prj₂ p) b ≡ p b
uppt_arg p = indBool
                (λ b → (prj₁ p ,₂ prj₂ p) b ≡ p b)
                refl
                refl

uppt : {A B : Set} → (p : A ×₂ B) → (prj₁ p ,₂ prj₂ p) ≡ p
uppt p = funext (uppt_arg p)

ind×₂ : ∀ {𝑖} → {A B : Set} → (P : A ×₂ B → Set 𝑖)
      → (d : (x : A)(y : B) → P (x ,₂ y))
      → (u : A ×₂ B) → P u
ind×₂ P d u = subst P (uppt u) (d (prj₁ u) (prj₂ u))


-- Ex 1.7

-- Path induction

J : ∀ {ℓ} → {A : Set}
    → (R : (x y : A) → (p : x ≡ y) → Set ℓ)
    → (r : (a : A) → R a a refl)
    → ({a b : A} (p : a ≡ b) → R a b p)
J _ r refl = r _


-- Based-path induction

based-path-ind : {A : Set} → {a : A}
                 → (R : (x : A) → (p : a ≡ x) → Set)
                 → R a refl
                 → ((x : A) → (p : a ≡ x) → R x p)
based-path-ind _ r _ refl = r


transport : {A : Set}{x y : A}
            → (B : A → Set) → x ≡ y
            → B x → B y
transport B refl = id

SumContr : {A : Set} → (x : A) → Set
SumContr {A = A} a = Σ A λ x → a ≡ x

isContr : (A : Set) → Set
isContr A = Σ A λ a → (x : A) → a ≡ x


ind'-contr : {A : Set} → (a : A) → isContr (SumContr a)
ind'-contr {A} a = (a ,₁ refl) ,₁ λ { (x2 ,₁ p2) → f x2 p2 }
                   where
                      f : (x : A)(p : a ≡ x) → (a ,₁ refl) ≡ (x ,₁ p)
                      f .a refl = refl


ind' : {A : Set} → {a : A}
       → (R : (x : A) → (p : a ≡ x) → Set)
       → R a refl
       → ((x : A) → (p : a ≡ x) → R x p)
ind' {A} {a} R r x p = transport (λ {(x2 ,₁ p2) → R x2 p2}) ((Σ.proj₂ (ind'-contr a)) (x ,₁ p)) r


-- Ex 1.8

add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ n → n) (λ m r → λ n → suc (r n))

mult : ℕ → ℕ → ℕ
mult = recℕ (ℕ → ℕ) (λ n → 0) (λ m r → λ n → add n (r n))

-- exp (first arg -> power) (second argument -> base)
exp : ℕ → ℕ → ℕ
exp = recℕ (ℕ → ℕ) (λ n → 1) (λ m r → λ n → mult n (r n))

-- Proof for Semiring
{- 

Semiring:

A set S with binary operators + and * is a semiring if it satisfies the following condition

1] ∀ {a b c : S} → (a + b) + c = a + (b + c) -- Additive Associativity
2] ∀ {a b : S} → a + b = b + a -- Additive Commutativity
   ∀ {a : S} → a + 0 = 0 + a = a
3] ∀ {a b c : S} → (a * b) * c = a * (b * c) -- Multiplicative Associativity
   ∀ {a : S} → a * 1 = 1 * a = 1
   ∀ {a : S} → a * 0 = 0 * a = 0
4] ∀ {a b c : S} → a * (b + c) = (a * b) + (a * c) and (a + b) * c = (a * c) + (b * c) -- Left and Right Distributivity

Reference : http://mathworld.wolfram.com/Semiring.html

-}

-- Proof for ℕ is Semiring
-- ∀ {a b c : S} → (a + b) + c = a + (b + c)

{-
indℕ : (C : ℕ → Set) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indℕ C z f 0 = z
indℕ C z f (suc n) = f n (indℕ C z f n)
-}

add-assoc : (i j k : ℕ) → i + (j + k) ≡ (i + j) + k
add-assoc = indℕ
              (λ i → (j k : ℕ) → i + (j + k) ≡ (i + j) + k)
              (λ j k → refl)
              (λ i i+[j+k]≡[i+j]+k j k → cong suc (i+[j+k]≡[i+j]+k j k))

-- ∀ {a : S} → a + 0 = 0 + a = a
add-right-unit : (i : ℕ) → i + 0 ≡ i
add-right-unit = indℕ (λ i →  i + 0 ≡ i) refl (λ i i+0≡i → cong suc i+0≡i) 


add-suc : (i j : ℕ) → suc (i + j) ≡ i + (suc j)
add-suc = indℕ (λ i → (j : ℕ) → suc (i + j) ≡ i + (suc j))
               (λ j → refl)
               (λ i s[i+j]≡i+s[j] j → cong suc (s[i+j]≡i+s[j] j))

-- ∀ {a b : S} → a + b = b + a
add-comm : (i j : ℕ) → i + j ≡ j + i
add-comm = indℕ
             (λ i → (j : ℕ) → i + j ≡ j + i)
             (λ j → sym (add-right-unit j))
             (λ i i+j≡j+i j → trans (cong suc (i+j≡j+i j)) (add-suc j i))

{-
indℕ : (C : ℕ → Set) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indℕ C c f 0 = c
indℕ C c f (suc n) = f n (indℕ C c f n)
-}



-- ∀ {a : S} → a * 1 = 1 * a = 1
mult-right-unit : (i : ℕ) → i * 1 ≡ i
mult-right-unit = indℕ (λ i → i * 1 ≡ i) refl (λ i i*1≡i → cong suc i*1≡i) 

--  ∀ {a b c : S} →  (a + b) * c = (a * c) + (b * c)
mult-right-dist : (i j k : ℕ) → (i + j) * k ≡ (i * k) + (j * k)
mult-right-dist = indℕ
                    (λ i → (j k : ℕ) → (i + j) * k ≡ (i * k) + (j * k))
                    (λ j k → refl)
                    (λ i [i+j]*k≡[i*k]+[j*k] j k → (begin
                                                    (suc i + j) * k ≡⟨ refl ⟩
                                                    (1 + i + j) * k ≡⟨ refl ⟩
                                                    k + (i + j) * k ≡⟨ cong (λ x → k + x) ([i+j]*k≡[i*k]+[j*k] j k) ⟩
                                                    k + (i * k + j * k) ≡⟨ add-assoc k (i * k) (j * k) ⟩
                                                    k + i * k + j * k ≡⟨ refl ⟩
                                                    suc i * k + j * k ∎)) 

--  ∀ {a b c : S} → a * (b + c) = (a * b) + (a * c)
mult-left-dist : (i j k : ℕ) → i * (j + k) ≡ (i * j) + (i * k)
mult-left-dist = indℕ
                    (λ i → (j k : ℕ) → i * (j + k) ≡ (i * j) + (i * k))
                    (λ j k → refl)
                    (λ i i*[j+k]≡[i*j]+[i*k] j k → (begin
                                                   suc i * (j + k) ≡⟨ refl ⟩
                                                   j + k + i * (j + k) ≡⟨ cong (λ x → j + k + x) (i*[j+k]≡[i*j]+[i*k] j k) ⟩
                                                   (j + k) + (i * j + i * k) ≡⟨ sym (add-assoc j k (i * j + i * k)) ⟩
                                                   j + (k + ((i * j) + (i * k))) ≡⟨ cong (λ x → j + x) (add-assoc k (i * j) (i * k)) ⟩
                                                   j + (k + i * j + i * k) ≡⟨ cong (λ x → j + (x + i * k)) (add-comm k (i * j)) ⟩
                                                   j + (((i * j) + k) + i * k) ≡⟨ cong (λ x → j + x) (sym (add-assoc (i * j) k (i * k))) ⟩
                                                   j + ((i * j) + (k + i * k)) ≡⟨ add-assoc j (i * j) (k + i * k) ⟩
                                                   j + i * j + (k + i * k) ≡⟨ refl ⟩
                                                   suc i * j + suc i * k ∎))                    

-- ∀ {a b c : S} → (a * b) * c = a * (b * c) -- Multiplicative Associativity
mult-assoc : (i j k : ℕ) →  i * (j * k) ≡ (i * j) * k
mult-assoc = indℕ
              (λ i → (j k : ℕ) → i * (j * k) ≡ (i * j) * k)
              (λ j k → refl)
              (λ i i*[j*k]≡[i*j]*k j k → (begin
                                          suc i * (j * k) ≡⟨ refl ⟩
                                          j * k + i * (j * k) ≡⟨ cong (λ x → j * k + x) (i*[j*k]≡[i*j]*k j k) ⟩
                                          j * k + (i * j) * k ≡⟨ sym (mult-right-dist j (i * j) k) ⟩
                                          (j + i * j) * k ≡⟨ refl ⟩
                                          suc i * j * k ∎))

-- ∀ {a : S} → a * 0 = 0 * a = 0
mult-right-zero : (i : ℕ) → i * 0 ≡ 0
mult-right-zero = indℕ (λ i → i * 0 ≡ 0)
                       refl
                       (λ i i*0≡0 → (begin
                                    suc i * 0 ≡⟨ refl ⟩
                                    (suc i) * 0 ≡⟨ refl ⟩
                                    i * 0 ≡⟨ i*0≡0 ⟩
                                    0 ∎)) 


-- Ex 1.9

data Fin : ℕ → Set where
    zero' : ∀ {n} → Fin (suc n) 
    suc' : ∀ {n} → Fin n → Fin (suc n)

Fin-Family : Set
Fin-Family = Σ ℕ (λ n → Fin n)

recFin : {n : ℕ} → (C : Set) → C → (C → C) → Fin n → C
recFin C z f zero' = z
recFin C z f (suc' a) = f (recFin C z f a)

fmax : (n : ℕ) → Fin (suc n)
fmax  = indℕ
           (λ m → (Fin (suc m)))
           zero'
           (λ m r → suc' r)
           

-- Ex 1.10

{-
ack : ℕ → ℕ → ℕ
ack 0 x = suc x
ack (suc x) 0 = ack x 1
ack (suc x) (suc y) = ack x (ack (suc x) y)
-}

ack-helper : (ℕ → ℕ) → ℕ → ℕ
ack-helper fun = recℕ ℕ (fun 1) (λ n → fun)

ack : ℕ → ℕ → ℕ
ack = recℕ (ℕ → ℕ) (λ n → suc n) (λ n → ack-helper)

-- Ex 1.11
¬ : Set → Set
¬ A = A → ⊥

neg1 : {A : Set} →
       (A → ¬ (¬ A)) → (¬ (¬ (¬ A))) → (¬ A)
neg1  f nna a     = nna (f a)

-- Ex 1.12
-- 1]
ex1 :  {A B : Set} → (A → (B → A)) 
ex1 = (λ a → λ b → a)

-- another
ex1' : {A B : Set} → A → (B → A)
ex1' a b = a

-- 2]
ex2 : {A : Set } → A → ((A → ⊥) → ⊥)
ex2 a na = na a

--3]
ex3 : {A B : Set} → ((¬ A) ⊎ (¬ B)) → (¬ (A × B))
ex3 (inj₁ na) (a , b) = na a 
ex3 (inj₂ nb) (a , b) = nb b

-- Ex 1.13
pf1 : {A : Set} → A → (¬ (¬ (A ⊎ ¬ A)))
pf1 a n[a⊎na] = n[a⊎na] (inj₁ a)

pf2 : {A : Set} → ¬ A → (¬ (¬ (A ⊎ ¬ A)))
pf2 na n[a⊎na] = n[a⊎na] (inj₂ na)

pf3 : {A : Set} → (¬ (A ⊎ (¬ A))) → ⊥
pf3 x = x (inj₂ (λ y → x (inj₁ y)))


-- Ex 1.14

try : {A : Set} → (x : A) → (p : x ≡ x) → (p ≡ refl)
try x refl = refl

-- But this function cannot be constructed using induction principle for identity types as both end points are fixed.
-- When we apply path induction this will result in ill-typed program.
-- For the family C : (a ≣ a) → Set, we cannot apply the induction principle and consider only the case for C reflₐ.

-- Reference class notes [ Ex 1.15 and 1.16 are handled in class ]

-- Ex 1.15
{-
data _≡_ {A : Set} : (x y : A) → Set where
  refl : (x : A) → x ≡ x
-}

rec≡ : {A : Set} →
       (R : A → A → Set) {reflexiveR : {a : A} → R a a} →
       ({x y : A} (p : x ≡ y) → R x y)
rec≡ R {reflR} (refl) = reflR -- {y}

rec≡S : {A : Set} {C : A → Set} →
        ({x y : A} (p : x ≡ y) → C x → C y)
rec≡S {C = C} p = rec≡ (λ a b → C a → C b) {id} p

ind≡ : {A : Set} → 
       (R : (x : A) → (y : A) → (p : x ≡ y) → Set)
       {reflexiveR : {a : A} → R a a (refl)} →
       ({x y : A} (p : x ≡ y) → R x y p)
ind≡ R {reflR} (refl) = reflR -- {y}

ind≡S : {A : Set} {C : A → Set} →
       ({x y : A} (p : x ≡ y) → C x → C y)
ind≡S {C = C} p = ind≡ (λ a b p → C a → C b) {id} p

-- Ex 1.16

{-
add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ n → n) (λ m r → λ n → suc (r n))

add-right-unit : (i : ℕ) → add i 0 ≡ i
add-right-unit = indℕ (λ i → add i 0 ≡ i) refl (λ i i+0≡i → cong suc i+0≡i) 
-}

add-comm' : (i j : ℕ) → i + j ≡ j + i
add-comm' = indℕ
             (λ i → (j : ℕ) → i + j ≡ j + i)
             (λ j → sym (add-right-unit j))
             (λ i i+j≡j+i j → trans (cong suc (i+j≡j+i j)) (add-suc j i))



{-

References :

1] HoTT Book
2] Asked some help from Kyle Carter in Agda Programming
3] http://agda.readthedocs.org/en/latest/language/index.html
4] http://www2.tcs.ifi.lmu.de/~abel/Equality.pdf
5] http://blog.ezyang.com/2013/06/homotopy-type-theory-chapter-one/
6] http://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html#mathematical-characters
7] http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism
8] http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.LocalDefinition?from=ReferenceManual.LocalDef

-}
