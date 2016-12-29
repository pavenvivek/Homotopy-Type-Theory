
module Eckmann-Hilton where

infixr 8  _∘_     -- path composition
infix  4  _≡_     -- propositional equality

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

-- Equational Reasoning operators

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin_ p1 = p1

_≡⟨_⟩_ : {A : Set} → (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p1 ⟩ p2 = p1 ∘ p2

_∎ : {A : Set} → (a : A) → a ≡ a
_∎ a = refl a

-- p = p ∘ refl

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y) 
unitTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ p ∘ (refl y)) 
    (λ x → refl (refl x))
    {x} {y} p 

-- p = refl ∘ p

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p 

-- p ∘ (q ∘ r) = (p ∘ q) ∘ r

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

--

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd -- on p
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

------------------------------------------------------------------------------
-- Path and loop spaces

1-Paths : (A : Set) → {a b : A} → Set
1-Paths A {a} {b} = (a ≡ b)

2-Paths : (A : Set) → {a b : A} {p q : 1-Paths A {a} {b}} → Set
2-Paths A {a} {b} {p} {q} = (p ≡ q)

-- Loop space
Ω : (A : Set) → {a : A} → Set
Ω A {a} = 1-Paths A {a} {a}

-- 2d Loop Space
Ω² : (A : Set) → {a : A} → Set
Ω² A {a} = 2-Paths A {a} {a} {refl a} {refl a}


-- Whiskering to the right
whisker-right : {A : Set} → {a b c : A}
                → {p q : (1-Paths A {a} {b})}
                → (α : (2-Paths A {a} {b} {p} {q}))
                → (r : (1-Paths A {b} {c}))
                → (p ∘ r) ≡ (q ∘ r)
whisker-right {A} {a} {b} {c} {p} {q} α r = pathInd (λ {b} {c} r → {p q : (1-Paths A {a} {b})} → (α : (2-Paths A {a} {b} {p} {q})) → (p ∘ r) ≡ (q ∘ r))
                                            (λ b {p} {q} α → begin
                                                              p ∘ refl b ≡⟨ ! (unitTransR p) ⟩
                                                              p ≡⟨ α ⟩
                                                              q ≡⟨ unitTransR q ⟩
                                                              q ∘ refl b ∎)
                                            r α

-- Whiskering to the left
whisker-left : {A : Set} → {a b c : A}
                → {r s : (1-Paths A {b} {c})}
                → (q : (1-Paths A {a} {b}))
                → (β : (2-Paths A {b} {c} {r} {s}))
                → (q ∘ r) ≡ (q ∘ s)
whisker-left {A} {a} {b} {c} {r} {s} q β = pathInd (λ {a} {b} q → {r s : (1-Paths A {b} {c})} → (β : (2-Paths A {b} {c} {r} {s})) → (q ∘ r) ≡ (q ∘ s))
                                            (λ b {r} {s} β → begin
                                                              refl b ∘ r ≡⟨ ! (unitTransL r) ⟩
                                                              r ≡⟨ β ⟩
                                                              s ≡⟨ unitTransL s ⟩
                                                              refl b ∘ s ∎)
                                            q β

-- horizontal composition 1 (hc1)
_⋆_ : {A : Set} → {a b c : A}
      → {p q : (1-Paths A {a} {b})}
      → {r s : (1-Paths A {b} {c})}
      → (α : (2-Paths A {a} {b} {p} {q}))
      → (β : (2-Paths A {b} {c} {r} {s}))
      → (p ∘ r) ≡ (q ∘ s)
_⋆_ {A} {a} {b} {c} {p} {q} {r} {s} α β  = (whisker-right α r) ∘ (whisker-left q β)


-- horizontal composition 2 (hc2)
_⋆'_ : {A : Set} → {a b c : A}
       → {p q : (1-Paths A {a} {b})}
       → {r s : (1-Paths A {b} {c})}
       → (α : (2-Paths A {a} {b} {p} {q}))
       → (β : (2-Paths A {b} {c} {r} {s}))
       → (p ∘ r) ≡ (q ∘ s)
_⋆'_ {A} {a} {b} {c} {p} {q} {r} {s} α β  = (whisker-left p β) ∘ (whisker-right α s)

hc1≡hc2 : {A : Set} → {a b c : A}
          → {p q : (1-Paths A {a} {b})}
          → {r s : (1-Paths A {b} {c})}
          → (α : (2-Paths A {a} {b} {p} {q}))
          → (β : (2-Paths A {b} {c} {r} {s}))
          → (α ⋆ β) ≡ (α ⋆' β)
hc1≡hc2 {A} {a} {b} {c} {p} {q} {r} {s} α β  = pathInd (λ {r} {s} β → (α ⋆ β) ≡ (α ⋆' β))
                                                 (λ r →
                                                    pathInd (λ {p} {q} α → (α ⋆ refl r) ≡ (α ⋆' refl r))
                                                      (λ p →
                                                         pathInd (λ {a} {b} p → (c : A) → (r : b ≡ c) → (refl p ⋆ refl r) ≡ (refl p ⋆' refl r))
                                                           (λ a₁ c₁ r₁ →
                                                              pathInd (λ {a₂} {c₂} r₂ → refl (refl a₂) ⋆ refl r₂ ≡ refl (refl a₂) ⋆' refl r₂)
                                                                (λ a₂ → refl (refl (refl a₂)))
                                                                r₁)
                                                           p c r)
                                                      α)
                                                 β

α⋆β≡α∘β : {A : Set} → {a : A} → (α β : Ω² A {a}) → α ⋆ β ≡ α ∘ β
α⋆β≡α∘β {A} {a} α β = begin
                       α ⋆ β ≡⟨ refl _ ⟩
                       (whisker-right α (refl a)) ∘ (whisker-left (refl a) β) ≡⟨ refl _ ⟩
                       (refl (refl a) ∘ α ∘ unitTransR (refl a)) ∘ (unitTransL (refl a)  ∘ β ∘ unitTransL (refl a)) ≡⟨ refl _ ⟩
                       (refl (refl a) ∘ (α ∘ refl (refl a))) ∘ (refl (refl a) ∘ (β ∘ refl (refl a))) ≡⟨ ap
                                                                                                          (λ x → (refl (refl a) ∘ x) ∘ (refl (refl a) ∘ β ∘ refl (refl a)))
                                                                                                          (! (unitTransR α)) ⟩
                       (refl (refl a) ∘ α) ∘ (refl (refl a) ∘ (β ∘ refl (refl a))) ≡⟨ ap
                                                                                        (λ x → (refl (refl a) ∘ α) ∘ (refl (refl a) ∘ x))
                                                                                        (! (unitTransR β)) ⟩
                       (refl (refl a) ∘ α) ∘ (refl (refl a) ∘ β) ≡⟨ ap
                                                                      (λ x → x ∘ refl (refl a) ∘ β)
                                                                      (! (unitTransL α)) ⟩
                       α ∘ (refl (refl a) ∘ β) ≡⟨ ap
                                                    (λ x → α ∘ x)
                                                    (! (unitTransL β)) ⟩
                       α ∘ β ∎

α⋆'β≡β∘α : {A : Set} → {a : A} → (α β : Ω² A {a}) → α ⋆' β ≡ β ∘ α
α⋆'β≡β∘α {A} {a} α β = begin
                        α ⋆' β ≡⟨ refl _ ⟩
                        (whisker-left (refl a) β) ∘ (whisker-right α (refl a)) ≡⟨ refl _ ⟩
                        (unitTransL (refl a)  ∘ β ∘ unitTransL (refl a)) ∘ (refl (refl a) ∘ α ∘ unitTransR (refl a)) ≡⟨ refl _ ⟩
                        (refl (refl a) ∘ (β ∘ refl (refl a))) ∘ (refl (refl a) ∘ (α ∘ refl (refl a))) ≡⟨ ap
                                                                                                           (λ x → (refl (refl a) ∘ x) ∘ (refl (refl a) ∘ α ∘ refl (refl a)))
                                                                                                           (! (unitTransR β)) ⟩
                        (refl (refl a) ∘ β) ∘ (refl (refl a) ∘ (α ∘ refl (refl a))) ≡⟨ ap
                                                                                         (λ x → (refl (refl a) ∘ β) ∘ refl (refl a) ∘ x)
                                                                                         (! (unitTransR α)) ⟩
                        (refl (refl a) ∘ β) ∘ (refl (refl a) ∘ α) ≡⟨ ap
                                                                       (λ x → x ∘ refl (refl a) ∘ α)
                                                                       (! (unitTransL β)) ⟩
                        β ∘ (refl (refl a) ∘ α) ≡⟨ ap
                                                     (λ x → β ∘ x)
                                                     (! (unitTransL α)) ⟩
                        β ∘ α ∎

eckmann_hilton : {A : Set} → {a : A} → (α β : Ω² A {a}) → α ∘ β ≡ β ∘ α
eckmann_hilton {A} {a} α β = begin
                             α ∘ β ≡⟨ ! (α⋆β≡α∘β α β) ⟩
                             α ⋆ β ≡⟨ hc1≡hc2 α β ⟩
                             α ⋆' β ≡⟨ α⋆'β≡β∘α α β ⟩
                             β ∘ α ∎
