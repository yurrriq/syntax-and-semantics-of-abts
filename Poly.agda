{-# OPTIONS --type-in-type --without-K #-}
module Poly where

data 𝟘 : Set where

record 𝟙 : Set where
  constructor *
open 𝟙

module ≡ where
  data _t_ {A} x : A → Set where
    idn : x t x

  _∘_ : ∀ {A}{a b c : A} → b t c → a t b → a t c
  q ∘ idn = q

  inv : ∀ {A}{a b : A} → a t b → b t a
  inv idn = idn

  ap₁ : ∀ {A B a₀ a₁}(f : A → B) → a₀ t a₁ → f a₀ t f a₁
  ap₁ f idn = idn

  ap₂ : ∀ {A a₀ a₁}(P : A → Set) → a₀ t a₁ → (P a₀ → P a₁)
  ap₂ P idn = λ x → x

module ∐ where
  record t (A : Set) (B : A → Set) : Set where
    no-eta-equality
    constructor _,_
    field
      π₀ : A
      π₁ : B π₀

  infix 0 t
  syntax t A (λ x → B) = [ A ∋ x ] B
  open t public
open ∐ using (_,_)

module ∏ where
  record t (I : Set) (P : I → Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : ∀ {i} → P i

  infixr 1 t
  syntax t I (λ i → P) = [ I ∋ i ] P
  open t public

  idn : ∀ {A} → A → A
  idn x = x

  κ : ∀ {A B} → A → (B → A)
  κ a _ = a

  ! : ∀ {A} → A → (𝟙 → A)
  ! a * = a

  _∘_ : ∀ {A B C} → (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

module ⨛ where
  record t {I : Set} (P : I → Set) : Set where
    no-eta-equality
    constructor ι
    field
      {idx} : I
      π : P idx

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P
  open t public

module ⨜ where
  record t {I : Set} (P : I → Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : ∀ {i} → P i

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P
  open t public

_ᵒᵖ₀ : ∀ {𝒞} → 𝒞 → 𝒞
_ᵒᵖ₀ A = A

_ᵒᵖ₁
  : ∀ {𝒞}
  → (𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set)
  → (A : 𝒞 ᵒᵖ₀)
  → (B : 𝒞)
  → Set
(𝒞[_,_] ᵒᵖ₁) A B = 𝒞[ B , A ]

℘ : (X : Set) → Set
℘ X = X → Set

℘ᵒᵖ : (X : Set) → Set
℘ᵒᵖ X = X ᵒᵖ₀ → Set

SET[_,_] : Set ᵒᵖ₀ → Set → Set
SET[ A , B ] = A → B

℘[_,_] : ∀ {I} → (℘ I) ᵒᵖ₀ → ℘ I → Set
℘[ Ψ , Φ ] = ∀ {x} → Ψ x → Φ x

[_]⁻¹ : ∀ {E I} → (E → I) → ℘ I
[ p ]⁻¹ i = ∐.[ _ ∋ e ] (i ≡.t p e)

tot : ∀ {I} → ℘ I → Set
tot = ∐.t _

fib : ∀ {I} (ϕ : ℘ I) → (tot ϕ → I)
fib ϕ = ∐.π₀

record _↓[_]_ {𝒞 𝒟 𝒱 : Set}
  (F : 𝒞 → 𝒱)
  (𝒱[_,_] : 𝒱 ᵒᵖ₀ → 𝒱 → Set)
  (G : 𝒟 → 𝒱) : Set where
  no-eta-equality
  constructor ∃⟨_,_⟩↓_
  field
    dom : 𝒞
    cod : 𝒟
    map : 𝒱[ F dom , G cod ]
module ↓ where
  open _↓[_]_ public

_/_ : {𝒞 : Set} (𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set) (I : 𝒞) → Set
𝒞[_,_] / I = ∏.idn ↓[ 𝒞[_,_] ] ∏.! I

fam : ∀ {I} → ℘ I → SET[_,_] / I
fam ϕ = ∃⟨ tot ϕ , * ⟩↓ fib ϕ

pow : ∀ {I} → SET[_,_] / I → ℘ I
pow (∃⟨ dom , cod ⟩↓ map) = [ map ]⁻¹

Lan
  : {𝒞 𝒟 𝔙 : Set}
  → (𝒟[_,_] : 𝒟 ᵒᵖ₀ → 𝒟 → Set) (_⟦⊗⟧_ : 𝔙 → Set → Set)
  → (J : 𝒞 → 𝒟) (F : 𝒞 → 𝔙)
  → (𝒟 → Set)
Lan 𝒟[_,_] _⟦⊗⟧_ J F d = ⨛.[ _ ∋ c ] F c ⟦⊗⟧ 𝒟[ J c , d ]

Ran
  : {𝒞 𝒟 𝔙 : Set}
  → (𝒟[_,_] : 𝒟 ᵒᵖ₀ → 𝒟 → Set) (_⟦⋔⟧_ : Set → 𝔙 → Set)
  → (J : 𝒞 → 𝒟) (F : 𝒞 → 𝔙)
  → (𝒟 → Set)
Ran 𝒟[_,_] _⟦⋔⟧_ J F d = ⨜.[ _ ∋ c ] 𝒟[ d , J c ] ⟦⋔⟧ F c

module ⊗ where
  record _t_ (A : Set) (B : Set) : Set where
    no-eta-equality
    constructor _,_
    field
      π₀ : A
      π₁ : B
  infixr 1 _t_
  infixr 0 _,_
  open _t_ public
open ⊗ using (_,_)

module ⇒ where
  infixr 1 _∘_
  infixr 1 _∘Π_
  infixr 2 ![_]

  _t_ : (A B : Set) → Set
  A t B = A → B

  id : ∀ {A} → A → A
  id x = x

  _∘_ : ∀ {A B C} (g : B → C) (f : A → B) → (A → C)
  (g ∘ f) x = g (f x)

  _∘Π_
    : ∀ {A}{B : A → Set}{C : ∀ {a} (b : B a) → Set}
    → (g : ∀ {a} (b : B a) → C b)
    → (f : (a : A) → B a)
    → ((a : A) → C (f a))
  (g ∘Π f) x = g (f x)

  ![_]
    : ∀ {A B}
    → (a : A)
    → (B → A)
  ![_] a _ = a

  uncurry : ∀ {A B C} → (A t (B t C)) → ((A ⊗.t B) t C)
  uncurry f (a , b) = f a b

Σ : ∀ {A B} (f : A → B) → (℘ A → ℘ B)
Σ f = Lan ≡._t_ ⊗._t_ f

Δ : ∀ {A B} (f : A → B) → (℘ B → ℘ A)
Δ f = ⇒._∘ f

Π : ∀ {A B} (f : A → B) → (℘ A → ℘ B)
Π f = Ran ≡._t_ ⇒._t_ f

Σ⊣₀Δ
  : ∀ {A B}(f : A → B)(Φ : ℘ A)(Ψ : ℘ B)
  → ℘[ Σ f Φ , Ψ ]
  → ℘[ Φ , Δ f Ψ ]
Σ⊣₀Δ f Φ Ψ k {c} ϕ = k (⨛.ι (ϕ , ≡.idn))

Σ⊣₁Δ
  : ∀ {A B}(f : A → B)(Φ : ℘ A)(Ψ : ℘ B)
  → ℘[ Φ , Δ f Ψ ]
  → ℘[ Σ f Φ , Ψ ]
Σ⊣₁Δ f Φ Ψ k (⨛.ι (ϕ , p)) = ≡.ap₂ Ψ p (k ϕ)

Δ⊣₀Π
  : ∀ {A B}(f : A → B)(Φ : ℘ A)(Ψ : ℘ B)
  → ℘[ Δ f Ψ , Φ ]
  → ℘[ Ψ , Π f Φ ]
Δ⊣₀Π f Φ Ψ k {c} ψ = ⨜.ι λ p → k (≡.ap₂ Ψ p ψ)

Δ⊣₁Π
  : ∀ {A B}(f : A → B)(Φ : ℘ A)(Ψ : ℘ B)
  → ℘[ Ψ , Π f Φ ]
  → ℘[ Δ f Ψ , Φ ]
Δ⊣₁Π f Φ Ψ k {c} ψ = ⨜.π (k ψ) ≡.idn

module Nat where
  data t : Set where
    z : t
    s : t → t
  {-# BUILTIN NATURAL t #-}
open Nat using (z; s)

module Fin where
  data t : Nat.t → Set where
    z : ∀ {n} → t (Nat.s n)
    s : ∀ {n} → t n → t (Nat.s n)
open Fin using (z; s)

𝔽 : Set
𝔽 = Nat.t

𝔽[_,_] : 𝔽 → 𝔽 → Set
𝔽[ m , n ] = Fin.t m → Fin.t n

𝓎
  : ∀ {𝒞}
  → (𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set)
  → (𝒞 → ℘ᵒᵖ 𝒞)
𝓎 𝒞[_,_] B = 𝒞[_, B ]

𝓎ᵒᵖ : ∀ {𝒞}
  → (𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set)
  → (𝒞 ᵒᵖ₀ → ℘ 𝒞)
𝓎ᵒᵖ 𝒞[_,_] A = 𝒞[ A ,_]

∮
  : ∀ {𝒞}
  → (𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set)
  → (Ψ : ℘ᵒᵖ 𝒞)
  → Set
∮ 𝒞[_,_] Ψ = 𝓎 𝒞[_,_] ↓[ ℘[_,_] ᵒᵖ₁ ] ∏.! Ψ

∮ᵒᵖ
  : ∀ {𝒞}
  → (𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set)
  → (Ψ : ℘ 𝒞)
  → Set
∮ᵒᵖ 𝒞[_,_] Ψ = ∏.! Ψ ↓[ ℘[_,_] ] 𝓎ᵒᵖ 𝒞[_,_]

ex₀ : ∮ 𝔽[_,_] (λ n → n ≡.t 2)
ex₀ = ∃⟨ 2 , * ⟩↓ λ { {.2} ≡.idn → ∏.idn }

ex₁ : ∮ᵒᵖ 𝔽[_,_] (λ n → n ≡.t 2)
ex₁ = ∃⟨ * , 2 ⟩↓ λ { {.2} ≡.idn → ∏.idn }

SET⃗ : Set
SET⃗ = ∏.idn ↓[ SET[_,_] ] ∏.idn

∮π₀
  : ∀ {𝒞}
  → {𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set}
  → {Ψ : ℘ 𝒞}
  → ∮ 𝒞[_,_] Ψ → 𝒞
∮π₀ (∃⟨ dom , _ ⟩↓ _) = dom

∮π₁
  : ∀ {𝒞}
  → {𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set}
  → {Ψ : ℘ 𝒞}
  → ∮ 𝒞[_,_] Ψ → SET⃗
∮π₁ {Ψ = Ψ} (∃⟨ dom , cod ⟩↓ map) = ∃⟨ Ψ dom , Ψ dom ⟩↓ ∏.idn

coh
  : ∀ {𝒞}
  → {𝒞[_,_] : 𝒞 ᵒᵖ₀ → 𝒞 → Set}
  → {Ψ : ℘ 𝒞}
  → (𝔊 : ∮ 𝒞[_,_] Ψ)
  → Ψ (∮π₀ 𝔊) ≡.t ↓.cod (∮π₁ 𝔊)
coh (∃⟨ dom , cod ⟩↓ map) = ≡.idn
