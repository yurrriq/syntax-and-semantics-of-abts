\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where

infix 0 ∐
infixr 1 ⨛
infixr 1 ⨜
infixr 0 _,_
infixr 1 _⊗_

module ≡ where
  infix 0 _t_
  data _t_ {A} x : A → Set where
    refl : x t x

  _∘_
    : {A : Set}
    → {x y z : A}
    → (p : y t z)
    → (q : x t y)
    → x t z
  refl ∘ q = q

  sym
    : {A : Set}
    → {x y : A}
    → (p : x t y)
    → y t x
  sym refl = refl

module Π where
  infixr 1 _∘_
  infixr 1 _∘Π_
  infixr 2 ![_]

  _⇒_ : (A B : Set) → Set
  A ⇒ B = A → B

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

record ∐ (A : Set) (B : A → Set) : Set where
  no-eta-equality
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀

syntax ∐ A (λ x → B) = ∐[ A ∋ x ] B

record _⊗_ (A : Set) (B : Set) : Set where
  no-eta-equality
  constructor _,_
  field
    π₀ : A
    π₁ : B

⟨_,_⟩
  : ∀ {X A B}
  → (f : X → A)
  → (g : X → B)
  → ((x : X) → A ⊗ B)
⟨ f , g ⟩ x = f x , g x

record ⨜  {I : Set} (P : I → Set) : Set where
  no-eta-equality
  constructor λ↓
  field
    _·_ : ∀ i → P i

syntax ⨜ {I = I} (λ i → P) = ⨜[ I ∋ i ] P

record ⨛ {I : Set} (P : I → Set) : Set where
  no-eta-equality
  constructor s↑
  field
    {π₀} : I
    π₁ : P π₀

syntax ⨛ {I = I} (λ i → P) = ⨛[ I ∋ i ] P

module Nat where
  infix 0 _+_
  data t : Set where
    ze : t
    su : (n : t) → t

  _+_ : t → t → t
  ze + n = n
  su m + n = su (m + n)

module Fin where
  data t : (n : Nat.t) → Set where
    ze : ∀ {n} → t (Nat.su n)
    su : ∀ {n} → t n → t (Nat.su n)

  nat : ∀ {n} → t n → Nat.t
  nat ze = Nat.ze
  nat (su n) = Nat.su (nat n)

  inl : ∀ {m n} → t m → t (m Nat.+ n)
  inl {Nat.ze} ()
  inl {Nat.su m} ze = ze
  inl {Nat.su m} (su i) = su (inl i)

  inr : ∀ {m n} → t n → t (m Nat.+ n)
  inr {Nat.ze} i = i
  inr {Nat.su m} i = su (inr {m} i)

  data Split (m n : Nat.t) : t (m Nat.+ n) → Set where
    split-inl : (i : t m) → Split m n (inl {m} {n} i)
    split-inr : (j : t n) → Split m n (inr {m} {n} j)

  split : (m n : Nat.t) → (i : t (m Nat.+ n)) → Split m n i
  split Nat.ze n i = split-inr i
  split (Nat.su m) n ze = split-inl ze
  split (Nat.su m) n (su i) with split m n i
  split (Nat.su m) n (su ._) | split-inl i = split-inl (su i)
  split (Nat.su m) n (su ._) | split-inr j = split-inr j

record Var (n : Nat.t) : Set where
  no-eta-equality
  constructor var
  field
    π : Fin.t n

record Sym (n : Nat.t) : Set where
  no-eta-equality
  constructor sym
  field
    π : Fin.t n

record TCtx (𝒮 : Set) : Set where
  constructor tctx
  no-eta-equality
  field
    tlen : Nat.t
  tdom : Set
  tdom = Var tlen
  field
    tidx : tdom → 𝒮
  infix 1 tlen
  syntax tlen Γ = #t Γ
  syntax tidx Γ x = Γ [ x ]t
open TCtx

_⧺_ : ∀ {𝒮 : Set} (Γ Δ : TCtx 𝒮) → TCtx 𝒮
_⧺_ {𝒮} Γ Δ = tctx (#t Γ Nat.+ #t Δ) aux
  where
    aux : (i : Var (#t Γ Nat.+ #t Δ)) → 𝒮
    aux (var i) with Fin.split (#t Γ) (#t Δ) i
    aux (var .(Fin.inl        i)) | Fin.split-inl i = Γ [ var i ]t
    aux (var .(Fin.inr {#t Γ} j)) | Fin.split-inr j = Δ [ var j ]t

record SCtx (𝒮 : Set) : Set where
  no-eta-equality
  field
    slen : Nat.t
  sdom : Set
  sdom = Sym slen
  field
    sidx : sdom → 𝒮
  infix 1 slen
  syntax slen Γ = #t Γ
  syntax sidx Γ x = Γ [ x ]s
open SCtx

_∋⟨_,_⟩ : ∀ {𝒮} (Γ : TCtx 𝒮) (x : tdom Γ ) (s : 𝒮) → Set
Γ ∋⟨ x , s ⟩ = Γ [ x ]t ≡.t s

record 𝒱 (𝒮 : Set) : Set where
  no-eta-equality
  constructor 𝓋
  field
    π : SCtx 𝒮 ⊗ TCtx 𝒮 ⊗ 𝒮

record 𝒜 (𝒮 : Set) : Set where
  no-eta-equality
  constructor 𝒶
  field
    π : TCtx (𝒱 𝒮) ⊗ 𝒮

record MCtx (𝒮 : Set) : Set where
  no-eta-equality
  constructor 𝓂
  field
    π : TCtx (𝒱 𝒮)

module TRen where
  record t {A} (Γ Δ : TCtx A) : Set where
    no-eta-equality
    constructor ρ
    field
      map : tdom Γ → tdom Δ
      coh : ∀ {i} → Γ [ i ]t ≡.t Δ [ map i ]t
  open t

  cmp
    : {A : Set} {Γ : TCtx A} {Δ : TCtx A}
    → (Η : TCtx A)
    → (g : t Δ Η)
    → (f : t Γ Δ)
    → t Γ Η
  cmp H g f = ρ (map g Π.∘ map f) (coh g ≡.∘ coh f)

_↪t_ : ∀ {A} (Γ Δ : TCtx A) → Set
Γ ↪t Δ = TRen.t Γ Δ

module SRen where
  record t {A} (Υ Υ′ : SCtx A) : Set where
    no-eta-equality
    constructor ρ
    field
      map : sdom Υ → sdom Υ′
      coh : ∀ {i} → Υ [ i ]s ≡.t Υ′ [ map i ]s
  open t

  cmp
    : {A : Set} {Υ : SCtx A} {Υ′ : SCtx A}
    → (Η : SCtx A)
    → (g : t Υ′ Η)
    → (f : t Υ Υ′)
    → t Υ Η
  cmp H g f = ρ (map g Π.∘ map f) (coh g ≡.∘ coh f)
_↪s_ : ∀ {A} (Υ Υ′ : SCtx A) → Set
Υ ↪s Υ′ = SRen.t Υ Υ′

record Sign : Set₁ where
  no-eta-equality
  constructor sign
  field
    𝒮 : Set
    𝒪 : SCtx 𝒮 ⊗ 𝒜 𝒮 → Set
    map : ∀ {a Υ Υ′} → Υ ↪s Υ′ → (𝒪 (Υ , a) → 𝒪 (Υ′ , a))

data _∣_∥_⊢_
  (Σ : Sign)
  (Υ : SCtx (Sign.𝒮 Σ))
  (Γ : TCtx (Sign.𝒮 Σ))
    : (s : Sign.𝒮 Σ) → Set where
  v : ∀ {x s}
    → (ϕ : Γ ∋⟨ x , s ⟩)
    → Σ ∣ Υ ∥ Γ ⊢ s

module _ (Σ : Sign) where

  record H : Set where
    no-eta-equality
    constructor h
    field
      π : SCtx (Sign.𝒮 Σ) ⊗ TCtx (Sign.𝒮 Σ)
  pattern _∥_ Υ Δ = h (Υ , Δ)

  record H↑ : Set where
    no-eta-equality
    constructor h↑
    field
      π : H → Set
\end{code}
