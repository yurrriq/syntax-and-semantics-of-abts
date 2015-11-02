\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where

infix 0 ∐
infixr 0 _,_
infixr 1 _⊗_
infixr 2 _~>_

_~>_ : ∀ {𝒞} (F G : 𝒞 → Set) → Set
F ~> G = ∀ {c} → F c → G c

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

module ⨜ where
  record t {I : Set} (P : I → Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : ∀ i → P i
  open t public

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P

module ⨛ where
  record t {I : Set} (P : I → Set) : Set where
    no-eta-equality
    constructor ι
    field
      {π₀} : I
      π₁ : P π₀
  open t public

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P

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

module Var where
  record t (n : Nat.t) : Set where
    no-eta-equality
    constructor ι
    field
      π : Fin.t n
  open t public

module Sym where
  record t (n : Nat.t) : Set where
    no-eta-equality
    constructor ι
    field
      π : Fin.t n
  open t public

module TCtx where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      tlen : Nat.t
    tdom : Set
    tdom = Var.t tlen
    field
      tidx : tdom → 𝒮
    infix 1 tlen
    syntax tlen Γ = #t Γ
    syntax tidx Γ x = Γ [ x ]t
  open t public
open TCtx hiding (t; ι)

_⧺_ : ∀ {𝒮 : Set} (Γ Δ : TCtx.t 𝒮) → TCtx.t 𝒮
_⧺_ {𝒮} Γ Δ = TCtx.ι (#t Γ Nat.+ #t Δ) aux
  where
    aux : (i : Var.t (#t Γ Nat.+ #t Δ)) → 𝒮
    aux (Var.ι i) with Fin.split (#t Γ) (#t Δ) i
    aux (Var.ι .(Fin.inl        i)) | Fin.split-inl i = Γ [ Var.ι i ]t
    aux (Var.ι .(Fin.inr {#t Γ} j)) | Fin.split-inr j = Δ [ Var.ι j ]t

module SCtx where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      slen : Nat.t
    sdom : Set
    sdom = Sym.t slen
    field
      sidx : sdom → 𝒮
    infix 1 slen
    syntax slen Γ = #t Γ
    syntax sidx Γ x = Γ [ x ]s
  open t public
open SCtx hiding (t; ι)

_∋⟨_,_⟩s : ∀ {𝒮} (Υ : SCtx.t 𝒮) (x : sdom Υ ) (s : 𝒮) → Set
Υ ∋⟨ x , s ⟩s = Υ [ x ]s ≡.t s

_∋⟨_,_⟩t : ∀ {𝒮} (Γ : TCtx.t 𝒮) (x : tdom Γ ) (s : 𝒮) → Set
Γ ∋⟨ x , s ⟩t = Γ [ x ]t ≡.t s

module 𝒱 where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : SCtx.t 𝒮 ⊗ TCtx.t 𝒮 ⊗ 𝒮
  open t public

module 𝒜 where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : TCtx.t (𝒱.t 𝒮) ⊗ 𝒮
  open t public

module MCtx where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : TCtx.t (𝒱.t 𝒮)
  open t public

module TRen where
  record t {A} (Γ Δ : TCtx.t A) : Set where
    no-eta-equality
    constructor ρ
    field
      map : tdom Γ → tdom Δ
      coh : ∀ {i} → Γ [ i ]t ≡.t Δ [ map i ]t
  open t public

  t↪cmp
    : {A : Set} {Γ : TCtx.t A} {Δ : TCtx.t A}
    → (Η : TCtx.t A)
    → (g : t Δ Η)
    → (f : t Γ Δ)
    → t Γ Η
  t↪cmp H g f = ρ (map g Π.∘ map f) (coh g ≡.∘ coh f)

  syntax t↪cmp H g f = g ↪∘[ H ]t f
open TRen using (t↪cmp)

_↪t_ : ∀ {A} (Γ Δ : TCtx.t A) → Set
Γ ↪t Δ = TRen.t Γ Δ

module SRen where
  record t {A} (Υ Υ′ : SCtx.t A) : Set where
    no-eta-equality
    constructor ρ
    field
      map : sdom Υ → sdom Υ′
      coh : ∀ {i} → Υ [ i ]s ≡.t Υ′ [ map i ]s
  open t public

  s↪cmp
    : {A : Set} {Υ : SCtx.t A} {Υ′ : SCtx.t A}
    → (Η : SCtx.t A)
    → (g : t Υ′ Η)
    → (f : t Υ Υ′)
    → t Υ Η
  s↪cmp H g f = ρ (map g Π.∘ map f) (coh g ≡.∘ coh f)

  syntax s↪cmp H g f = g ↪∘[ H ]s f
open SRen using (s↪cmp)

_↪s_ : ∀ {A} (Υ Υ′ : SCtx.t A) → Set
Υ ↪s Υ′ = SRen.t Υ Υ′

module Sign where
  record t : Set₁ where
    no-eta-equality
    constructor ι
    field
      𝒮 : Set
      𝒪 : SCtx.t 𝒮 ⊗ 𝒜.t 𝒮 → Set
      map : ∀ {a Υ Υ′} → Υ ↪s Υ′ → (𝒪 (Υ , a) → 𝒪 (Υ′ , a))
  open t public

data _∣_∥_⊢_
  (Σ : Sign.t)
  (Υ : SCtx.t (Sign.𝒮 Σ))
  (Γ : TCtx.t (Sign.𝒮 Σ))
    : (s : Sign.𝒮 Σ) → Set where
  v : ∀ {x s}
    → (ϕ : Γ ∋⟨ x , s ⟩t)
    → Σ ∣ Υ ∥ Γ ⊢ s

module _ (Σ : Sign.t) where
  -- infixr 1 _⊗↑_

  module H where
    record t : Set where
      no-eta-equality
      constructor ι
      field
        π : SCtx.t (Sign.𝒮 Σ) ⊗ TCtx.t (Sign.𝒮 Σ)
    open t public
  pattern _∥_ Υ Γ = H.ι (Υ , Γ)

  module H↑ where
    record t : Set where
      no-eta-equality
      constructor ι
      field
        π : H.t → Set
    open t public

  abstract
    *𝒴 : Set
    *𝒴 = H.t → H↑.t

    𝓎 : *𝒴
    𝓎 (Υ ∥ Γ) = H↑.ι λ { (Υ′ ∥ Δ) → (Υ ↪s Υ′) ⊗ (Γ ↪t Δ) }

    *𝓎→ : (H.t → H↑.t) → *𝒴
    *𝓎→ x = x

    *𝓎← : *𝒴 → (H.t → H↑.t)
    *𝓎← x = x

  ⟪𝓎⟫ : H.t → H↑.t
  ⟪𝓎⟫ x = *𝓎← 𝓎 x

  _~>_ : ∀ {𝒞} (F G : 𝒞 → Set) → Set
  F ~> G = ∀ {c} → F c → G c

  abstract
    *⊗↑ : Set
    *⊗↑ = H↑.t → H↑.t → H↑.t

    _⊗↑_ : *⊗↑
    (A ⊗↑ B) = H↑.ι λ h → H↑.π A h ⊗ H↑.π B h

    *⊗↑→ : (H↑.t → H↑.t → H↑.t) → *⊗↑
    *⊗↑→ x = x

    *⊗↑← : *⊗↑ → (H↑.t → H↑.t → H↑.t)
    *⊗↑← x = x

  _⟪⊗↑⟫_ : H↑.t → H↑.t → H↑.t
  A ⟪⊗↑⟫ B = *⊗↑← _⊗↑_ A B

  _↗_ : H↑.t → H↑.t → H↑.t
  (B ↗ A) = H↑.ι λ h → H↑.π (⟪𝓎⟫ h ⟪⊗↑⟫ A) ~> H↑.π B

  abstract
    *S : Set
    *S = Sign.𝒮 Σ → H↑.t

    S : *S
    S s = H↑.ι λ { (Υ ∥ Γ) → ∐[ sdom Υ ∋ x ] Υ ∋⟨ x , s ⟩s }

    S→ : (Sign.𝒮 Σ → H↑.t) → *S
    S→ x = x

    S← : *S → (Sign.𝒮 Σ → H↑.t)
    S← x = x

  abstract
    *V : Set
    *V = Sign.𝒮 Σ → H↑.t

    V : *V
    V s = H↑.ι λ { (Υ ∥ Γ) → ∐[ tdom Γ ∋ x ] Γ ∋⟨ x , s ⟩t }

    V→ : (Sign.𝒮 Σ → H↑.t) → *V
    V→ x = x

    V← : *V → (Sign.𝒮 Σ → H↑.t)
    V← x = x

  _⊢_ : (Υ∥Γ : H.t) (s : Sign.𝒮 Σ) → Set
  (Υ ∥ Γ) ⊢ s = Σ ∣ Υ ∥ Γ ⊢ s

  abstract
    *↗[]t : Set
    *↗[]t = (X : (s : Sign.𝒮 Σ) → H↑.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → H↑.t

    _↗[_]t : *↗[]t
    X ↗[ Γ ]t = H↑.ι λ h → ⨜.[ tdom Γ ∋ x ] H↑.π (X (Γ [ x ]t)) h

    *↗[]t→ : ((X : (s : Sign.𝒮 Σ) → H↑.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → H↑.t) → *↗[]t
    *↗[]t→ x = x

    *↗[]t← : *↗[]t → ((X : (s : Sign.𝒮 Σ) → H↑.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → H↑.t)
    *↗[]t← x = x

  abstract
    *↗[]s : Set
    *↗[]s = (X : (s : Sign.𝒮 Σ) → H↑.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → H↑.t

    _↗[_]s : *↗[]s
    X ↗[ Υ ]s = H↑.ι λ h → ⨜.[ sdom Υ ∋ x ] H↑.π (X (Υ [ x ]s)) h

    *↗[]s→ : ((X : (s : Sign.𝒮 Σ) → H↑.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → H↑.t) → *↗[]s
    *↗[]s→ x = x

    *↗[]s← : *↗[]s → ((X : (s : Sign.𝒮 Σ) → H↑.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → H↑.t)
    *↗[]s← x = x

  abstract
    *⊚ : Set
    *⊚ = (A : H↑.t) (P : (s : Sign.𝒮 Σ) → H↑.t) → H↑.t

    _⊚_ : *⊚
    (A ⊚ P) = H↑.ι λ h →
      ⨛.[ H.t ∋ h′ ] let Υ′ ∥ Δ = h′ in
        H↑.π A (Υ′ ∥ Δ)
          ⊗ H↑.π (S ↗[ Υ′ ]s) h
          ⊗ H↑.π (P ↗[ Δ  ]t) h

    *⊚→ : ((A : H↑.t) (P : (s : Sign.𝒮 Σ) → H↑.t) → H↑.t) → *⊚
    *⊚→ x = x

    *⊚← : *⊚ → ((A : H↑.t) (P : (s : Sign.𝒮 Σ) → H↑.t) → H↑.t)
    *⊚← x = x
\end{code}
