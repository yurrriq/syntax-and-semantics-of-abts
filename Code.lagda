\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where

infix 2 _[_]a→Γ
infix 2 _[_]a→Υ
infix 2 _[_]a→τ
infix 2 _[_]m→Γ
infix 2 _[_]m→Υ
infix 2 _[_]m→τ
infixr 0 _⧺s_
infixr 0 _⧺t_
infixr 2 _~>_

-- equality
module ≡ where
  infix 0 _t_
  data _t_ {A} x : A → Set where
    idn : x t x

  _∘_
    : {A : Set}
    → {x y z : A}
    → (p : y t z)
    → (q : x t y)
    → x t z
  idn ∘ q = q

  inv
    : {A : Set}
    → {x y : A}
    → (p : x t y)
    → y t x
  inv idn = idn

  map
    : ∀ {A}{a b}
    → (P : A → Set)
    → (f : a t b)
    → (P a → P b)
  map P idn x = x

-- products
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

-- functions
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

⟨_,_⟩
  : ∀ {X A B}
  → (f : X → A)
  → (g : X → B)
  → ((x : X) → A ⊗.t B)
⟨ f , g ⟩ x = f x , g x

⟨_⊗_⟩
  : ∀ {X Y A B}
  → (f : X → A)
  → (g : Y → B)
  → (X ⊗.t Y → A ⊗.t B)
⟨ f ⊗ g ⟩ = ⟨ f ⇒.∘ ⊗.π₀ , g ⇒.∘ ⊗.π₁ ⟩

𝔓 : (X : Set) → Set
𝔓 X = X → Set

_~>_ : ∀ {𝒞} (F G : 𝔓 𝒞) → Set
F ~> G = ∀ {c} → F c → G c

-- dependent coproduct
module ∐ where
  record t (A : Set) (B : 𝔓 A) : Set where
    no-eta-equality
    constructor _,_
    field
      π₀ : A
      π₁ : B π₀

  infix 0 t
  syntax t A (λ x → B) = [ A ∋ x ] B
  open t public

-- dependent product
module ∏ where
  record t (I : Set) (P : 𝔓 I) : Set where
    no-eta-equality
    constructor ι
    field
      π : ∀ i → P i
  open t public

  infixr 1 t
  syntax t I (λ i → P) = [ I ∋ i ] P
  open t public

-- coend
module ⨛ where
  record t {I : Set} (P : 𝔓 I) : Set where
    no-eta-equality
    constructor ι
    field
      {idx} : I
      π : P idx
  open t public

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P

  into : {I : Set} {P : 𝔓 I} (i : I) → P i → t P
  into = λ {I} {P} i → ι

-- end
module ⨜ where
  record t {I : Set} (P : 𝔓 I) : Set where
    no-eta-equality
    constructor ι
    field
      π : ∀ {i} → P i
  open t public

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P

  π[_] : {I : Set} (i : I) {P : I → Set} → t P → P i
  π[ i ] = λ z → π z

record SET↓ (I : Set) : Set where
  no-eta-equality
  constructor ∃_↓_
  field
    dom : Set
    map : dom → I

[_]⁻¹ : ∀ {E I} → (E → I) → 𝔓 I
[ p ]⁻¹ i = ∐.[ _ ∋ e ] (i ≡.t p e)

tot : ∀ {I} → 𝔓 I → Set
tot = ∐.t _

fib : ∀ {I} (ϕ : 𝔓 I) → (tot ϕ → I)
fib ϕ = ∐.π₀

fam : ∀ {I} → 𝔓 I → SET↓ I
fam ϕ = ∃ tot ϕ ↓ fib ϕ

pow : ∀ {I} → SET↓ I → 𝔓 I
pow (∃ dom ↓ map) = [ map ]⁻¹

Lan
  : {𝒞 𝒟 𝔙 : Set}
  → (𝒟[_,_] : 𝒟 → 𝒟 → Set) (_⟦⊗⟧_ : 𝔙 → Set → Set)
  → (J : 𝒞 → 𝒟) (F : 𝒞 → 𝔙)
  → (𝒟 → Set)
Lan 𝒟[_,_] _⟦⊗⟧_ J F d = ⨛.[ _ ∋ c ] F c ⟦⊗⟧ 𝒟[ J c , d ]

Ran
  : {𝒞 𝒟 𝔙 : Set}
  → (𝒟[_,_] : 𝒟 → 𝒟 → Set) (_⟦⋔⟧_ : Set → 𝔙 → Set)
  → (J : 𝒞 → 𝒟) (F : 𝒞 → 𝔙)
  → (𝒟 → Set)
Ran 𝒟[_,_] _⟦⋔⟧_ J F d = ⨜.[ _ ∋ c ] 𝒟[ d , J c ] ⟦⋔⟧ F c

Σ : ∀ {A B} (f : A → B) → (𝔓 A → 𝔓 B)
Σ f = Lan ≡._t_ ⊗._t_ f

Δ : ∀ {A B} (f : A → B) → (𝔓 B → 𝔓 A)
Δ f = ⇒._∘ f

Π : ∀ {A B} (f : A → B) → (𝔓 A → 𝔓 B)
Π f = Ran ≡._t_ ⇒._t_ f

𝔓[_,_] : _
𝔓[_,_] = _~>_

Σ⊣₀Δ
  : ∀ {A B}(f : A → B)(Φ : 𝔓 A)(Ψ : 𝔓 B)
  → 𝔓[ Σ f Φ , Ψ ]
  → 𝔓[ Φ , Δ f Ψ ]
Σ⊣₀Δ f Φ Ψ k {c} ϕ = k (⨛.ι (ϕ , ≡.idn))

Σ⊣₁Δ
  : ∀ {A B}(f : A → B)(Φ : 𝔓 A)(Ψ : 𝔓 B)
  → 𝔓[ Φ , Δ f Ψ ]
  → 𝔓[ Σ f Φ , Ψ ]
Σ⊣₁Δ f Φ Ψ k (⨛.ι (ϕ , p)) = ≡.map Ψ p (k ϕ)

Δ⊣₀Π
  : ∀ {A B}(f : A → B)(Φ : 𝔓 A)(Ψ : 𝔓 B)
  → 𝔓[ Δ f Ψ , Φ ]
  → 𝔓[ Ψ , Π f Φ ]
Δ⊣₀Π f Φ Ψ k {c} ψ = ⨜.ι λ p → k (≡.map Ψ p ψ)

Δ⊣₁Π
  : ∀ {A B}(f : A → B)(Φ : 𝔓 A)(Ψ : 𝔓 B)
  → 𝔓[ Ψ , Π f Φ ]
  → 𝔓[ Δ f Ψ , Φ ]
Δ⊣₁Π f Φ Ψ k {c} ψ = ⨜.π (k ψ) ≡.idn

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

module SCtx where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      slen : Nat.t
      sidx : Sym.t slen → 𝒮
    π↓s : SET↓ 𝒮
    π↓s = ∃ (Sym.t slen) ↓ sidx

    sdom : Set
    sdom = SET↓.dom π↓s

    spre : 𝔓 𝒮
    spre = pow π↓s

    infix 1 slen
    infix 2 sidx
    infix 1 spre
    syntax slen Υ = ∣ Υ ∣s
    syntax sidx Υ 𝓈 = Υ [ 𝓈 ]s
    syntax spre Υ τ = [ Υ ]s⁻¹ τ
  open t public
open SCtx hiding (t; ι)

_⧺s_ : ∀ {𝒮 : Set} (Υ Υ′ : SCtx.t 𝒮) → SCtx.t 𝒮
_⧺s_ {𝒮} Υ Υ′ = SCtx.ι (∣ Υ ∣s Nat.+ ∣ Υ′ ∣s) aux
  where
    aux : (i : Sym.t (∣ Υ ∣s Nat.+ ∣ Υ′ ∣s)) → 𝒮
    aux (Sym.ι i) with Fin.split (∣ Υ ∣s) (∣ Υ′ ∣s) i
    aux (Sym.ι .(Fin.inl         i)) | Fin.split-inl i = Υ  [ Sym.ι i ]s
    aux (Sym.ι .(Fin.inr {∣ Υ ∣s} j)) | Fin.split-inr j = Υ′ [ Sym.ι j ]s

_∋⟨_,_⟩s : ∀ {𝒮} (Υ : SCtx.t 𝒮) (x : sdom Υ ) (s : 𝒮) → Set
Υ ∋⟨ x , s ⟩s = Υ [ x ]s ≡.t s

module TCtx where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      tlen : Nat.t
      tidx : Var.t tlen → 𝒮
    π↓t : SET↓ 𝒮
    π↓t = ∃ (Var.t tlen) ↓ tidx

    tdom : Set
    tdom = SET↓.dom π↓t

    tpre : 𝔓 𝒮
    tpre = pow π↓t

    infix 1 tlen
    infix 2 tidx
    infix 1 tpre
    syntax tlen Γ = ∣ Γ ∣t
    syntax tidx Γ x = Γ [ x ]t
    syntax tpre Γ τ = [ Γ ]t⁻¹ τ
  open t public
open TCtx hiding (t; ι)

_⧺t_ : ∀ {𝒮 : Set} (Γ Γ′ : TCtx.t 𝒮) → TCtx.t 𝒮
_⧺t_ {𝒮} Γ Γ′ = TCtx.ι (∣ Γ ∣t Nat.+ ∣ Γ′ ∣t) aux
  where
    aux : (i : Var.t (∣ Γ ∣t Nat.+ ∣ Γ′ ∣t)) → 𝒮
    aux (Var.ι i) with Fin.split (∣ Γ ∣t) (∣ Γ′ ∣t) i
    aux (Var.ι .(Fin.inl          i)) | Fin.split-inl i = Γ  [ Var.ι i ]t
    aux (Var.ι .(Fin.inr {∣ Γ ∣t} j)) | Fin.split-inr j = Γ′ [ Var.ι j ]t

_∋⟨_,_⟩t : ∀ {𝒮} (Γ : TCtx.t 𝒮) (x : tdom Γ ) (s : 𝒮) → Set
Γ ∋⟨ x , s ⟩t = Γ [ x ]t ≡.t s

module 𝒱 where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : SCtx.t 𝒮 ⊗.t TCtx.t 𝒮 ⊗.t 𝒮
    Υ : _
    Υ = let (Υ , _) = π in Υ

    Γ : _
    Γ = let (_ , Γ , _) = π in Γ

    τ : _
    τ = let (_ , _ , τ) = π in τ
  open t public

module 𝒜 where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : TCtx.t (𝒱.t 𝒮) ⊗.t 𝒮
    Γ : _
    Γ = let (Γ , _) = π in Γ

    τ : _
    τ = let (_ , τ) = π in τ

    adom : _
    adom = tdom Γ

    aidx : tdom Γ → _
    aidx x = Γ [ x ]t

    syntax aidx α x = α [ x ]a
  open t public
open 𝒜 using (aidx; adom)

_[_]a→Υ : ∀ {𝒮} (α : 𝒜.t 𝒮) (x : adom α) → _
α [ x ]a→Υ = 𝒱.Υ (α [ x ]a)

_[_]a→Γ : ∀ {𝒮} (α : 𝒜.t 𝒮) (x : adom α) → _
α [ x ]a→Γ = 𝒱.Γ (α [ x ]a)

_[_]a→τ : ∀ {𝒮} (α : 𝒜.t 𝒮) (x : adom α) → _
α [ x ]a→τ = 𝒱.τ (α [ x ]a)

module MCtx where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : TCtx.t (𝒱.t 𝒮)
    mlen : Nat.t
    mlen = tlen π

    mdom : Set
    mdom = Var.t mlen

    midx : mdom → 𝒱.t 𝒮
    midx = tidx π

    infix 1 mlen
    syntax mlen Ω = #m Ω
    syntax midx Ω x = Ω [ x ]m
  open t public
open MCtx hiding (t; ι; π)

_[_]m→Υ : ∀ {𝒮} (Ω : MCtx.t 𝒮) (#x : _) → _
Ω [ #x ]m→Υ = 𝒱.Υ (Ω [ #x ]m)

_[_]m→Γ : ∀ {𝒮} (Ω : MCtx.t 𝒮) (#x : _) → _
Ω [ #x ]m→Γ = 𝒱.Γ (Ω [ #x ]m)

_[_]m→τ : ∀ {𝒮} (Ω : MCtx.t 𝒮) (#x : _) → _
Ω [ #x ]m→τ  = 𝒱.τ (Ω [ #x ]m)

module TRen where
  record t {A} (Γ Γ′ : TCtx.t A) : Set where
    no-eta-equality
    constructor ρ
    field
      map : tdom Γ → tdom Γ′
      coh : ∀ {i} → Γ [ i ]t ≡.t Γ′ [ map i ]t
  open t public

  t↪id
    : {A : Set} {Γ : TCtx.t A}
    → t Γ Γ
  t↪id = ρ (λ x → x) ≡.idn

  t↪cmp
    : {A : Set} {Γ : TCtx.t A} {Γ′ : TCtx.t A}
    → (Η : TCtx.t A)
    → (g : t Γ′ Η)
    → (f : t Γ Γ′)
    → t Γ Η
  t↪cmp H g f = ρ (map g ⇒.∘ map f) (coh g ≡.∘ coh f)

  syntax t↪cmp H g f = g ↪∘[ H ]t f
open TRen using (t↪cmp)

_↪t_ : ∀ {A} (Γ Γ′ : TCtx.t A) → Set
Γ ↪t Γ′ = TRen.t Γ Γ′

module SRen where
  record t {A} (Υ Υ′ : SCtx.t A) : Set where
    no-eta-equality
    constructor ρ
    field
      map : sdom Υ → sdom Υ′
      coh : ∀ {i} → Υ [ i ]s ≡.t Υ′ [ map i ]s
  open t public

  s↪id
    : {A : Set} {Υ : SCtx.t A}
    → t Υ Υ
  s↪id = ρ (λ x → x) ≡.idn

  s↪cmp
    : {A : Set} {Υ : SCtx.t A} {Υ′ : SCtx.t A}
    → (Η : SCtx.t A)
    → (g : t Υ′ Η)
    → (f : t Υ Υ′)
    → t Υ Η
  s↪cmp H g f = ρ (map g ⇒.∘ map f) (coh g ≡.∘ coh f)

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
      𝒪 : 𝔓 (SCtx.t 𝒮 ⊗.t 𝒜.t 𝒮)
      map : ∀ {a Υ Υ′} → Υ ↪s Υ′ → (𝒪 (Υ , a) → 𝒪 (Υ′ , a))
  open t public

module _ (Σ : Sign.t) where
  infixr 1 _⊗↑_
  infix 0 _>_∥_⊢_

  module H where
    record t : Set where
      no-eta-equality
      constructor ι
      field
        π : SCtx.t (Sign.𝒮 Σ) ⊗.t TCtx.t (Sign.𝒮 Σ)
    open t public
  pattern _∥_ Υ Γ = H.ι (Υ , Γ)

  -- yoneda embedding
  module *𝒴 where
    abstract
      t : Set
      t = H.t → 𝔓 H.t

      act : t
      act (Υ ∥ Γ) = λ { (Υ′ ∥ Γ′) → (Υ ↪s Υ′) ⊗.t (Γ ↪t Γ′) }

      ι : (H.t → 𝔓 H.t) → t
      ι x = x

      π : t → (H.t → 𝔓 H.t)
      π x = x

      into : {Υ Υ′ : SCtx.t (Sign.𝒮 Σ)} {Γ Γ′ : TCtx.t (Sign.𝒮 Σ)} → (Υ ↪s Υ′) ⊗.t (Γ ↪t Γ′) → π act (Υ ∥ Γ) (Υ′ ∥ Γ′)
      into x = x

      out : {Υ Υ′ : SCtx.t (Sign.𝒮 Σ)} {Γ Γ′ : TCtx.t (Sign.𝒮 Σ)} → π act (Υ ∥ Γ) (Υ′ ∥ Γ′) → (Υ ↪s Υ′) ⊗.t (Γ ↪t Γ′)
      out x = x

  𝓎 : H.t → 𝔓 H.t
  𝓎 x = *𝒴.π *𝒴.act x

  -- product of presheaves
  module *⊗ where
    abstract
      t : Set
      t = 𝔓 H.t → 𝔓 H.t → 𝔓 H.t

      act : t
      act A B = λ h → A h ⊗.t B h

      ι : (𝔓 H.t → 𝔓 H.t → 𝔓 H.t) → t
      ι x = x

      π : t → (𝔓 H.t → 𝔓 H.t → 𝔓 H.t)
      π x = x

      out : {A B : 𝔓 H.t} {h : H.t} → π act A B h → A h ⊗.t B h
      out x = x

      into : {A B : 𝔓 H.t} {h : H.t} → A h ⊗.t B h → π act A B h
      into x = x

      out₃ : {A B C : 𝔓 H.t} {h : H.t} → π act A (π act B C) h → A h ⊗.t B h ⊗.t C h
      out₃ x = x

      into₃ : {A B C : 𝔓 H.t} {h : H.t} → A h ⊗.t B h ⊗.t C h → π act A (π act B C) h
      into₃ x = x

  _⊗↑_ : 𝔓 H.t → 𝔓 H.t → 𝔓 H.t
  A ⊗↑ B = *⊗.π *⊗.act A B

  -- exponential of presheaves
  module *↗ where
    abstract
      t : Set
      t = 𝔓 H.t → 𝔓 H.t → 𝔓 H.t

      act : t
      act B A = λ h → (𝓎 h ⊗↑ A) ~> B

      ι : (𝔓 H.t → 𝔓 H.t → 𝔓 H.t) → t
      ι x = x

      π : t → (𝔓 H.t → 𝔓 H.t → 𝔓 H.t)
      π x = x

      out : {A B : 𝔓 H.t} {h : H.t} → π act B A h → (𝓎 h ⊗↑ A) ~> B
      out x = x

  _↗_ : 𝔓 H.t → 𝔓 H.t → 𝔓 H.t
  (B ↗ A) = *↗.π *↗.act B A

  -- symbols presheaf
  module *S where
    abstract
      t : Set
      t = Sign.𝒮 Σ → 𝔓 H.t

      act : t
      act τ = λ { (Υ ∥ Γ) → [ Υ ]s⁻¹ τ }

      ι : (Sign.𝒮 Σ → 𝔓 H.t) → t
      ι x = x

      π : t → (Sign.𝒮 Σ → 𝔓 H.t)
      π x = x

      into : {τ : Sign.𝒮 Σ} {Υ : SCtx.t (Sign.𝒮 Σ)} {Γ : TCtx.t (Sign.𝒮 Σ)} → [ Υ ]s⁻¹ τ → π act τ (Υ ∥ Γ)
      into x = x

      out : {τ : Sign.𝒮 Σ} {Υ : SCtx.t (Sign.𝒮 Σ)} {Γ : TCtx.t (Sign.𝒮 Σ)} → π act τ (Υ ∥ Γ) → [ Υ ]s⁻¹ τ
      out x = x

  S : (τ : Sign.𝒮 Σ) → 𝔓 H.t
  S τ = *S.π *S.act τ

  -- variables presheaf
  module *V where
    abstract
      t : Set
      t = Sign.𝒮 Σ → 𝔓 H.t

      act : t
      act τ = λ { (Υ ∥ Γ) → [ Γ ]t⁻¹ τ }

      ι : (Sign.𝒮 Σ → 𝔓 H.t) → t
      ι x = x

      π : t → (Sign.𝒮 Σ → 𝔓 H.t)
      π x = x

      into : {τ : Sign.𝒮 Σ} {Υ : SCtx.t (Sign.𝒮 Σ)} {Γ : TCtx.t (Sign.𝒮 Σ)} → [ Γ ]t⁻¹ τ → π act τ (Υ ∥ Γ)
      into x = x

  V : (τ : Sign.𝒮 Σ) → 𝔓 H.t
  V τ = *V.π *V.act τ

  module *↗[]t where
    abstract
      t : Set
      t = (X : (τ : Sign.𝒮 Σ) → 𝔓 H.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → 𝔓 H.t

      act : t
      act X Γ = λ h → ⨜.[ tdom Γ ∋ x ] (X (Γ [ x ]t)) h

      ι : ((X : (τ : Sign.𝒮 Σ) → 𝔓 H.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → 𝔓 H.t) → t
      ι x = x

      π : t → ((X : (τ : Sign.𝒮 Σ) → 𝔓 H.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → 𝔓 H.t)
      π x = x

      into : {X : Sign.𝒮 Σ → 𝔓 H.t} {Γ : TCtx.t (Sign.𝒮 Σ)} {h : H.t} → ⨜.[ tdom Γ ∋ x ] (X (Γ [ x ]t)) h → π act X Γ h
      into x = x

      out : {X : Sign.𝒮 Σ → 𝔓 H.t} {Γ : TCtx.t (Sign.𝒮 Σ)} {h : H.t} → π act X Γ h →  ⨜.[ tdom Γ ∋ x ] (X (Γ [ x ]t)) h
      out x = x

      concat : ∀ {Γ Γ′ X} → (π act X Γ ⊗↑ π act X Γ′) ~> π act X (Γ ⧺t Γ′)
      concat {Γ = Γ} {Γ′ = Γ′} [Γ]⊗[Γ′] with *⊗.out [Γ]⊗[Γ′]
      concat {Γ = Γ} {Γ′ = Γ′} {X = X} {h} [Γ]⊗[Γ′] | [Γ] , [Γ′] = ⨜.ι (λ {i} → aux i)
        where
          aux : (x : Var.t ∣ Γ ⧺t Γ′ ∣t) → X ((Γ ⧺t Γ′) [ x ]t) h
          aux (Var.ι i) with Fin.split (∣ Γ ∣t) (∣ Γ′ ∣t) i
          aux (Var.ι .(Fin.inl i)) | Fin.split-inl i = ⨜.π [Γ]
          aux (Var.ι .(Fin.inr {m = ∣ Γ ∣t} j)) | Fin.split-inr j = ⨜.π [Γ′]

  _↗[_]t : (X : (τ : Sign.𝒮 Σ) → 𝔓 H.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → 𝔓 H.t
  X ↗[ Γ ]t = *↗[]t.π *↗[]t.act X Γ


  module *↗[]s where
    abstract
      t : Set
      t = (X : (τ : Sign.𝒮 Σ) → 𝔓 H.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → 𝔓 H.t

      act : t
      act X Υ = λ h → ⨜.[ sdom Υ ∋ x ] (X (Υ [ x ]s)) h

      ι : ((X : (τ : Sign.𝒮 Σ) → 𝔓 H.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → 𝔓 H.t) → t
      ι x = x

      π : t → ((X : (τ : Sign.𝒮 Σ) → 𝔓 H.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → 𝔓 H.t)
      π x = x

      into : {X : Sign.𝒮 Σ → 𝔓 H.t} {Υ : SCtx.t (Sign.𝒮 Σ)} {h : H.t} → ⨜.[ sdom Υ ∋ x ] (X (Υ [ x ]s)) h → π act X Υ h
      into x = x

      out : {X : Sign.𝒮 Σ → 𝔓 H.t} {Υ : SCtx.t (Sign.𝒮 Σ)} {h : H.t} → π act X Υ h → ⨜.[ sdom Υ ∋ x ] (X (Υ [ x ]s)) h
      out x = x

      concat : ∀ {Υ Υ′ X} → (π act X Υ ⊗↑ π act X Υ′) ~> π act X (Υ ⧺s Υ′)
      concat {Υ = Υ} {Υ′ = Υ′} [Υ]⊗[Υ′] with *⊗.out [Υ]⊗[Υ′]
      concat {Υ = Υ} {Υ′ = Υ′} {X = X} {h} [Υ]⊗[Υ′] | [Υ] , [Υ′] = ⨜.ι (λ {i} → aux i)
        where
          aux : (x : Sym.t ∣ Υ ⧺s Υ′ ∣s) → X ((Υ ⧺s Υ′) [ x ]s) h
          aux (Sym.ι i) with Fin.split (∣ Υ ∣s) (∣ Υ′ ∣s) i
          aux (Sym.ι .(Fin.inl i)) | Fin.split-inl i = ⨜.π [Υ]
          aux (Sym.ι .(Fin.inr {m = ∣ Υ ∣s} j)) | Fin.split-inr j = ⨜.π [Υ′]

  _↗[_]s : (X : (τ : Sign.𝒮 Σ) → 𝔓 H.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → 𝔓 H.t
  X ↗[ Υ ]s = *↗[]s.π *↗[]s.act X Υ

  module *⊚ where
    abstract
      t : Set
      t = (A : 𝔓 H.t) (P : (τ : Sign.𝒮 Σ) → 𝔓 H.t) → 𝔓 H.t

      act : t
      act A P = λ h →
        ⨛.[ H.t ∋ h′ ] let Υ′ ∥ Γ′ = h′ in
          A (Υ′ ∥ Γ′)
            ⊗.t (S ↗[ Υ′ ]s) h
            ⊗.t (P ↗[ Γ′ ]t) h

      ι : ((A : 𝔓 H.t) (P : (τ : Sign.𝒮 Σ) → 𝔓 H.t) → 𝔓 H.t) → t
      ι x = x

      π : t → ((A : 𝔓 H.t) (P : (τ : Sign.𝒮 Σ) → 𝔓 H.t) → 𝔓 H.t)
      π x = x

      into : {A : 𝔓 H.t} {P : Sign.𝒮 Σ → 𝔓 H.t} {h : H.t} → (⨛.[ H.t ∋ h′ ] let Υ′ ∥ Γ′ = h′ in A (Υ′ ∥ Γ′) ⊗.t (S ↗[ Υ′ ]s) h ⊗.t (P ↗[ Γ′ ]t) h) → π act A P h
      into x = x

  _⊚_ : (A : 𝔓 H.t) (P : (τ : Sign.𝒮 Σ) → 𝔓 H.t) → 𝔓 H.t
  (A ⊚ P) = *⊚.π *⊚.act A P

  module *⊙ where
    abstract
      t : Set
      t = (P Q : (τ : Sign.𝒮 Σ) → 𝔓 H.t) → ((τ : Sign.𝒮 Σ) → 𝔓 H.t)

      act : t
      act P Q τ = P τ ⊚ Q

      ι : ((P Q : (τ : Sign.𝒮 Σ) → 𝔓 H.t) → ((τ : Sign.𝒮 Σ) → 𝔓 H.t)) → t
      ι x = x

      π : t → ((P Q : (τ : Sign.𝒮 Σ) → 𝔓 H.t) → ((τ : Sign.𝒮 Σ) → 𝔓 H.t))
      π x = x

      into : {P Q : Sign.𝒮 Σ → 𝔓 H.t} {τ : Sign.𝒮 Σ} {h : H.t} → (P τ ⊚ Q) h → π act P Q τ h
      into x = x

  -- substitution tensor
  _⊙_ : (P Q : (τ : Sign.𝒮 Σ) → 𝔓 H.t) → ((τ : Sign.𝒮 Σ) → 𝔓 H.t)
  P ⊙ Q = *⊙.π *⊙.act P Q

  data _>_∥_⊢_
    (Ω : MCtx.t (Sign.𝒮 Σ))
    (Υ : SCtx.t (Sign.𝒮 Σ))
    (Γ : TCtx.t (Sign.𝒮 Σ))
      : (τ : Sign.𝒮 Σ) → Set where
    tvar
      : (x : tdom Γ)
      → Ω > Υ ∥ Γ ⊢ Γ [ x ]t
    mvar
      : (#m : mdom Ω)
      → (∀ 𝓈 → [ Υ ]s⁻¹ Ω [ #m ]m→Υ [ 𝓈 ]s)
      → (∀ x → Ω > Υ ∥ Γ ⊢ Ω [ #m ]m→Γ [ x ]t)
      → Ω > Υ ∥ Γ ⊢ Ω [ #m ]m→τ
    app
      : ∀ {α}
      → (ϑ : Sign.𝒪 Σ (Υ , α))
      → (∀ x → Ω > (Υ ⧺s α [ x ]a→Υ) ∥ (Γ ⧺t α [ x ]a→Γ) ⊢ α [ x ]a→τ)
      → Ω > Υ ∥ Γ ⊢ 𝒜.τ α

  module Model
    (P : Sign.𝒮 Σ → 𝔓 H.t)
    (ν : {τ : Sign.𝒮 Σ} → V τ ~> P τ)
    (ς : {τ : Sign.𝒮 Σ} → (P ⊙ P) τ ~> P τ)
    where

    -- useful when you want to know what something's type "really" is, regardless of 'abstract'.
    -- To learn the type of X, open a hole and put {{type-of X}} and type C-u C-c C-n.
    type-of : {A : Set} → A → Set
    type-of {A} _ = A


    -- Fiore & Hur / Second-Order Equational Logics decompose substitution into two auxiliary maps which they don't explicitly define.
    ς⟨_,_⟩ : {τ : Sign.𝒮 Σ} (Υ : SCtx.t (Sign.𝒮 Σ)) (Γ : TCtx.t (Sign.𝒮 Σ)) → ((P τ ↗ 𝓎 (Υ ∥ Γ)) ⊗↑ S ↗[ Υ ]s ⊗↑ P ↗[ Γ ]t) ~> P τ
    ς⟨ _ , _ ⟩ = ς ⇒.∘Π *⊙.into ⇒.∘Π aux₂ ⇒.∘Π aux₁
      where
        aux₁
          : {ps : SCtx.t (Sign.𝒮 Σ)} {qs : TCtx.t (Sign.𝒮 Σ)} {h : H.t} {τ : Sign.𝒮 Σ} (let Υ ∥ Γ = h)
          → ((P τ ↗ 𝓎 (ps ∥ qs)) ⊗↑ S ↗[ ps ]s ⊗↑ P ↗[ qs ]t) h
          → P τ ((Υ ⧺s ps) ∥ (Γ ⧺t qs)) ⊗.t (S ↗[ Υ ]s) h ⊗.t (S ↗[ ps ]s) h ⊗.t (P ↗[ Γ ]t) h ⊗.t (P ↗[ qs ]t) h
        aux₁ 𝔪⊗[ps]⊗[qs] with *⊗.out₃ 𝔪⊗[ps]⊗[qs]
        aux₁ {h = Υ ∥ Γ} 𝔪⊗[ps]⊗[qs] | 𝔪 , [ps] , [qs] =
          ( *↗.out 𝔪
              (*⊗.into
                ( *𝒴.into ({!!} , {!!})
                , *𝒴.into {!!}
                )
              )
          , *↗[]s.into (⨜.ι (*S.into (_ ∐., ≡.idn)))
          , *↗[]s.into (⨜.ι (⨜.π (*↗[]s.out [ps])))
          , *↗[]t.into (⨜.ι (ν (*V.into (_ ∐., ≡.idn))))
          , *↗[]t.into (⨜.ι (⨜.π (*↗[]t.out [qs])))
          )

        aux₂
          : {ps : SCtx.t (Sign.𝒮 Σ)} {qs : TCtx.t (Sign.𝒮 Σ)} {h : H.t} {τ : Sign.𝒮 Σ} (let Υ ∥ Γ = h)
          → P τ ((Υ ⧺s ps) ∥ (Γ ⧺t qs)) ⊗.t (S ↗[ Υ ]s) h ⊗.t (S ↗[ ps ]s) h ⊗.t (P ↗[ Γ ]t) h ⊗.t (P ↗[ qs ]t) h
          → (P τ ⊚ P) h
        aux₂ (M , [Υ] , [ps] , [Γ] , [qs]) =
          *⊚.into
            ( ⨛.into (_ ∥ _)
                ( M
                , *↗[]s.concat (*⊗.into ([Υ] , [ps]))
                , *↗[]t.concat (*⊗.into ([Γ] , [qs]))
                )
            )

\end{code}
