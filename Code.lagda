\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where

infix 2 _[_]a→Γ
infix 2 _[_]a→Υ
infix 2 _[_]a→τ
infix 2 _[_]m→Γ
infix 2 _[_]m→Υ
infix 2 _[_]m→τ
infixr 1 _⧺s_
infixr 1 _⧺t_

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

-- dependent coproduct
module ∐ where
  record t (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      π₀ : A
      π₁ : B π₀

  infix 0 t
  syntax t A (λ x → B) = [ A ∋ x ] B
  open t public

-- dependent product
module ∏ where
  record t (I : Set) (P : I → Set) : Set where
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
  record t {I : Set} (P : I → Set) : Set where
    no-eta-equality
    constructor ι
    field
      {idx} : I
      π : P idx
  open t public

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P

  ι[_] : {I : Set} {P : I → Set} (i : I) → P i → t P
  ι[_] = λ {I} {P} i → ι

-- end
module ⨜ where
  record t {I : Set} (P : I → Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : ∀ {i} → P i
  open t public

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P

  π[_] : {I : Set} (i : I) {P : I → Set} → t P → P i
  π[ i ] = λ z → π z

module ℘ where
  infix 2 _∈_
  infixr 2 _⊆_

  T : (X : Set) → Set
  T X = X → Set

  _∈_ : ∀ {X} (x : X) (φ : T X) → Set
  x ∈ φ = φ x -- cps/yoneda

  Sub : ∀ {X} (Ψ Φ : T X) → Set
  Sub Ψ Φ = ∀ {x} → x ∈ Ψ → x ∈ Φ

  syntax Sub {X} Ψ Φ = Ψ ⊆[ X ] Φ

  _⊆_ : ∀ {X} (Ψ Φ : T X) → Set
  _⊆_ = Sub

  Lan
    : {X Y 𝔙 : Set}
    → (Y[_,_] : Y → Y → Set) (_⟦⊗⟧_ : 𝔙 → Set → Set)
    → (𝔲 : X → Y) (Ψ : X → 𝔙)
    → T Y
  Lan Y[_,_] _⟦⊗⟧_ Ψ 𝔲 y = ⨛.[ _ ∋ x ] 𝔲 x ⟦⊗⟧ Y[ Ψ x , y ]

  Ran
    : {X Y 𝔙 : Set}
    → (Y[_,_] : Y → Y → Set) (_⟦⋔⟧_ : Set → 𝔙 → Set)
    → (𝔲 : X → Y) (Ψ : X → 𝔙)
    → T Y
  Ran Y[_,_] _⟦⋔⟧_ 𝔲 Ψ y = ⨜.[ _ ∋ x ] Y[ y , 𝔲 x ] ⟦⋔⟧ Ψ x

  module Σ where
    record t {Γ Θ} (𝔲 : Θ → Γ) (Ψ : T Θ) (x : Γ) : Set where
      no-eta-equality
      constructor ι
      field
        π : Lan ≡._t_ ⊗._t_ 𝔲 Ψ x
    open t public

  module Δ where
    record t {Γ Θ} (𝔲 : Γ → Θ) (Ψ : T Θ) (x : Γ) : Set where
      no-eta-equality
      constructor ι
      field
        π : Ψ (𝔲 x)
    open t public

  module Π where
    record t {Γ Θ} (𝔲 : Θ → Γ) (Ψ : T Θ) (x : Γ) : Set where
      no-eta-equality
      constructor ι
      field
        π : Ran ≡._t_ ⇒._t_ 𝔲 Ψ x
    open t public

  module _ {Γ Θ} (f : Θ → Γ) (Φ : T Θ) (Ψ : T Γ) where
    Σ⊣Δ : Σ.t f Φ ⊆ Ψ → Φ ⊆ Δ.t f Ψ
    Σ⊣Δ k ϕ = Δ.ι (k (Σ.ι (⨛.ι (ϕ , ≡.idn))))

    Δ⊢Σ : Φ ⊆ Δ.t f Ψ → Σ.t f Φ ⊆ Ψ
    Δ⊢Σ k (Σ.ι (⨛.ι (ϕ , p))) = ≡.map Ψ p (Δ.π (k ϕ))

    Δ⊣Π : Δ.t f Ψ ⊆ Φ → Ψ ⊆ Π.t f Φ
    Δ⊣Π k ψ = Π.ι (⨜.ι λ p → k (Δ.ι (≡.map Ψ p ψ)))

    Π⊢Δ : Ψ ⊆ Π.t f Φ → Δ.t f Ψ ⊆ Φ
    Π⊢Δ k ψ = ⨜.π (Π.π (k (Δ.π ψ))) ≡.idn
open ℘ using (_∈_; _⊆_)

record SET↓ (I : Set) : Set where
  no-eta-equality
  constructor ∃_↓_
  field
    dom : Set
    map : dom → I

[_]⁻¹ : ∀ {E I} → (E → I) → ℘.T I
[ p ]⁻¹ i = ∐.[ _ ∋ e ] (i ≡.t p e)

tot : ∀ {I} → ℘.T I → Set
tot = ∐.t _

fib : ∀ {I} (ϕ : ℘.T I) → (tot ϕ → I)
fib ϕ = ∐.π₀

fam : ∀ {I} → ℘.T I → SET↓ I
fam ϕ = ∃ tot ϕ ↓ fib ϕ

pow : ∀ {I} → SET↓ I → ℘.T I
pow (∃ dom ↓ map) = [ map ]⁻¹

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

module Vec where
  data t (A : Set) : Nat.t → Set where
    [] : t A Nat.ze
    _∷_ : {n : Nat.t} → A → t A n → t A (Nat.su n)

  _⧺_ : {A : Set} {m n : Nat.t} → t A m → t A n → t A (m Nat.+ n)
  [] ⧺ ys = ys
  (x ∷ xs) ⧺ ys = x ∷ (xs ⧺ ys)

  map
    : {A B : Set} {n : Nat.t} (f : A → B)
    → t A n
    → t B n
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  π : {A : Set} {n : Nat.t} → Fin.t n → t A n → A
  π Fin.ze (x ∷ _) = x
  π (Fin.su i) (_ ∷ xs) = π i xs

  concat-coh-l
    : {A : Set} {m n : Nat.t} (i : Fin.t m) (xs : t A m) (ys : t A n)
    → π i xs ≡.t π (Fin.inl i) (xs ⧺ ys)
  concat-coh-l () [] ys
  concat-coh-l Fin.ze (x ∷ xs) ys = ≡.idn
  concat-coh-l (Fin.su i) (x ∷ xs) ys = concat-coh-l i xs ys

  concat-coh-r
    : {A : Set} {m n : Nat.t} (i : Fin.t n) (xs : t A m) (ys : t A n)
    → π i ys ≡.t π (Fin.inr {m = m} i) (xs ⧺ ys)
  concat-coh-r i [] ys = ≡.idn
  concat-coh-r i (x ∷ xs) ys = concat-coh-r i xs ys

  tabulate
    : {A : Set} {n : Nat.t}
    → (Fin.t n → A)
    → t A n
  tabulate {n = Nat.ze} φ = []
  tabulate {n = Nat.su n} φ = φ Fin.ze ∷ tabulate (φ ⇒.∘ Fin.su)


module □ where
  data t {A : Set} (P : ℘.T A) : {n : Nat.t} → Vec.t A n → Set where
    [] : t P Vec.[]
    _∷_ : {n : Nat.t} {x : A} {xs : Vec.t A n} → x ∈ P → t P xs → t P (x Vec.∷ xs)

  _⧺_
    : {A : Set} {P : ℘.T A} {m n : Nat.t} {xs : Vec.t A m} {ys : Vec.t A n}
    → t P xs
    → t P ys
    → t P (xs Vec.⧺ ys)
  [] ⧺ ys = ys
  (x ∷ xs) ⧺ ys = x ∷ (xs ⧺ ys)

  π : {A : Set} {P : ℘.T A} {n : Nat.t} {xs : Vec.t A n} (i : Fin.t n) → t P xs → P (Vec.π i xs)
  π Fin.ze (x ∷ _) = x
  π (Fin.su i) (_ ∷ xs) = π i xs

  map
    : {A : Set} {P Q : ℘.T A} {n : Nat.t} {xs : Vec.t A n}
    → (P ⊆ Q)
    → t P xs
    → t Q xs
  map η [] = []
  map η (x ∷ xs) = η x ∷ map η xs

  tabulate
    : {A : Set} {P : ℘.T A} {n : Nat.t} {xs : Vec.t A n}
    → ((i : Fin.t n) → P (Vec.π i xs))
    → t P xs
  tabulate {xs = Vec.[]} φ = []
  tabulate {xs = x Vec.∷ xs} φ = φ Fin.ze ∷ tabulate (φ ⇒.∘Π Fin.su)

module Var where
  record t (n : Nat.t) : Set where
    no-eta-equality
    constructor ι
    field
      π : Fin.t n

  open t public

  su : {n : Nat.t} → t n → t (Nat.su n)
  su = ι ⇒.∘ Fin.su ⇒.∘ π

module Sym where
  record t (n : Nat.t) : Set where
    no-eta-equality
    constructor ι
    field
      π : Fin.t n
  open t public

  su : {n : Nat.t} → t n → t (Nat.su n)
  su = ι ⇒.∘ Fin.su ⇒.∘ π

module SCtx where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      {slen} : Nat.t
      sctx : Vec.t 𝒮 slen

    sidx : Sym.t slen → 𝒮
    sidx s = Vec.π (Sym.π s) sctx

    π↓s : SET↓ 𝒮
    π↓s = ∃ (Sym.t slen) ↓ sidx

    sdom : Set
    sdom = SET↓.dom π↓s

    spre : ℘.T 𝒮
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
Υ ⧺s Υ′ = SCtx.ι (sctx Υ Vec.⧺ sctx Υ′)

_∋⟨_,_⟩s : ∀ {𝒮} (Υ : SCtx.t 𝒮) (x : sdom Υ ) (s : 𝒮) → Set
Υ ∋⟨ x , s ⟩s = Υ [ x ]s ≡.t s

module TCtx where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      {tlen} : Nat.t
      tctx : Vec.t 𝒮 tlen

    tidx : Var.t tlen → 𝒮
    tidx x = Vec.π (Var.π x) tctx

    π↓t : SET↓ 𝒮
    π↓t = ∃ (Var.t tlen) ↓ tidx

    tdom : Set
    tdom = SET↓.dom π↓t

    tpre : ℘.T 𝒮
    tpre = pow π↓t

    infix 1 tlen
    infix 2 tidx
    infix 1 tpre
    syntax tlen Γ = ∣ Γ ∣t
    syntax tidx Γ x = Γ [ x ]t
    syntax tpre Γ τ = [ Γ ]t⁻¹ τ
  open t public

open TCtx hiding (t; ι)

-- type context concatenation
_⧺t_ : ∀ {𝒮 : Set} (Γ Γ′ : TCtx.t 𝒮) → TCtx.t 𝒮
Γ ⧺t Γ′ = TCtx.ι (tctx Γ Vec.⧺ tctx Γ′)

_∋⟨_,_⟩t : ∀ {𝒮} (Γ : TCtx.t 𝒮) (x : tdom Γ ) (s : 𝒮) → Set
Γ ∋⟨ x , s ⟩t = Γ [ x ]t ≡.t s

-- valences
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

-- arities
module 𝒜 where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : TCtx.t (𝒱.t 𝒮) ⊗.t 𝒮

    Ω : _
    Ω = let (Ω , _) = π in Ω

    τ : _
    τ = let (_ , τ) = π in τ

    adom : _
    adom = tdom Ω

    aidx : tdom Ω → _
    aidx x = Ω [ x ]t

    syntax aidx α x = α [ x ]a
  open t public
open 𝒜 using (aidx; adom)

_[_]a→Υ : ∀ {𝒮} (α : 𝒜.t 𝒮) (x : adom α) → SCtx.t 𝒮
α [ x ]a→Υ = 𝒱.Υ (α [ x ]a)

_[_]a→Γ : ∀ {𝒮} (α : 𝒜.t 𝒮) (x : adom α) → TCtx.t 𝒮
α [ x ]a→Γ = 𝒱.Γ (α [ x ]a)

_[_]a→τ : ∀ {𝒮} (α : 𝒜.t 𝒮) (x : adom α) → 𝒮
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
    → {Η : TCtx.t A}
    → (g : t Γ′ Η)
    → (f : t Γ Γ′)
    → t Γ Η
  t↪cmp g f = ρ (map g ⇒.∘ map f) (coh g ≡.∘ coh f)

  syntax t↪cmp {H = H} g f = g ↪∘[ H ]t f

  module weakening where
    inl
      : {A : Set} {Γ : TCtx.t A} (Γ′ : TCtx.t A)
      → t Γ (Γ ⧺t Γ′)
    inl {Γ = TCtx.ι Γ} (TCtx.ι Γ′) =
      ρ (Var.ι ⇒.∘ Fin.inl ⇒.∘ Var.π)
        (Vec.concat-coh-l _ Γ Γ′)

    inr
      : {A : Set} (Γ : TCtx.t A) {Γ′ : TCtx.t A}
      → t Γ′ (Γ ⧺t Γ′)
    inr (TCtx.ι {m} Γ) {TCtx.ι Γ′} =
      ρ (Var.ι ⇒.∘ Fin.inr {m = m} ⇒.∘ Var.π)
        (Vec.concat-coh-r _ Γ Γ′)

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
    : {A : Set} {Υ Υ′ : SCtx.t A}
    → {Η : SCtx.t A}
    → (g : t Υ′ Η)
    → (f : t Υ Υ′)
    → t Υ Η
  s↪cmp g f = ρ (map g ⇒.∘ map f) (coh g ≡.∘ coh f)
  syntax s↪cmp {H = H} g f = g ↪∘[ H ]s f

  module weakening where
    inl
      : {A : Set} {Υ : SCtx.t A} (Υ′ : SCtx.t A)
      → t Υ (Υ ⧺s Υ′)
    inl {Υ = SCtx.ι Υ} (SCtx.ι Υ′) =
      ρ (Sym.ι ⇒.∘ Fin.inl ⇒.∘ Sym.π)
        (Vec.concat-coh-l _ Υ Υ′)

    inr
      : {A : Set} (Υ : SCtx.t A) {Υ′ : SCtx.t A}
      → t Υ′ (Υ ⧺s Υ′)
    inr (SCtx.ι {m} Υ) {SCtx.ι Υ′} =
      ρ (Sym.ι ⇒.∘ Fin.inr {m = m} ⇒.∘ Sym.π)
        (Vec.concat-coh-r _ Υ Υ′)

open SRen using (s↪cmp)

_↪s_ : ∀ {A} (Υ Υ′ : SCtx.t A) → Set
Υ ↪s Υ′ = SRen.t Υ Υ′

module Sign where
  record t : Set₁ where
    no-eta-equality
    constructor ι
    field
      𝒮 : Set
      𝒪 : ℘.T (SCtx.t 𝒮 ⊗.t 𝒜.t 𝒮)
      map : ∀ {Υ Υ′} → Υ ↪s Υ′ → (𝒪 ⇒.∘ (Υ ,_)) ⊆ (𝒪 ⇒.∘ (Υ′ ,_))
  open t public

module _ (Σ : Sign.t) where
  infix 0 _∥_
  infix 0 _>_∥_⊢_

  module H where
    record t : Set where
      no-eta-equality
      constructor ι
      field
        π : SCtx.t (Sign.𝒮 Σ) ⊗.t TCtx.t (Sign.𝒮 Σ)
      Υ : _
      Υ = let (Υ , _) = π in Υ
      Γ : _
      Γ = let (_ , Γ) = π in Γ
    open t public
  pattern _∥_ Υ Γ = H.ι (Υ , Γ)

  -- yoneda embedding
  module 𝓎 where
    record t (b a : H.t) : Set where
      no-eta-equality
      constructor ι
      field
        π :
          let (Υ  ∥ Γ ) = b in
          let (Υ′ ∥ Γ′) = a in
          (Υ ↪s Υ′) ⊗.t (Γ ↪t Γ′)

  module ⊗↑ where
    infixr 1 _t_
    record _t_ (A B : ℘.T H.t) (h : H.t) : Set where
      no-eta-equality
      constructor ι
      field
        π : h ∈ A ⊗.t h ∈ B

  module ↗ where
    record _t_ (B A : ℘.T H.t) (h : H.t) : Set where
      no-eta-equality
      constructor ι
      field
        π : (𝓎.t h ⊗↑.t A) ⊆ B
    open _t_ public

  module ↗m where
    record _[_]
      (X : (τ : Sign.𝒮 Σ) → ℘.T H.t)
      (Ω : MCtx.t (Sign.𝒮 Σ))
      (h : H.t)
        : Set where
      no-eta-equality
      constructor ι
      field
        π :
          □.t
            (λ 𝓋 → h ∈ (X (𝒱.τ 𝓋) ↗.t 𝓎.t (𝒱.Υ 𝓋 ∥ 𝒱.Γ 𝓋)))
            (tctx (MCtx.π Ω))

    infix 3 _[_]
    open _[_] public

    lookup
      : {X : Sign.𝒮 Σ → ℘.T H.t}
      → {Ω : MCtx.t (Sign.𝒮 Σ)}
      → (𝔪 : mdom Ω) (let 𝒱.ι (psₘ , qsₘ , τₘ) = midx Ω 𝔪)
      → X [ Ω ] ⊆ (X τₘ ↗.t 𝓎.t (psₘ ∥ qsₘ))
    lookup 𝔪 (ι □Ω) = □.π (Var.π 𝔪) □Ω

  module ↗s where
    infix 3 _[_]
    record _[_]
      (X : (τ : Sign.𝒮 Σ) → ℘.T H.t)
      (Υ : SCtx.t (Sign.𝒮 Σ))
      (h : H.t)
        : Set where
      no-eta-equality
      constructor ι
      field
        π : □.t (λ x → h ∈ X x) (sctx Υ)

    open _[_] public

    ⧺
      : ∀ {Υ Υ′ X}
      → (X [ Υ ] ⊗↑.t X [ Υ′ ]) ⊆ X [ Υ ⧺s Υ′ ]
    ⧺ (⊗↑.ι (ι X↗Υ , ι X↗Υ′)) = ι (X↗Υ □.⧺ X↗Υ′)

    lookup
      : {X : Sign.𝒮 Σ → ℘.T H.t} {Υ : SCtx.t (Sign.𝒮 Σ)} (s : Sym.t ∣ Υ ∣s)
      → X [ Υ ] ℘.⊆ X (sidx Υ s)
    lookup x (ι □Υ) = □.π (Sym.π x) □Υ

  module ↗t where
    record _[_]
      (X : (τ : Sign.𝒮 Σ) → ℘.T H.t)
      (Γ : TCtx.t (Sign.𝒮 Σ))
      (h : H.t)
        : Set where
      no-eta-equality
      constructor ι
      field
        π : □.t (λ x → h ∈ X x) (tctx Γ)
    open _[_] public

    ⧺
      : ∀ {Γ Γ′ X}
      → (X [ Γ ] ⊗↑.t X [ Γ′ ]) ⊆ X [ Γ ⧺t Γ′ ]
    ⧺ (⊗↑.ι (ι X↗Γ , ι X↗Γ′)) = ι (X↗Γ □.⧺ X↗Γ′)

    lookup
      : {X : Sign.𝒮 Σ → ℘.T H.t} {Γ : TCtx.t (Sign.𝒮 Σ)} (x : Var.t ∣ Γ ∣t)
      → X [ Γ ] ℘.⊆ X (tidx Γ x)
    lookup x (ι □Γ) = □.π (Var.π x) □Γ

  module S where
    record t (τ : Sign.𝒮 Σ) (h : H.t) : Set where
      no-eta-equality
      constructor ι
      field
        π : [ H.Υ h ]s⁻¹ τ
    open t public

  module V where
    record t (τ : Sign.𝒮 Σ) (h : H.t) : Set where
      no-eta-equality
      constructor ι
      field
        π : [ H.Γ h ]t⁻¹ τ
    open t public

  module ⊚ where
    record _t_
      (A : ℘.T H.t)
      (P : (τ : Sign.𝒮 Σ) → ℘.T H.t)
      (h : H.t)
        : Set where
      no-eta-equality
      constructor ι
      field
        π :
          ⨛.[ H.t ∋ h′ ] let Υ′ ∥ Γ′ = h′ in
            A (Υ′ ∥ Γ′)
              ⊗.t (h ∈ S.t ↗s.[ Υ′ ])
              ⊗.t (h ∈ P ↗t.[ Γ′ ])

  module ⊙ where
    record _t_
      (P Q : (τ : Sign.𝒮 Σ) → ℘.T H.t)
      (τ : Sign.𝒮 Σ)
      (h : H.t)
        : Set where
      no-eta-equality
      constructor ι
      field
        π : h ∈ (P τ ⊚.t Q)

  module 𝔉 where
    𝒪[_] : 𝒜.t (Sign.𝒮 Σ) → ℘.T H.t
    𝒪[ 𝒶 ] (Υ ∥ _) = Sign.𝒪 Σ (Υ , 𝒶)

    t : (X : Sign.𝒮 Σ → ℘.T H.t) → Sign.𝒮 Σ → ℘.T H.t
    t X τ h =
      ∐.[ 𝒜.t (Sign.𝒮 Σ) ∋ 𝒶 ] (𝒜.τ 𝒶 ≡.t τ) ⊗.t
        (∐.[ (h ∈ 𝒪[ 𝒶 ]) ∋ ϑ ]
           □.t
             (λ 𝓋 → h ∈ (X (𝒱.τ 𝓋) ↗.t 𝓎.t (𝒱.Υ 𝓋 ∥ 𝒱.Γ 𝓋)))
             (tctx (𝒜.Ω 𝒶))
        )

  data _>_∥_⊢_
    (Ω : MCtx.t (Sign.𝒮 Σ))
    (Υ : SCtx.t (Sign.𝒮 Σ))
    (Γ : TCtx.t (Sign.𝒮 Σ))
      : (τ : Sign.𝒮 Σ) → Set where
    tvar
      : (x : tdom Γ)
      → Ω > Υ ∥ Γ ⊢ Γ [ x ]t
    mvar
      : (𝔪 : mdom Ω)
      → □.t (spre Υ) (sctx (Ω [ 𝔪 ]m→Υ))
      → □.t (Ω > Υ ∥ Γ ⊢_) (tctx (Ω [ 𝔪 ]m→Γ))
      → Ω > Υ ∥ Γ ⊢ Ω [ 𝔪 ]m→τ
    app
      : ∀ {α}
      → (ϑ : Sign.𝒪 Σ (Υ , α))
      → □.t (λ 𝓋 → Ω > Υ ⧺s 𝒱.Υ 𝓋  ∥ Γ ⧺t 𝒱.Γ 𝓋 ⊢ 𝒱.τ 𝓋) (tctx (𝒜.Ω α))
      → Ω > Υ ∥ Γ ⊢ 𝒜.τ α

  module Model
    (P : Sign.𝒮 Σ → ℘.T H.t)
    (ν : {τ : Sign.𝒮 Σ} → V.t τ ⊆ P τ)
    (ς : {τ : Sign.𝒮 Σ} → (P ⊙.t P) τ ⊆ P τ)
    (α : {τ : Sign.𝒮 Σ} → 𝔉.t P τ ⊆ P τ)
    where

    -- Fiore & Hur / Second-Order Equational Logics decompose substitution into two auxiliary maps which they don't explicitly define.
    ς⟨_,_⟩
      : {τ : Sign.𝒮 Σ}
      → (Υ : SCtx.t (Sign.𝒮 Σ))
      → (Γ : TCtx.t (Sign.𝒮 Σ))
      → ((P τ ↗.t 𝓎.t (Υ ∥ Γ)) ⊗↑.t S.t ↗s.[ Υ ] ⊗↑.t P ↗t.[ Γ ]) ⊆ P τ
    ς⟨ Υ , Γ ⟩ = ς ⇒.∘ ⊙.ι ⇒.∘ aux₂ ⇒.∘ aux₁
      where
        aux₁
          : {Υ′ : SCtx.t (Sign.𝒮 Σ)}
          → {Γ′ : TCtx.t (Sign.𝒮 Σ)}
          → {h  : H.t} (let Υ ∥ Γ = h)
          → {τ  : Sign.𝒮 Σ}
          → h ∈
              (P τ ↗.t 𝓎.t (Υ′ ∥ Γ′)
                ⊗↑.t S.t ↗s.[ Υ′ ]
                ⊗↑.t   P ↗t.[ Γ′ ])
          → P τ (Υ ⧺s Υ′ ∥ Γ ⧺t Γ′)
              ⊗.t h ∈ S.t ↗s.[ Υ  ]
              ⊗.t h ∈ S.t ↗s.[ Υ′ ]
              ⊗.t h ∈   P ↗t.[ Γ  ]
              ⊗.t h ∈   P ↗t.[ Γ′ ]
        aux₁ {Υ′ = Υ′} {Γ′ = Γ′} {h = Υ ∥ Γ} (⊗↑.ι (↗.ι m , ⊗↑.ι (↗s.ι □Υ′ , ↗t.ι □Γ′))) =
          ( m
             (⊗↑.ι
               ( 𝓎.ι (SRen.weakening.inl Υ′ , TRen.weakening.inl Γ′)
               , 𝓎.ι (SRen.weakening.inr Υ , TRen.weakening.inr Γ)
               )
             )
          , ↗s.ι (□-id-s Υ)
          , ↗s.ι □Υ′
          , ↗t.ι (□-ν-t Γ)
          , ↗t.ι □Γ′
          )

          where
            □-id-s : (Υ : SCtx.t (Sign.𝒮 Σ)) → □.t (λ τ → S.t τ (Υ ∥ Γ)) (sctx Υ)
            □-id-s (SCtx.ι Vec.[]) = □.[]
            □-id-s (SCtx.ι (_ Vec.∷ τs)) =
              S.ι ((Sym.ι Fin.ze) ∐., ≡.idn) □.∷
                □.map
                  (λ { (S.ι (s ∐., p)) → S.ι (Sym.su s ∐., p) })
                  (□-id-s (SCtx.ι τs))

            □-id-t : (Γ : TCtx.t (Sign.𝒮 Σ)) → □.t (λ τ → V.t τ (Υ ∥ Γ)) (tctx Γ)
            □-id-t (TCtx.ι Vec.[]) = □.[]
            □-id-t (TCtx.ι (_ Vec.∷ τs)) =
              V.ι ((Var.ι Fin.ze) ∐., ≡.idn) □.∷
                □.map
                  (λ { (V.ι (x ∐., p)) → V.ι (Var.su x ∐., p) })
                  (□-id-t (TCtx.ι τs))

            □-ν-t : (Γ : TCtx.t (Sign.𝒮 Σ)) → □.t (λ τ → P τ (Υ ∥ Γ)) (tctx Γ)
            □-ν-t = □.map ν ⇒.∘Π □-id-t

        aux₂
          : {Υ′ : SCtx.t (Sign.𝒮 Σ)}
          → {Γ′ : TCtx.t (Sign.𝒮 Σ)}
          → {h  : H.t} (let Υ ∥ Γ = h)
          → {τ  : Sign.𝒮 Σ}
          → P τ (Υ ⧺s Υ′ ∥ Γ ⧺t Γ′)
              ⊗.t h ∈ S.t ↗s.[ Υ  ]
              ⊗.t h ∈ S.t ↗s.[ Υ′ ]
              ⊗.t h ∈   P ↗t.[ Γ  ]
              ⊗.t h ∈   P ↗t.[ Γ′ ]
          → h ∈ (P τ ⊚.t P)
        aux₂ (M , ↗Υ , ↗Υ′ , ↗Γ , ↗Γ′) =
          ⊚.ι
            (⨛.ι[ _ ∥ _ ]
              ( M
              , ↗s.⧺ (⊗↑.ι (↗Υ , ↗Υ′))
              , ↗t.⧺ (⊗↑.ι (↗Γ , ↗Γ′))
              )
            )

    -- interpretation of contexts
    ⟦_⟧m : MCtx.t (Sign.𝒮 Σ) → ℘.T H.t
    ⟦ Ω ⟧m = P ↗m.[ Ω ]

    ⟦_⟧s : SCtx.t (Sign.𝒮 Σ) → ℘.T H.t
    ⟦ Υ ⟧s = S.t ↗s.[ Υ ]

    ⟦_⟧t : TCtx.t (Sign.𝒮 Σ) → ℘.T H.t
    ⟦ Γ ⟧t = V.t ↗t.[ Γ ]

    ⟦_>_∥_⟧ : MCtx.t (Sign.𝒮 Σ) → SCtx.t (Sign.𝒮 Σ) → TCtx.t (Sign.𝒮 Σ) → ℘.T H.t
    ⟦ Ω > Υ ∥ Γ ⟧ = ⟦ Ω ⟧m ⊗↑.t ⟦ Υ ⟧s ⊗↑.t ⟦ Γ ⟧t

    -- interpretation of terms
    {-# TERMINATING #-}
    ⟦_⟧_ : ∀ {Ω Υ Γ s} → Ω > Υ ∥ Γ ⊢ s → ⟦ Ω > Υ ∥ Γ ⟧ ⊆ P s
    ⟦ tvar x ⟧ ⊗↑.ι (_ , ⊗↑.ι (_ , ⟦Γ⟧)) = ν (↗t.lookup x ⟦Γ⟧)
    ⟦ mvar 𝔪 us Ms ⟧ ρ =
      let
        ⊗↑.ι (⟦Ω⟧ , ⊗↑.ι (⟦Υ⟧ , ⟦Γ⟧)) = ρ
      in
        ς⟨ _ , _ ⟩
          (⊗↑.ι
            ( ↗m.lookup 𝔪 ⟦Ω⟧
            , ⊗↑.ι
                ( ↗s.ι
                    (□.map
                      (λ { (Sym.ι x ∐., p) →
                             ≡.map
                               (λ c → S.t c _)
                               (≡.inv p)
                               (□.π x (↗s.π ⟦Υ⟧))
                         }
                      )
                      us
                    )
                , ↗t.ι (□.map (⟦_⟧ ρ) Ms)
                )
            )
          )
    ⟦_⟧_ {Ω = Ω} {Υ = Υ} {Γ = Γ} (app {𝒶} ϑ Ms) {Υ′ ∥ Δ} (⊗↑.ι (⟦Ω⟧ , ⊗↑.ι (⟦Υ⟧ , ⟦Γ⟧))) =
      α ( 𝒶
      ∐., ( ≡.idn
          , ( Sign.map
               Σ
               (SRen.ρ
                 (λ s → ∐.π₀ (S.π (↗s.lookup s ⟦Υ⟧)))
                 (∐.π₁ (S.π (↗s.lookup _ ⟦Υ⟧)))
               )
               ϑ
          ∐., □.map
                (λ {𝓋} M →
                  ↗.ι
                    (λ { {h} (⊗↑.ι (𝓎.ι (Υ′↪Υ″ , Δ↪Δ′) , 𝓎.ι (Υ𝓋↪Υ″ , Γ𝓋↪Δ′))) →
                         let
                           ⟦Υ⟧′ : h ∈ ⟦ Υ ⟧s
                           ⟦Υ⟧′ =
                             ↗s.ι
                               (□.tabulate λ i →
                                 let
                                   S.ι (s ∐., [s]) = ↗s.lookup (Sym.ι i) ⟦Υ⟧
                                 in
                                   S.ι (SRen.map Υ′↪Υ″ s ∐., (SRen.coh Υ′↪Υ″ ≡.∘ [s]))
                               )

                           ⟦Υ𝓋⟧ : h ∈ ⟦ 𝒱.Υ 𝓋 ⟧s
                           ⟦Υ𝓋⟧ = ↗s.ι (□.tabulate λ i → S.ι (SRen.map Υ𝓋↪Υ″ (Sym.ι i) ∐., SRen.coh Υ𝓋↪Υ″))

                           ⟦Γ⟧′ : h ∈ ⟦ Γ ⟧t
                           ⟦Γ⟧′ =
                             ↗t.ι
                               (□.tabulate λ i →
                                 let
                                   V.ι (x ∐., [x]) = ↗t.lookup (Var.ι i) ⟦Γ⟧
                                 in
                                   V.ι ((TRen.map Δ↪Δ′ x) ∐., (TRen.coh Δ↪Δ′ ≡.∘ [x]))
                               )

                           ⟦Γ𝓋⟧ : h ∈ ⟦ 𝒱.Γ 𝓋 ⟧t
                           ⟦Γ𝓋⟧ = ↗t.ι (□.tabulate λ i → V.ι (TRen.map Γ𝓋↪Δ′ (Var.ι i) ∐., TRen.coh Γ𝓋↪Δ′))

                           ⟦Ω⟧′ : h ∈ ⟦ Ω ⟧m
                           ⟦Ω⟧′ =
                             ↗m.ι
                               (□.tabulate λ i →
                                 ↗.ι
                                   λ { (⊗↑.ι (𝓎.ι (Υ″↪c₀ , Δ′↪c₁) , 𝓎.ι (Υ𝓋↪c₀ , Γ𝓋↪c₁))) →
                                         ↗.π
                                           (↗m.lookup (Var.ι i) ⟦Ω⟧)
                                           (⊗↑.ι
                                             ( 𝓎.ι
                                                 ( s↪cmp Υ″↪c₀ Υ′↪Υ″
                                                 , t↪cmp Δ′↪c₁ Δ↪Δ′
                                                 )
                                             , 𝓎.ι
                                                 ( Υ𝓋↪c₀
                                                 , Γ𝓋↪c₁
                                                 )
                                             )
                                           )
                                     }
                               )

                         in
                           ⟦ M ⟧
                             ⊗↑.ι
                               ( ⟦Ω⟧′
                               , ⊗↑.ι
                                   ( ↗s.⧺ (⊗↑.ι (⟦Υ⟧′ , ⟦Υ𝓋⟧))
                                   , ↗t.⧺ (⊗↑.ι (⟦Γ⟧′ , ⟦Γ𝓋⟧))
                                   )
                               )
                       }
                    )
                )
                Ms
            )
          )
        )

\end{code}
