\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where

infixr 2 _~>_

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

module ⨜ where
  record t {I : Set} (P : 𝔓 I) : Set where
    no-eta-equality
    constructor ι
    field
      π : ∀ {i} → P i
  open t public

  infixr 1 t
  syntax t {I = I} (λ i → P) = [ I ∋ i ] P

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
fam ϕ = ∃ (tot ϕ) ↓ (fib ϕ)

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
    syntax tlen Γ = #t Γ
    syntax tidx Γ x = Γ [ x ]t
    syntax tpre Γ τ = [ Γ ]t⁻¹ τ
  open t public
open TCtx hiding (t; ι)

_⧺_ : ∀ {𝒮 : Set} (Γ Γ′ : TCtx.t 𝒮) → TCtx.t 𝒮
_⧺_ {𝒮} Γ Γ′ = TCtx.ι (#t Γ Nat.+ #t Γ′) aux
  where
    aux : (i : Var.t (#t Γ Nat.+ #t Γ′)) → 𝒮
    aux (Var.ι i) with Fin.split (#t Γ) (#t Γ′) i
    aux (Var.ι .(Fin.inl        i)) | Fin.split-inl i = Γ  [ Var.ι i ]t
    aux (Var.ι .(Fin.inr {#t Γ} j)) | Fin.split-inr j = Γ′ [ Var.ι j ]t

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
    syntax slen Υ = #s Υ
    syntax sidx Υ α = Υ [ α ]s
    syntax spre Υ τ = [ Υ ]s⁻¹ τ
  open t public
open SCtx hiding (t; ι)

_∋⟨_,_⟩s : ∀ {𝒮} (Υ : SCtx.t 𝒮) (x : sdom Υ ) (s : 𝒮) → Set
Υ ∋⟨ x , s ⟩s = Υ [ x ]s ≡.t s

_∋⟨_,_⟩t : ∀ {𝒮} (Γ : TCtx.t 𝒮) (x : tdom Γ ) (s : 𝒮) → Set
Γ ∋⟨ x , s ⟩t = Γ [ x ]t ≡.t s

-- FIXME: named projections
module 𝒱 where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : SCtx.t 𝒮 ⊗.t TCtx.t 𝒮 ⊗.t 𝒮
  open t public

-- FIXME: named projections
module 𝒜 where
  record t (𝒮 : Set) : Set where
    no-eta-equality
    constructor ι
    field
      π : TCtx.t (𝒱.t 𝒮) ⊗.t 𝒮
  open t public

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

module TRen where
  record t {A} (Γ Γ′ : TCtx.t A) : Set where
    no-eta-equality
    constructor ρ
    field
      map : tdom Γ → tdom Γ′
      coh : ∀ {i} → Γ [ i ]t ≡.t Γ′ [ map i ]t
  open t public

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
  -- infixr 1 _⊗↑_

  module H where
    record t : Set where
      no-eta-equality
      constructor ι
      field
        π : SCtx.t (Sign.𝒮 Σ) ⊗.t TCtx.t (Sign.𝒮 Σ)
    open t public
  pattern _∥_ Υ Γ = H.ι (Υ , Γ)

  module H↑ where
    record t : Set where
      no-eta-equality
      constructor ι
      field
        π : 𝔓 H.t
    open t public

  module *𝒴 where
    abstract
      t : Set
      t = H.t → H↑.t

      act : t
      act (Υ ∥ Γ) = H↑.ι λ { (Υ′ ∥ Γ′) → (Υ ↪s Υ′) ⊗.t (Γ ↪t Γ′) }

      ι : (H.t → H↑.t) → t
      ι x = x

      π : t → (H.t → H↑.t)
      π x = x

  𝓎 : H.t → H↑.t
  𝓎 x = *𝒴.π *𝒴.act x

  module *⊗ where
    abstract
      t : Set
      t = H↑.t → H↑.t → H↑.t

      act : t
      act A B = H↑.ι λ h → H↑.π A h ⊗.t H↑.π B h

      ι : (H↑.t → H↑.t → H↑.t) → t
      ι x = x

      π : t → (H↑.t → H↑.t → H↑.t)
      π x = x

  _⊗↑_ : H↑.t → H↑.t → H↑.t
  A ⊗↑ B = *⊗.π *⊗.act A B

  module *↗ where
    abstract
      t : Set
      t = H↑.t → H↑.t → H↑.t

      act : t
      act B A = H↑.ι λ h → H↑.π (𝓎 h ⊗↑ A) ~> H↑.π B

      ι : (H↑.t → H↑.t → H↑.t) → t
      ι x = x

      π : t → (H↑.t → H↑.t → H↑.t)
      π x = x

  _↗_ : H↑.t → H↑.t → H↑.t
  (B ↗ A) = *↗.π *↗.act B A

  module *S where
    abstract
      t : Set
      t = Sign.𝒮 Σ → H↑.t

      act : t
      act τ = H↑.ι λ { (Υ ∥ Γ) → [ Υ ]s⁻¹ τ }

      ι : (Sign.𝒮 Σ → H↑.t) → t
      ι x = x

      π : t → (Sign.𝒮 Σ → H↑.t)
      π x = x

  S : (τ : Sign.𝒮 Σ) → H↑.t
  S τ = *S.π *S.act τ

  module *V where
    abstract
      t : Set
      t = Sign.𝒮 Σ → H↑.t

      act : t
      act τ = H↑.ι λ { (Υ ∥ Γ) → [ Γ ]t⁻¹ τ }

      ι : (Sign.𝒮 Σ → H↑.t) → t
      ι x = x

      π : t → (Sign.𝒮 Σ → H↑.t)
      π x = x

  V : (τ : Sign.𝒮 Σ) → H↑.t
  V τ = *V.π *V.act τ

  module *↗[]t where
    abstract
      t : Set
      t = (X : (τ : Sign.𝒮 Σ) → H↑.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → H↑.t

      act : t
      act X Γ = H↑.ι λ h → ⨜.[ tdom Γ ∋ x ] H↑.π (X (Γ [ x ]t)) h

      ι : ((X : (τ : Sign.𝒮 Σ) → H↑.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → H↑.t) → t
      ι x = x

      π : t → ((X : (τ : Sign.𝒮 Σ) → H↑.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → H↑.t)
      π x = x

  _↗[_]t : (X : (τ : Sign.𝒮 Σ) → H↑.t) (Γ : TCtx.t (Sign.𝒮 Σ)) → H↑.t
  X ↗[ Γ ]t = *↗[]t.π *↗[]t.act X Γ

  module *↗[]s where
    abstract
      t : Set
      t = (X : (τ : Sign.𝒮 Σ) → H↑.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → H↑.t

      act : t
      act X Υ = H↑.ι λ h → ⨜.[ sdom Υ ∋ x ] H↑.π (X (Υ [ x ]s)) h

      ι : ((X : (τ : Sign.𝒮 Σ) → H↑.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → H↑.t) → t
      ι x = x

      π : t → ((X : (τ : Sign.𝒮 Σ) → H↑.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → H↑.t)
      π x = x

  _↗[_]s : (X : (τ : Sign.𝒮 Σ) → H↑.t) (Γ : SCtx.t (Sign.𝒮 Σ)) → H↑.t
  X ↗[ Υ ]s = *↗[]s.π *↗[]s.act X Υ

  module *⊚ where
    abstract
      t : Set
      t = (A : H↑.t) (P : (τ : Sign.𝒮 Σ) → H↑.t) → H↑.t

      act : t
      act A P = H↑.ι λ h →
        ⨛.[ H.t ∋ h′ ] let Υ′ ∥ Γ′ = h′ in
          H↑.π A (Υ′ ∥ Γ′)
            ⊗.t H↑.π (S ↗[ Υ′ ]s) h
            ⊗.t H↑.π (P ↗[ Γ′ ]t) h

      ι : ((A : H↑.t) (P : (τ : Sign.𝒮 Σ) → H↑.t) → H↑.t) → t
      ι x = x

      π : t → ((A : H↑.t) (P : (τ : Sign.𝒮 Σ) → H↑.t) → H↑.t)
      π x = x

  _⊚_ : (A : H↑.t) (P : (τ : Sign.𝒮 Σ) → H↑.t) → H↑.t
  (A ⊚ P) = *⊚.π *⊚.act A P

  module *⊙ where
    abstract
      t : Set
      t = (P Q : (τ : Sign.𝒮 Σ) → H↑.t) → ((τ : Sign.𝒮 Σ) → H↑.t)

      act : t
      act P Q τ = P τ ⊚ Q

      ι : ((P Q : (τ : Sign.𝒮 Σ) → H↑.t) → ((τ : Sign.𝒮 Σ) → H↑.t)) → t
      ι x = x

      π : t → ((P Q : (τ : Sign.𝒮 Σ) → H↑.t) → ((τ : Sign.𝒮 Σ) → H↑.t))
      π x = x

  _⊙_ : (P Q : (τ : Sign.𝒮 Σ) → H↑.t) → ((τ : Sign.𝒮 Σ) → H↑.t)
  P ⊙ Q = *⊙.π *⊙.act P Q

  data _>_∥_⊢_
    (Ω : MCtx.t (Sign.𝒮 Σ))
    (Υ : SCtx.t (Sign.𝒮 Σ))
    (Γ : TCtx.t (Sign.𝒮 Σ))
      : (τ : Sign.𝒮 Σ) → Set where
    tvar
      : (x : tdom Γ)
      → Ω > Υ ∥ Γ ⊢ (Γ [ x ]t)
    mvar
      : (m : mdom Ω)
      (let 𝒱.ι (ps , qs , τ) = Ω [ m ]m)
      → (∀ α → [ Υ ]s⁻¹ (ps [ α ]s))
      → (∀ x → Ω > Υ ∥ Γ ⊢ (qs [ x ]t))
      → Ω > Υ ∥ Γ ⊢ τ
\end{code}
