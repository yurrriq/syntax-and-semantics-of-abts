\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where
\end{code}

\begin{code}
data _≡_ {A} x : A → Set where
  refl : x ≡ x
\end{code}

%<*nat>
\begin{code}
data Nat : Set where
  ze : Nat
  su : (n : Nat) → Nat
\end{code}
%</nat>

%<*fin>
\begin{code}
data Fin : (n : Nat) → Set where
  ze : ∀ {n} → Fin (su n)
  su : ∀ {n} → Fin n → Fin (su n)
\end{code}
%</fin>

\begin{code}
infix 0 _⊗_
\end{code}
\begin{code}
record ∐ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst
open ∐

_⊗_ : (A B : Set) → Set
A ⊗ B = ∐ A λ _ → B
\end{code}

\begin{code}
∫↓ : {I : Set} → (I → Set) → Set
∫↓ {I = I} P = ∀ i → P i

syntax ∫↓ {I = I} (λ i → P) = ∫↓ I ∋ i [ P ]
\end{code}

\begin{code}
infix 1 ∫↑
infix 1 ∫↓
\end{code}
\begin{code}
record ∫↑ {I : Set} (P : I → Set) : Set where
  constructor s↑
  field
    π∫₀ : I
    π∫₁ : P π∫₀
open ∫↑ public

syntax ∫↑ {I = I} (λ i → P) = ∫↑ I ∋ i [ P ]
\end{code}

\begin{code}
SET[_,_] : (A B : Set) → Set
SET[ A , B ] = A → B
\end{code}

\begin{code}
_⇒_ : (A B : Set) → Set
A ⇒ B = A → B

id : {A : Set} → A → A
id x = x
\end{code}

%<*lan>
\begin{code}
LanG
  : {𝒞 𝒟 𝔙 : Set}
  → (𝒟[_,_] : 𝒟 → 𝒟 → Set) (_⟦⊗⟧_ : 𝔙 → Set → Set)
  → (J : 𝒞 → 𝒟) (F : 𝒞 → 𝔙)
  → (𝒟 → Set)
LanG 𝒟[_,_] _⟦⊗⟧_ J F d = ∫↑ _ ∋ c [ F c ⟦⊗⟧ 𝒟[ J c , d ] ]

Lan : {𝒞 : Set} (J F : 𝒞 → Set) (A : Set) → Set
Lan J F A = LanG SET[_,_] _⊗_ J F A
\end{code}
%</lan>

%<*ran>
\begin{code}
RanG
  : {𝒞 𝒟 𝔙 : Set}
  → (𝒟[_,_] : 𝒟 → 𝒟 → Set) (_⟦⋔⟧_ : Set → 𝔙 → Set)
  → (J : 𝒞 → 𝒟) (F : 𝒞 → 𝔙)
  → (𝒟 → Set)
RanG 𝒟[_,_] _⟦⋔⟧_ J F d = ∫↓ _ ∋ c [ 𝒟[ d , J c ] ⟦⋔⟧ F c ]

Ran : {𝒞 : Set} (J F : 𝒞 → Set) (A : Set) → Set
Ran J F A = RanG SET[_,_] _⇒_ J F A
\end{code}
%</ran>

%<*name>
\begin{code}
Var : Nat → Set
Var = Fin

Sym : Nat → Set
Sym = Fin
\end{code}
%</name>

%<*ctx>
\begin{code}
Ctx : (𝒮 : Set) → Set
Ctx 𝒮 = ∐ Nat λ n → Var n → 𝒮

SCtx : (𝒮 : Set) → Set
SCtx 𝒮 = ∐ Nat λ n → Sym n → 𝒮

_∋⟨_,_⟩ : ∀ {𝒮} (Γ : Ctx 𝒮) (x : Var (fst Γ)) (s : 𝒮) → Set
Γ ∋⟨ x , s ⟩ = snd Γ x ≡ s
\end{code}
%</ctx>

%<*sign>
\begin{code}
record Sign : Set₁ where
  field
    𝒮 : Set
    𝒜 : Set
    𝒪 : SCtx 𝒮 ⊗ 𝒜 → Set
open Sign
\end{code}
%</sign>

%<*trees>
\begin{code}
data _∣_∥_⊢_ (Σ : Sign) (Υ : SCtx (𝒮 Σ)) (Γ : Ctx (𝒮 Σ)) : (s : 𝒮 Σ) → Set where
  v : ∀ {x s}
    → (ϕ : Γ ∋⟨ x , s ⟩)
    → Σ ∣ Υ ∥ Γ ⊢ s
\end{code}
%</trees>

%<*substitution>
\begin{code}
module _ (Σ : Sign) where
  H : Set
  H = SCtx (𝒮 Σ) ⊗ Ctx (𝒮 Σ)

  H↑ : Set
  H↑ = H → Set

  V : (s : 𝒮 Σ) → H↑
  V s ⟨ Υ , Γ ⟩ = ∐ _ λ x → Γ ∋⟨ x , s ⟩

  _⊢_ : (Υ×Γ : H) (s : 𝒮 Σ) → Set
  ⟨ Υ , Γ ⟩ ⊢ s = Σ ∣ Υ ∥ Γ ⊢ s

  _⊙_ : (P Q : (s : 𝒮 Σ) → H↑) (s : 𝒮 Σ) → H↑
  (P ⊙ Q) s ⟨ Υ , Γ ⟩ =
    ∫↑ _ ∋ Δ [ P s ⟨ Υ , Δ ⟩ ⊗
      ∫↓ V s ⟨ Υ , Δ ⟩ ∋ x [ P (snd Δ (fst x)) ⟨ Υ , Γ ⟩ ] ]

  _~>_ : ∀ {𝒞₀} (F G : 𝒞₀ → Set) → Set
  F ~> G = ∀ {c} → F c → G c

  module _
    (P : (s : 𝒮 Σ) → H↑)
    (ν : ∀ {s} → V s ~> P s)
    (ς : ∀ {s} → (P ⊙ P) s ~> P s)
    where

    _=≪_
      : ∀ {s Υ Δ Γ}
      → (k : (x : V s ⟨ Υ , Δ ⟩) → P (snd Δ (fst x)) ⟨ Υ , Γ ⟩)
      → ((D : P s ⟨ Υ , Δ ⟩) → P s ⟨ Υ , Γ ⟩)
    k =≪ D = ς (s↑ _ ⟨ D , k ⟩)
\end{code}
%</substitution>
