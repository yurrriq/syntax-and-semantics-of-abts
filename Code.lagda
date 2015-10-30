\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where
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
record ∐ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : (A : Set) (B : Set) → Set
A × B = ∐ A (λ _ → B)
\end{code}

\begin{code}
∫↓ : {I : Set} → (I → Set) → Set
∫↓ {I = I} P = ∀ i → P i

syntax ∫↓ {I = I} (λ i → P) = ∫↓[ i ∶ I ] P
\end{code}

\begin{code}
record ∫↑ {I : Set} (P : I → Set) : Set where
  constructor s↑
  field
    π∫₀ : I
    π∫₁ : P π∫₀
open ∫↑ public

syntax ∫↑ {I = I} (λ i → P) = ∫↑[ i ∶ I ] P
\end{code}

\begin{code}
SET[_,_] : (A B : Set) → Set
SET[ A , B ] = A → B
\end{code}

\begin{code}
record _⊗_ (A B : Set) : Set where
  constructor _,_
  field
    π⊗₀ : A
    π⊗₁ : B
open _⊗_ public
\end{code}

\begin{code}
_⇒_ : (A B : Set) → Set
A ⇒ B = A → B
\end{code}

%<*lan>
\begin{code}
LanG
  : ∀ {𝒞₀ : Set} {𝒟₀ : Set} {𝒱₀ : Set}
  → (𝒟₁[_,_] : 𝒟₀ → 𝒟₀ → Set)
  → (_⟦⊗⟧_ : 𝒱₀ → Set → Set)
  → (J : 𝒞₀ → 𝒟₀)
  → (F : 𝒞₀ → 𝒱₀)
  → (𝒟₀ → Set)
LanG {𝒞₀ = 𝒞₀} 𝒟₁[_,_] _⟦⊗⟧_ J F d = ∫↑[ c ∶ 𝒞₀ ] (F c ⟦⊗⟧ 𝒟₁[ J c , d ])

Lan
  : {𝒞₀ : Set}
  → (J : 𝒞₀ → Set)
  → (F : 𝒞₀ → Set)
  → (A : Set)
  → Set
Lan J F A = LanG SET[_,_] _⊗_ J F A
\end{code}
%</lan>

%<*ran>
\begin{code}
RanG
  : ∀ {𝒞₀ : Set} {𝒟₀ : Set} {𝒱₀ : Set}
  → (𝒟₁[_,_] : 𝒟₀ → 𝒟₀ → Set)
  → (_⟦⋔⟧_ : Set → 𝒱₀ → Set)
  → (J : 𝒞₀ → 𝒟₀)
  → (F : 𝒞₀ → 𝒱₀)
  → (𝒟₀ → Set)
RanG {𝒞₀ = 𝒞₀} 𝒟₁[_,_] _⟦⋔⟧_ J F d = ∫↓[ c ∶ 𝒞₀ ] (𝒟₁[ d , J c ] ⟦⋔⟧ F c)

Ran
  : {𝒞₀ : Set}
  → (J : 𝒞₀ → Set)
  → (F : 𝒞₀ → Set)
  → (A : Set)
  → Set
Ran J F A = RanG SET[_,_] _⇒_ J F A
\end{code}
%</ran>

%<*name>
\begin{code}
Name : (n : Nat) → Set
Name = Fin
\end{code}
%</name>

%<*ctx>
\begin{code}
Ctx : (𝒮 : Set) (n : Nat) → Set
Ctx 𝒮 n = Name n → 𝒮
\end{code}
%</ctx>

%<*sign>
\begin{code}
record Sign : Set₁ where
  field
    𝒮 : Set
    𝒜 : Set
    𝒪 : ∀ {n} → Ctx 𝒮 n × 𝒜 → Set
open Sign
\end{code}
%</sign>

%<*trees>
\begin{code}
data _∣_∥_⊢_ (Σ : Sign) {m} {n} (Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮  Σ) n) : (s : 𝒮 Σ) → Set where
  v : (x : Name n) → Σ ∣ Υ ∥ Γ ⊢ Γ x
\end{code}
%</trees>
