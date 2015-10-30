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

syntax ∫↓ (λ i → P) = ∫↓[ i ] P
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

syntax ∫↑ (λ i → P) = ∫↑[ i ] P
\end{code}

\begin{code}
SET[_,_] : (A B : Set) → Set
SET[ A , B ] = A → B
\end{code}

\begin{code}
infix 0 _⊗_
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
LanG 𝒟[_,_] _⟦⊗⟧_ J F d = ∫↑[ c ] (F c ⟦⊗⟧ 𝒟[ J c , d ])

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
RanG 𝒟[_,_] _⟦⋔⟧_ J F d = ∫↓[ c ] (𝒟[ d , J c ] ⟦⋔⟧ F c)

Ran : {𝒞 : Set} (J F : 𝒞 → Set) (A : Set) → Set
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
data _∣_∥_⊢_ (Σ : Sign) {m} {n} (Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) : (s : 𝒮 Σ) → Set where
  v : (x : Name n) → Σ ∣ Υ ∥ Γ ⊢ Γ x
\end{code}
%</trees>

%<*substitution>
\begin{code}
module _ (Σ : Sign) where
  _●_
    : (A : ∀ {m}{n} (Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) → Set)
    → (P : 𝒮 Σ → ∀ {m}{n} (Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) → Set)
    → ∀ {m}{n}(Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) → Set
  (A ● P) {n = n} Υ Γ = ∫↑[ Δ ] (A {n = n} Υ Δ ⊗ ∫↓[ x ] P (Δ x) Υ Γ)

  -- Lan version
  _●ᴸ_
    : (A : ∀ {m}{n} (Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) → Set)
    → (P : 𝒮 Σ → ∀ {m}{n} (Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) → Set)
    → ∀ {m}{n}(Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) → Set
  (A ●ᴸ P) {n = n} Υ Γ = LanG (λ δ γ → ∫↓[ x ] P (δ x) Υ γ) _⊗_ id (A {n = n} Υ) Γ

  _⊙_
    : (P Q : 𝒮 Σ → ∀ {m}{n} (Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) → Set)
    → (s : 𝒮 Σ)
    → ∀ {m}{n}(Υ : Ctx (𝒮 Σ) m) (Γ : Ctx (𝒮 Σ) n) → Set
  (P ⊙ Q) s = P s ● Q
\end{code}
%</substitution>
