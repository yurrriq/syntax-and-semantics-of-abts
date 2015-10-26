\begin{code}
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

%<*var>
\begin{code}
Var : (n : Nat) → Set
Var = Fin
\end{code}
%</var>

%<*sctx>
\begin{code}
SCtx : (𝒮 : Set) (n : Nat) → Set
SCtx 𝒮 n = Var n → 𝒮
\end{code}
%</sctx>

%<*sign>
\begin{code}
record Sign : Set₁ where
  field
    𝒮 : Set
    𝒜 : Set
    𝒪 : ∀ {n} → SCtx 𝒮 n × 𝒜 → Set
open Sign
\end{code}
%</sign>

%<*trees>
\begin{code}
data _∣_⊢_ (Σ : Sign) {n} (Υ : SCtx (𝒮 Σ) n) : (s : 𝒮 Σ) → Set where
  v : (x : Fin n) → Σ ∣ Υ ⊢ Υ x
\end{code}
%</trees>
