\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where
\end{code}

\begin{code}
infix 1 ∫↑
infix 1 ∫↓
infixr 0 _,_
infixr 0 _⊗_
infixr 2 ![_]
infixr 1 _∘_
infixr 1 _∘Π_
\end{code}

\begin{code}
data _≡_ {A} x : A → Set where
  refl : x ≡ x
\end{code}

\begin{code}
_⇒_ : (A B : Set) → Set
A ⇒ B = A → B
\end{code}

\begin{code}
id : ∀ {A} → A → A
id x = x
\end{code}

\begin{code}
_∘_ : ∀ {A B C} (g : B → C) (f : A → B) → (A → C)
(g ∘ f) x = g (f x)
\end{code}

\begin{code}
_∘Π_
  : ∀ {A}{B : A → Set}{C : ∀ {a} (b : B a) → Set}
  → (g : ∀ {a} (b : B a) → C b)
  → (f : (a : A) → B a)
  → ((a : A) → C (f a))
(g ∘Π f) x = g (f x)
\end{code}

\begin{code}
![_] : ∀ {A B} → A → (B → A)
![_] a _ = a
\end{code}

\begin{code}
record ∐ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
\end{code}
\begin{code}
open ∐
\end{code}

\begin{code}
_⊗_ : (A B : Set) → Set
A ⊗ B = ∐ A λ _ → B
\end{code}

\begin{code}
⟨_,_⟩
  : ∀ {X A B}
  → (f : X → A)
  → (g : X → B)
  → ((x : X) → A ⊗ B)
⟨ f , g ⟩ x = f x , g x
\end{code}

\begin{code}
⟨_,Π_⟩
  : ∀ {X}{A : (x : X) → Set}{B : (x : X) (a : A x) → Set}
  → (f : (x : X) → A x)
  → (g : (x : X) → B x (f x))
  → ((x : X) → A x ⊗ B x (f x))
⟨ f ,Π g ⟩ x = f x , g x
\end{code}

\begin{code}
∫↓ : {I : Set} → (I → Set) → Set
∫↓ {I = I} P = ∀ i → P i
\end{code}

\begin{code}
syntax ∫↓ {I = I} (λ i → P) = ∫↓ I ∋ i ⟪ P ⟫
\end{code}

\begin{code}
record ∫↑ {I : Set} (P : I → Set) : Set where
  constructor s↑
  field
    {π∫₀} : I
    π∫₁ : P π∫₀
\end{code}
\begin{code}
open ∫↑ public
\end{code}

\begin{code}
syntax ∫↑ {I = I} (λ i → P) = ∫↑ I ∋ i ⟪ P ⟫
\end{code}

\begin{code}
SET[_,_] : (A B : Set) → Set
SET[ A , B ] = A → B
\end{code}

%<*lang>
\begin{code}
LanG
  : {𝒞 𝒟 𝔙 : Set}
  → (𝒟[_,_] : 𝒟 → 𝒟 → Set) (_⟦⊗⟧_ : 𝔙 → Set → Set)
  → (J : 𝒞 → 𝒟) (F : 𝒞 → 𝔙)
  → (𝒟 → Set)
LanG 𝒟[_,_] _⟦⊗⟧_ J F d = ∫↑ _ ∋ c ⟪ F c ⟦⊗⟧ 𝒟[ J c , d ] ⟫
\end{code}
%</lang>

%<*lan>
\begin{code}
Lan : {𝒞 : Set} (J F : 𝒞 → Set) (A : Set) → Set
Lan J F A = LanG SET[_,_] _⊗_ J F A
\end{code}
%</lan>

%<*rang>
\begin{code}
RanG
  : {𝒞 𝒟 𝔙 : Set}
  → (𝒟[_,_] : 𝒟 → 𝒟 → Set) (_⟦⋔⟧_ : Set → 𝔙 → Set)
  → (J : 𝒞 → 𝒟) (F : 𝒞 → 𝔙)
  → (𝒟 → Set)
RanG 𝒟[_,_] _⟦⋔⟧_ J F d = ∫↓ _ ∋ c ⟪ 𝒟[ d , J c ] ⟦⋔⟧ F c ⟫
\end{code}
%</rang>

%<*ran>
\begin{code}
Ran : {𝒞 : Set} (J F : 𝒞 → Set) (A : Set) → Set
Ran J F A = RanG SET[_,_] _⇒_ J F A
\end{code}
%</ran>

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

%<*var>
\begin{code}
Var : Nat → Set
Var = Fin
\end{code}
%</var>

%<*sym>
\begin{code}
Sym : Nat → Set
Sym = Fin
\end{code}
%</sym>

%<*ctx>
\begin{code}
Ctx : (𝒮 : Set) → Set
Ctx 𝒮 = ∐ Nat λ n → Var n → 𝒮
\end{code}
%</ctx>

%<*sctx>
\begin{code}
SCtx : (𝒮 : Set) → Set
SCtx 𝒮 = ∐ Nat λ n → Sym n → 𝒮
\end{code}
%</sctx>

%<*elem>
\begin{code}
_∋⟨_,_⟩ : ∀ {𝒮} (Γ : Ctx 𝒮) (x : Var (fst Γ)) (s : 𝒮) → Set
Γ ∋⟨ x , s ⟩ = snd Γ x ≡ s
\end{code}
%</elem>

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

\begin{code}
module _ (Σ : Sign) where
\end{code}

%<*H>
\begin{code}
  H : Set
  H = SCtx (𝒮 Σ) ⊗ Ctx (𝒮 Σ)
\end{code}
%</H>

%<*HHat>
\begin{code}
  H↑ : Set
  H↑ = H → Set
\end{code}
%</HHat>

%<*V>
\begin{code}
  V : (s : 𝒮 Σ) → H↑
  V s (Υ , Γ) = ∐ _ λ x → Γ ∋⟨ x , s ⟩
\end{code}
%</V>

\begin{code}
  _⊢_ : (Υ×Γ : H) (s : 𝒮 Σ) → Set
  (Υ , Γ) ⊢ s = Σ ∣ Υ ∥ Γ ⊢ s
\end{code}

%<*tensor0>
\begin{code}
  _⊚_ : (A : H↑) (P : (s : 𝒮 Σ) → H↑) → H↑
  (A ⊚ P) (Υ , Γ) =
    ∫↑ Ctx (𝒮 Σ) ∋ Δ ⟪ A (Υ , Δ) ⊗
      ∫↓ Var (fst Δ) ∋ x ⟪ P (snd Δ x) (Υ , Γ) ⟫ ⟫
\end{code}
%</tensor0>

%<*tensor1>
\begin{code}
  _⊙_ : (P Q : (s : 𝒮 Σ) → H↑) (s : 𝒮 Σ) → H↑
  (P ⊙ Q) s = P s ⊚ Q
\end{code}
%</tensor1>

\begin{code}
  _~>_ : ∀ {𝒞₀} (F G : 𝒞₀ → Set) → Set
  F ~> G = ∀ {c} → F c → G c
\end{code}

\begin{code}
  module _
    (P : (s : 𝒮 Σ) → H↑)
    (ν : ∀ {s} → V s ~> P s)
    (ς : ∀ {s} → (P ⊙ P) s ~> P s)
    where
\end{code}

%<*extension>
\begin{code}
    _♯
      : ∀ {Υ Δ Γ}
      → (f : ∀ {s} (x : V s (Υ , Δ)) → P s (Υ , Γ))
      → (∀ {s} (D : P s (Υ , Δ)) → P s (Υ , Γ))
    f ♯ = ς ∘ s↑ ∘ ⟨ id , ![ f ∘Π (_, refl) ] ⟩
\end{code}
%</extension>
