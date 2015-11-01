\begin{code}
{-# OPTIONS --type-in-type #-}

module Code where
\end{code}

\begin{code}
infix 0 _≡_
infix 0 ∐
infixr 1 ⨛
infixr 1 ⨜
infixl 1 _[_]
infixr 0 _,_
infixr 1 _⊗_
infixr 1 _∘_
infixr 1 _∘Π_
infixr 2 ![_]
\end{code}

\begin{code}
data _≡_ {A} x : A → Set where
  refl : x ≡ x

_∘≡_ : {A : Set} {x y z : A} (p : y ≡ z) (q : x ≡ y) → x ≡ z
refl ∘≡ q = q
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
syntax ∐ A (λ x → B) = ∐[ A ∋ x ] B
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
⨜ : {I : Set} → (I → Set) → Set
⨜ {I = I} P = ∀ i → P i
\end{code}

\begin{code}
syntax ⨜ {I = I} (λ i → P) = ⨜[ I ∋ i ] P
\end{code}

\begin{code}
record ⨛ {I : Set} (P : I → Set) : Set where
  constructor s↑
  field
    {π∫₀} : I
    π∫₁ : P π∫₀
\end{code}
\begin{code}
open ⨛ public
\end{code}

\begin{code}
syntax ⨛ {I = I} (λ i → P) = ⨛[ I ∋ i ] P
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
LanG 𝒟[_,_] _⟦⊗⟧_ J F d = ⨛[ _ ∋ c ] F c ⟦⊗⟧ 𝒟[ J c , d ]
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
RanG 𝒟[_,_] _⟦⋔⟧_ J F d = ⨜[ _ ∋ c ] 𝒟[ d , J c ] ⟦⋔⟧ F c
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

%<*nat>
\begin{code}
_+ℕ_ : Nat → Nat → Nat
ze +ℕ n = n
su m +ℕ n = su (m +ℕ n)
\end{code}
%</nat>

%<*fin>
\begin{code}
data Fin : (n : Nat) → Set where
  ze : ∀ {n} → Fin (su n)
  su : ∀ {n} → Fin n → Fin (su n)

fin-to-nat : ∀ {n} → Fin n → Nat
fin-to-nat ze = ze
fin-to-nat (su x) = su (fin-to-nat x)
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
Ctx 𝒮 = ∐[ Nat ∋ n ] (Var n → 𝒮)
\end{code}
%</ctx>

%<*ctxdom>
\begin{code}
∣_∣ : ∀ {𝒮} (Γ : Ctx 𝒮) → Nat
∣_∣ = fst
\end{code}
%</ctxdom>

%<*ctxidx>
\begin{code}
_[_] : ∀ {𝒮} (Γ : Ctx 𝒮) → ((x : Var ∣ Γ ∣) → 𝒮)
_[_] = snd
\end{code}
%</ctxidx>

%<*sctx>
\begin{code}
SCtx : (𝒮 : Set) → Set
SCtx 𝒮 = ∐[ Nat ∋ n ] (Sym n → 𝒮)
\end{code}
%</sctx>

%<*ctxext>
\begin{code}

fin+-inl : ∀ {m n} → Fin m → Fin (m +ℕ n)
fin+-inl {ze} ()
fin+-inl {su m} ze = ze
fin+-inl {su m} (su i) = su (fin+-inl i)

fin+-inr : ∀ {m n} → Fin n → Fin (m +ℕ n)
fin+-inr {ze} i = i
fin+-inr {su m} i = su (fin+-inr {m} i)

data Fin+Split (m n : Nat) : Fin (m +ℕ n) → Set where
  fin+-left : (i : Fin m) → Fin+Split m n (fin+-inl {m} {n} i)
  fin+-right : (j : Fin n) → Fin+Split m n (fin+-inr {m} {n} j)

fin+-split : (m n : Nat) → (i : Fin (m +ℕ n)) → Fin+Split m n i
fin+-split ze n i = fin+-right i
fin+-split (su m) n ze = fin+-left ze
fin+-split (su m) n (su i) with fin+-split m n i
fin+-split (su m) n (su ._) | fin+-left i = fin+-left (su i)
fin+-split (su m) n (su ._) | fin+-right j = fin+-right j

_,,_ : ∀ {𝒮 : Set} (Γ Δ : Ctx 𝒮) → Ctx 𝒮
(m , Γ) ,, (n , Δ) = m +ℕ n , aux
  where
    aux : (i : Fin (m +ℕ n)) → _
    aux i with fin+-split m n i
    aux .(fin+-inl i) | fin+-left i = Γ i
    aux .(fin+-inr {m} j) | fin+-right j = Δ j
\end{code}
%</ctxext>

%<*elem>
\begin{code}
_∋⟨_,_⟩ : ∀ {𝒮} (Γ : Ctx 𝒮) (x : Var ∣ Γ ∣) (s : 𝒮) → Set
Γ ∋⟨ x , s ⟩ = Γ [ x ] ≡ s
\end{code}
%</elem>

%<*valence>
\begin{code}
𝒱 : Set → Set
𝒱 𝒮 = SCtx 𝒮 ⊗ Ctx 𝒮 ⊗ 𝒮
\end{code}
%</valence>

%<*arity>
\begin{code}
𝒜 : Set → Set
𝒜 𝒮 = Ctx (𝒱 𝒮) ⊗ 𝒮
\end{code}
%</arity>

%<*mctx>
\begin{code}
MCtx : (𝒮 : Set) → Set
MCtx 𝒮 = Ctx (𝒱 𝒮)
\end{code}
%</mctx>

%<*sign>
\begin{code}
record Sign : Set₁ where
  field
    𝒮 : Set
    𝒪 : SCtx 𝒮 ⊗ 𝒜 𝒮 → Set
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

  pattern _∥_ Υ Γ = (Υ , Γ)
\end{code}
%</H>

%<*HHat>
\begin{code}
  H↑ : Set
  H↑ = H → Set
\end{code}
%</HHat>

%<*yoneda>
\begin{code}
  _↪_ : {A : Set} → Ctx A → Ctx A → Set
  (m , Γ) ↪ (n , Δ) = ∐[ (Fin m → Fin n) ∋ ρ ] (∀ i → Γ i ≡ Δ (ρ i))

  yo : H → H↑
  yo (Υ ∥ Γ) = λ { (Υ′ ∥ Δ) → (Υ ↪ Υ′) ⊗ (Γ ↪ Δ) }
\end{code}
%</yoneda>

\begin{code}
  _~>_ : ∀ {𝒞₀} (F G : 𝒞₀ → Set) → Set
  F ~> G = ∀ {c} → F c → G c

  infixr 2 _~>_
\end{code}

%<*exponential>
\begin{code}
  _⊗↑_ : H↑ → H↑ → H↑
  (A ⊗↑ B) h = A h ⊗ B h
  infixr 1 _⊗↑_

  _^_ : H↑ → H↑ → H↑
  (B ^ A) h = (yo h ⊗↑ A) ~> B
\end{code}
%</exponential>

%<*V>
\begin{code}
  V : (s : 𝒮 Σ) → H↑
  V s (Υ ∥ Γ) = ∐[ Var ∣ Γ ∣ ∋ x ] Γ ∋⟨ x , s ⟩
\end{code}
%</V>

%<*S>
\begin{code}
  S : (s : 𝒮 Σ) → H↑
  S s (Υ ∥ Γ) = ∐[ Sym ∣ Υ ∣ ∋ x ] Υ ∋⟨ x , s ⟩
\end{code}
%</S>

\begin{code}
  _⊢_ : (Υ∥Γ : H) (s : 𝒮 Σ) → Set
  (Υ ∥ Γ) ⊢ s = Σ ∣ Υ ∥ Γ ⊢ s
\end{code}

%<*tensor0>
\begin{code}
  _⊚_ : (A : H↑) (P : (s : 𝒮 Σ) → H↑) → H↑
  (A ⊚ P) h =
    ⨛[ H ∋ h′ ] let Υ′ ∥ Δ = h′ in
      A (Υ′ ∥ Δ)
        ⊗ (⨜[ Sym ∣ Υ′ ∣ ∋ u ] S (Υ′ [ u ]) h)
        ⊗ (⨜[ Var ∣ Δ ∣ ∋ x ] P (Δ [ x ]) h)
\end{code}
%</tensor0>

%<*tensor1>
\begin{code}
  _⊙_ : (P Q : (s : 𝒮 Σ) → H↑) (s : 𝒮 Σ) → H↑
  (P ⊙ Q) s = P s ⊚ Q
\end{code}
%</tensor1>

%<*endofunctor>
\begin{code}
  𝔉 : (X : 𝒮 Σ → H↑) → 𝒮 Σ → H↑
  𝔉 X s (Υ ∥ Γ) =
    ∐[ 𝒜 (𝒮 Σ) ∋ a ] let vs , s′ = a in (s′ ≡ s) ⊗
    (∐[ 𝒪 Σ (Υ , a) ∋ ϑ ]
     ⨜[ Fin ∣ vs ∣ ∋ i ] let psᵢ , qsᵢ , sᵢ = vs [ i ] in
        X sᵢ (Υ ,, psᵢ , Γ ,, qsᵢ))
\end{code}
%</endofunctor>

\begin{code}
  module _
    (P : (s : 𝒮 Σ) → H↑)
    (ν : ∀ {s} → V s ~> P s)
    (ς : ∀ {s} → (P ⊙ P) s ~> P s)
    (α : ∀ {s} → 𝔉 P s ~> P s)
    where

    S^[_] : SCtx (𝒮 Σ) → H↑
    (S^[ Υ ]) h = ⨜[ Sym ∣ Υ ∣ ∋ u ] S (Υ [ u ]) h

    _^[_] : (X : 𝒮 Σ → H↑) → Ctx (𝒮 Σ) → H↑
    (X ^[ Γ ]) h = ⨜[ Var ∣ Γ ∣ ∋ x ] X (Γ [ x ]) h

    ς⟨_,_⟩ : ∀ {s} (Υ : SCtx (𝒮 Σ)) (Γ : Ctx (𝒮 Σ)) → ((P s ^ yo (Υ ∥ Γ)) ⊗↑ S^[ Υ ] ⊗↑ P ^[ Γ ]) ~> P s
    ς⟨ Υ , Γ ⟩ = {!!}
\end{code}

%<*extension>
\begin{code}
    _♯
      : ∀ {Υ Δ Γ}
      → (f : ∀ {s} (x : V s (Υ ∥ Δ)) → P s (Υ ∥ Γ))
      → (∀ {s} (D : P s (Υ ∥ Δ))
      → P s (Υ ∥ Γ))
    f ♯ = ς ∘ s↑ ∘ ⟨ id , ![ (_, refl) , f ∘Π (_, refl) ] ⟩

    ⟨_,_⟩♯
      : ∀ {Υ Υ′ Δ Γ}
      → (ρ : ∀ {s} (x : S s (Υ′ ∥ Δ)) → S s (Υ ∥ Γ))
      → (f : ∀ {s} (x : V s (Υ′ ∥ Δ)) → P s (Υ ∥ Γ))
      → (∀ {s} (D : P s (Υ′ ∥ Δ))
      → P s (Υ ∥ Γ))
    ⟨ ρ , f ⟩♯ = ς ∘ s↑ ∘ ⟨ id , ![ ρ ∘Π (_, refl) , f ∘Π (_, refl) ] ⟩
\end{code}
%</extension>

%<*interpretation>
\begin{code}
    ⟦_>_∥_⟧ : MCtx (𝒮 Σ) → SCtx (𝒮 Σ) → Ctx (𝒮 Σ) → H↑
    ⟦ Ω > Υ ∥ Γ ⟧ =
      (λ h → ⨜[ Fin ∣ Ω ∣ ∋ m ] let psₘ , qsₘ , sₘ = Ω [ m ] in (P sₘ ^ yo (psₘ ∥ qsₘ)) h)
        ⊗↑ S^[ Υ ]
        ⊗↑ V ^[ Γ ]
\end{code}
%</interpretation>

\begin{code}
    data _▹_∥_⊢_ (Ω : MCtx (𝒮 Σ)) (Υ : SCtx (𝒮 Σ)) (Γ : Ctx (𝒮 Σ) ) : 𝒮 Σ → Set where
      var :
        (x : Var ∣ Γ ∣)
          → Ω ▹ Υ ∥ Γ ⊢ (Γ [ x ])
      metavar :
        (m : Var ∣ Ω ∣)
        (let ps , qs , s = Ω [ m ])
          → (∀ i → ∐[ Sym ∣ Υ ∣ ∋ u ] Υ ∋⟨ u , ps [ i ] ⟩)
          → (∀ i → Ω ▹ Υ ∥ Γ ⊢ (qs [ i ]))
          → Ω ▹ Υ ∥ Γ ⊢ s
      app :
        {a : 𝒜 (𝒮 Σ)}
        (let vs , s = a)
        (ϑ : 𝒪 Σ (Υ , a))
          → (∀ i → let psᵢ , qsᵢ , sᵢ = vs [ i ] in Ω ▹ Υ ,, psᵢ ∥ Γ ,, qsᵢ ⊢ sᵢ)
          → Ω ▹ Υ ∥ Γ ⊢ s

    ⟦_⟧_ : ∀ {Ω Υ Γ s} → Ω ▹ Υ ∥ Γ ⊢ s → ⟦ Ω > Υ ∥ Γ ⟧ ~> P s
    ⟦ var x ⟧ (_ , _ , ⟦Γ⟧) = ν (⟦Γ⟧ x)
    ⟦_⟧_ {Ω = Ω} {Υ = Υ} {Γ = Γ} {s = _} (metavar m us Ms) {Υ′ ∥ Δ} ρ =
     let
       ps , qs , s = Ω [ m ]
       ⟦Ω⟧ , ⟦Υ⟧ , ⟦Γ⟧ = ρ
       welp : S^[ Υ ] (Υ′ ∥ Δ)
       welp = ⟦Υ⟧
     in
       ς⟨ ps , qs ⟩
         ( ⟦Ω⟧ m
         , (λ i →
             let
               u , u∈Υ = us i
               u′ , u′∈Υ′ = ⟦Υ⟧ u
             in
               u′ , u∈Υ ∘≡ u′∈Υ′)
         , (λ i → ⟦ Ms i ⟧ ρ)
         )
    ⟦ app ϑ Ms ⟧ ρ = {!!}
\end{code}
