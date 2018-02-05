{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence
open import lib.Univalence
open import lib.PathGroupoid
open import lib.NConnected
open import lib.NType2
open import lib.cubical.Square
open import lib.cubical.SquareOver
open import lib.types.Lift
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Unit

module Other where

vid-squareover : ∀ {i j} {A : Type i} {B : A → Type j}
               {a₀₀ a₁₀ : A} {p : a₀₀ == a₁₀}
               {b₀₀ : B a₀₀} {b₁₀ : B a₁₀} {q : b₀₀ == b₁₀ [ B ↓ p ]}
               → SquareOver B (vid-square {p = p}) idp q q idp
vid-squareover {p = idp} {q = idp} = ids

_⊡↓h_ : ∀ {i j} {A : Type i} {B : A → Type j} {a₀₀ a₀₁ a₁₀ a₁₁ a₂₀ a₂₁ : A}
      {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
      {q₋₀ : a₁₀ == a₂₀} {q₋₁ : a₁₁ == a₂₁} {q₂₋ : a₂₀ == a₂₁}
      {sq₀ : Square p₀₋ p₋₀ p₋₁ p₁₋}
      {sq₁ : Square p₁₋ q₋₀ q₋₁ q₂₋}
      {b₀₀ b₀₁ b₁₀ b₁₁ b₂₀ b₂₁}
      {p₀₋' : b₀₀ == b₀₁ [ B ↓ p₀₋ ]} {p₋₀' : b₀₀ == b₁₀ [ B ↓ p₋₀ ]} {p₋₁' : b₀₁ == b₁₁ [ B ↓ p₋₁ ]} {p₁₋' : b₁₀ == b₁₁ [ B ↓ p₁₋ ]}
      {q₋₀' : b₁₀ == b₂₀ [ B ↓ q₋₀ ]} {q₋₁' : b₁₁ == b₂₁ [ B ↓ q₋₁ ]} {q₂₋' : b₂₀ == b₂₁ [ B ↓ q₂₋ ]}
      → SquareOver B sq₀ p₀₋' p₋₀' p₋₁' p₁₋'
      → SquareOver B sq₁ p₁₋' q₋₀' q₋₁' q₂₋'
      → SquareOver B (sq₀ ⊡h sq₁) p₀₋' (p₋₀' ∙ᵈ q₋₀') (p₋₁' ∙ᵈ q₋₁') q₂₋'
_⊡↓h_ {sq₀ = ids} {sq₁ = ids} = _⊡h_

module _ {i j} {A : Type i} {B : A → Type j} where
  tr-squareover : {a₀ a₁ : A} {p : a₀ == a₁}
                  {b₀ : B a₀} {b₁ : B a₁} (q : b₀ == b₁ [ B ↓ p ])
                  → SquareOver B (tr-square p) idp q idp (!ᵈ q)
  tr-squareover {p = idp} = tr-square

pair==-from-squareover : ∀ {i j} {A : Type i} {B : A → Type j} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
                       {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
                       (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
                       {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
                       {q₀₋ : b₀₀ == b₀₁ [ B ↓ p₀₋ ]} {q₋₀ : b₀₀ == b₁₀ [ B ↓ p₋₀ ]}
                       {q₋₁ : b₀₁ == b₁₁ [ B ↓ p₋₁ ]} {q₁₋ : b₁₀ == b₁₁ [ B ↓ p₁₋ ]}
                       (sqo : SquareOver B sq q₀₋ q₋₀ q₋₁ q₁₋)
                       → Square (pair= p₀₋ q₀₋) (pair= p₋₀ q₋₀) (pair= p₋₁ q₋₁) (pair= p₁₋ q₁₋)
pair==-from-squareover ids ids = ids

module _ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k} where
  ↓-Π-cst-app-β : {x x' : A} {p : x == x'}
    {u : (b : B) → C x b} {u' : (b : B) → C x' b}
    (f : (b : B) → u b == u' b [ (λ x → C x b) ↓ p ])
    (y : _)
    → ↓-Π-cst-app-out (↓-Π-cst-app-in f) y == f y
  ↓-Π-cst-app-β {p = idp} f y = app=-β f y

apd-∘''' : ∀ {i j k}{A : Type i}{B : Type j}{C : A → B → Type k}
      (f : (x : A) → (y : B) → C x y)
      {x x' : A} (p : x == x') (y : B)
      → apd (λ x → f x y) p == ↓-Π-cst-app-out (apd f p) y
apd-∘''' f idp y = idp

pathoverto-is-contr : ∀ {i} {A : Type i} (B : A → Type i) {a₀ a₁ : A} (p : a₀ == a₁) (b₁ : B a₁)
                    → is-contr (Σ (B a₀) (λ b₀ → b₀ == b₁ [ B ↓ p ]))
pathoverto-is-contr B p b₁ = transport is-contr (! (ua (Σ-emap-r (λ b₀ → to-transp!-equiv B p)))) (pathto-is-contr (transport! B p b₁))

transport!-= : ∀ {i}{j} {A : Type i}{B : Type j}
               (f : A → B) (g : A → B)
               {x x' : A} (p : x == x')
               (q : f x' == g x')
               (l : f x == f x') (l' : ap f p == l)
               (r : g x == g x') (r' : ap g p == r)
               → transport! (λ z → f z == g z) p q == l ∙ q ∙ ! r
transport!-= f g idp q _ idp _ idp = ! (∙-unit-r q)

↓-ap-in= : ∀ {i j k} {A : Type i} {B : Type j} (C : (b : B) → Type k)
  (f : A → B) {x y : A} (p : x == y)
  {q : f x == f y} (r : ap f p == q)
  {u : C (f x)} {v : C (f y)}
  → u == v [ (λ z → C (f z)) ↓ p ]
  → u == v [ C ↓ q ]
↓-ap-in= C f idp idp idp = idp

↓-ap-out=-β : ∀ {i j k} {A : Type i} {B : Type j} (C : (b : B) → Type k)
  (f : A → B) {x y : A} (p : x == y)
  {q : f x == f y} (r : ap f p == q)
  {u : C (f x)} {v : C (f y)}
  (z : u == v [ (λ z → C (f z)) ↓ p ])
  → ↓-ap-out= C f p r (↓-ap-in= C f p r z) == z
↓-ap-out=-β C f idp idp idp = idp
