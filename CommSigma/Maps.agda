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

open import NatColim
open import Other
open import CommSigma.Code

module CommSigma.Maps where

ColimΣ→ΣColimᴹ : ∀{i} → ℕColimRecCoindᴹ {_}{_}{i} (SigmaSequenceᴹ {i})
ColimΣ→ΣColimᴹ {i} = record { P = λ { (A , B) → Σ (ℕColim A) (code B) }
                            ; Pi = λ { (A , B) (x , y) → ncin O x , ncin O y }
                            ; Pl = λ { (A , B) (r₁ , r₂) → nc-lift r₁ , coe! (code-lift-β {_}{A}{B} r₁) r₂ }
                            ; Pg = λ { (A , B) (x , y) → pair= (ncglue O x) (code-glue-path' {i} {A} {B} x (ncin O y)) } }

module ColimΣ→ΣColimM {i} = ℕColimRecCoind {i} _ ColimΣ→ΣColimᴹ

ColimΣ→ΣColim : ∀ {i} {A : Sequence i} {B : DepSequence A} → ℕColim (SigmaSequence B) → Σ (ℕColim A) (code B)
ColimΣ→ΣColim {i}{A}{B} x = ColimΣ→ΣColimM.f (A , B) x

ΣColim→ColimΣiᴹ : ∀{i} → ℕColimRecCoindᴹ {_}{_}{i} (ApplySequenceᴹ {i})
ΣColim→ColimΣiᴹ {i} = record
  { P = λ { (A , B , x) → ℕColim (SigmaSequence B) }
  ; Pi = λ { (A , B , x) y → ncin O (x , y) }
  ; Pl = λ { (A , B , x) r → nc-lift r }
  ; Pg = λ { (A , B , x) y → ncglue O (x , y) } }

module ΣColim→ColimΣiM {i} = ℕColimRecCoind {i} _ ΣColim→ColimΣiᴹ

ΣColim→ColimΣi : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) (y : ℕColim (ApplySequence B x)) → ℕColim (SigmaSequence B)
ΣColim→ColimΣi {i}{A}{B} x y = ΣColim→ColimΣiM.f (A , B , x) y

postulate
  cheat : ∀{i}{A : Type i} → A

ΣColim→ColimΣgf : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) {y} {y'} (q : y == y' [ code B ↓ ncglue O x ]) →
                  ΣColim→ColimΣi {i}{A}{B} x y == nc-lift (ΣColim→ColimΣi (snd A O x) y')
ΣColim→ColimΣgf {i}{A}{B} x {y}{y'}q = transport (λ y → ΣColim→ColimΣi x (fst y) == nc-lift (ΣColim→ColimΣi (snd A O x) y'))
                                                 (contr-has-all-paths {{pathoverto-is-contr (code B) (ncglue O x) y'}} (nc-lift y' , code-glue-path x y') (y , q))
                                                 (ΣColim→ColimΣiM.nc-lift-β (A , B , x) y')

ΣColim→ColimΣgf' : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) y →
                   ΣColim→ColimΣgf {i}{A}{B} x (code-glue-path x y) == ΣColim→ColimΣiM.nc-lift-β (A , B , x) y
ΣColim→ColimΣgf' {i}{A}{B} x y = ap (λ z → transport (λ y' → ΣColim→ColimΣi x (fst y') == nc-lift (ΣColim→ColimΣi (snd A O x) y)) z (ΣColim→ColimΣiM.nc-lift-β (A , B , x) y))
                                    (prop-has-all-paths {{has-level-apply (contr-is-set (pathoverto-is-contr (code B) (ncglue O x) y)) (nc-lift y , code-glue-path x y) (nc-lift y , code-glue-path x y)}}
                                      (contr-has-all-paths {{pathoverto-is-contr (code B) (ncglue O x) y}} (nc-lift y , code-glue-path x y) (nc-lift y , code-glue-path x y))
                                      idp)

ΣColim→ColimΣg : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) →
               ΣColim→ColimΣi {i}{A}{B} x == (λ y → nc-lift (ΣColim→ColimΣi (snd A O x) y)) [ (λ X → code B X → ℕColim (SigmaSequence B)) ↓ ncglue O x ]
ΣColim→ColimΣg {i}{A}{B} x = ↓-app→cst-in (ΣColim→ColimΣgf x)

module ΣColim→ColimΣM {i} = ℕColimElimAlt DepSequence depShift (λ (A : Sequence i) B x → code B x → ℕColim (SigmaSequence B))
               (λ A B x y → ΣColim→ColimΣi x y)
               (λ A B x r y → nc-lift (r (coe (code-lift-β {_}{A}{B} x) y)))
               (λ A B x → ΣColim→ColimΣg x)

ΣColim→ColimΣ : ∀ {i} {A : Sequence i} {B : DepSequence A} → Σ (ℕColim A) (code B) → ℕColim (SigmaSequence B)
ΣColim→ColimΣ {i} {A} {B} (x , y) = ΣColim→ColimΣM.f A B x y
