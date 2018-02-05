{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence
open import lib.Equivalence2
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
open import lib.types.Paths
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Unit

open import Other
open import NatColim
open import CommSigma.Code
open import CommSigma

module CommPaths where

-- Commutation of sequential colimits and path types

is-contr-seq : ∀ {i} → Sequence i → Type i
is-contr-seq A = (n : ℕ) → is-contr (fst A n)

postulate
  is-contr-seq-colim : ∀ {i} {A : Sequence i} → is-contr-seq A → is-contr (ℕColim A)

YDepSeqᴹ : ∀ {i} → CoindDepSeqᴹ {i}
YDepSeqᴹ = record
  { T = λ A → fst A O
  ; nx = λ { {A} x → snd A O x }
  ; E = λ { x y → x == y }
  ; e = λ { {A} x y p → ap (snd A O) p }
  }

module YDepSeqM {i} = CoindDepSeq (YDepSeqᴹ {i})

=→code : ∀ {i} {A : Sequence i} → (x : fst A O) → (y : ℕColim A) → ncin O x == y → code (YDepSeqM.coind-depseq {A = A} x) y
=→code {i} {A} x _ idp = ncin O idp

any-is-equiv-contr : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → is-contr A → is-contr B → is-equiv f
any-is-equiv-contr f a b = is-eq f (λ _ → contr-center a) (λ c → contr-has-all-paths {{b}} (f (contr-center a)) c) (contr-path a)

is-contr-seq-Y : ∀ {i} {A : Sequence i} x → is-contr-seq (SigmaSequence (YDepSeqM.coind-depseq {A = A} x))
is-contr-seq-Y x O = pathfrom-is-contr x
is-contr-seq-Y {A = A} x (S n) = is-contr-seq-Y {A = shift A} (snd A O x) n

=→code-is-e : ∀ {i} {A : Sequence i} → (x : fst A O) → (y : ℕColim A) → is-equiv (=→code x y)
=→code-is-e {i} {A} x = total-equiv-is-fiber-equiv (=→code x) (any-is-equiv-contr _ (pathfrom-is-contr (ncin O x)) (transport is-contr (ua ColimΣ≃ΣColim) (is-contr-seq-colim (is-contr-seq-Y x))))

=≃code : ∀ {i} {A : Sequence i} → (x : fst A O) → (y : ℕColim A)
     → (ncin O x == y) ≃ code (YDepSeqM.coind-depseq {A = A} x) y
=≃code x y = =→code x y , =→code-is-e x y
