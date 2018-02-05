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
open import CommSigma.Maps
open import CommSigma.Paths

module CommSigma where

-- Commutation of sequential colimits and sigma types

ColimΣ≃ΣColim : ∀ {i}{A : Sequence i}{B : DepSequence A} → ℕColim (SigmaSequence B) ≃ Σ (ℕColim A) (code B)
ColimΣ≃ΣColim = ColimΣ→ΣColim , is-eq ColimΣ→ΣColim ΣColim→ColimΣ ΣColim→←ColimΣ ColimΣ→←ΣColim
