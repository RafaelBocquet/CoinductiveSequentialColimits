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

module CommSigma.Code where

-- Definition of code

module _ {i} where
  module ℕCCode = ℕColimRecAlt {i} DepSequence depShift (λ A _ → Type i)
    (λ { (D , d) B x → ℕColim (ApplySequence B x) })
    (λ { (D , d) B r → r })
    (λ { (D , d) B x → ua nc-lift⁻¹-e })
  code : ∀ {A : Sequence i} → DepSequence A → ℕColim A → Type i
  code {A} B x = ℕCCode.f A B x

  code-lift-β : ∀ {A : Sequence i} {B : DepSequence A} x → code B (nc-lift x) == code (depShift B) x
  code-lift-β {A} {B} x = ℕCCode.nc-lift-β A B x

  code-glue-β : ∀ {A : Sequence i} {B : DepSequence A} x → ap (code B) (ncglue O x) == ua nc-lift⁻¹-e
  code-glue-β {A} {B} x = ℕCCode.ncglue-β A B x

  -- Some paths over ap (code B) (ncglue O x) are defined here
  abstract
    code-glue-path : ∀ {A} {B : DepSequence A} x y → PathOver (code B) (ncglue O x) (nc-lift y) y
    code-glue-path {A}{B} x y = ↓-ap-out (λ x → x) (code B) (ncglue O x)
                                (↓-idf-in (ap (code B) (ncglue O x))
                                (ap (λ z → coe z (nc-lift y)) (code-glue-β x) ∙ coe-β nc-lift⁻¹-e (nc-lift y) ∙ <–-inv-r nc-lift⁻¹-e y))

  code-glue-path' : ∀ {A} {B : DepSequence A} x y → PathOver (code B) (ncglue O x) y (nc-lift⁻¹ y)
  code-glue-path' {A}{B} x y = ! (nc-lift⁻¹-lift y) ◃ code-glue-path x (nc-lift⁻¹ y)

  abstract
    code-glue-path'-ncin : ∀ {A} {B : DepSequence A} x y → SquareOver (code B) (tr-square (ncglue {i}{A} O x))
                                                           idp (code-glue-path' x (ncin O y)) (ncglue O y) (!ᵈ (code-glue-path x (ncin O (snd B O x y))))
    code-glue-path'-ncin {A}{B} x y = ap (λ z → z ◃ code-glue-path x (ncin O (snd B O x y))) (!-! (ncglue O y)) ∙v↓⊡
                                      (vid-square {p = ncglue O y} ⊡↓h tr-squareover (code-glue-path {A}{B} x (ncin O (snd B O x y))))
                                      ↓⊡v∙ ∙-unit-r (ncglue O y)
