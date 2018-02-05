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

open import Other
open import NatColim
open import CommSigma.Code
open import CommSigma.Maps

module CommSigma.Paths where

ΣColim→ColimΣ-lift-coe : ∀ {i} {A : Sequence i} {B : DepSequence A} (q : Σ (ℕColim (shift A)) (code (depShift B))) →
                         ΣColim→ColimΣ (nc-lift (fst q) , coe! (code-lift-β {_}{A}{B} (fst q)) (snd q)) == nc-lift (ΣColim→ColimΣ q)
ΣColim→ColimΣ-lift-coe {i}{A}{B} (q₁ , q₂) = app= (ΣColim→ColimΣM.nc-lift-β A B q₁) (coe! (code-lift-β {_}{A}{B} q₁) q₂) ∙
                                             ap (λ y → nc-lift (ΣColim→ColimΣ (q₁ , y))) (coe!-inv-r (code-lift-β {_}{A}{B} q₁) q₂)

ColimΣ→←ΣColimᴹl : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : ℕColim (SigmaSequence (depShift B)))
                   (r : ΣColim→ColimΣ (ColimΣ→ΣColim x) == x) → ΣColim→ColimΣ (ColimΣ→ΣColim (nc-lift {i} {SigmaSequence B} x)) == nc-lift {i} {SigmaSequence B} x
ColimΣ→←ΣColimᴹl {i}{A}{B} x r = (ap ΣColim→ColimΣ (ColimΣ→ΣColimM.nc-lift-β (A , B) x) ∙ ΣColim→ColimΣ-lift-coe (ColimΣ→ΣColim x)) ∙' ap nc-lift r

abstract
  ColimΣ→←ΣColimᴹg' : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) y →
                      ap ΣColim→ColimΣ (pair= (ncglue O x) (code-glue-path {_}{_}{B} x y)) == ΣColim→ColimΣiM.nc-lift-β (A , B , x) y
  ColimΣ→←ΣColimᴹg' {i}{A}{B} x y = ap ΣColim→ColimΣ (pair= (ncglue O x) (code-glue-path {_}{_}{B} x y))
                                    =⟨ split-ap2 ΣColim→ColimΣ (ncglue O x) (code-glue-path {_}{_}{B} x y) ⟩
                                    ↓-app→cst-out (apd (curry ΣColim→ColimΣ) (ncglue O x)) (code-glue-path {_}{_}{B} x y)
                                    =⟨ ap (λ r → ↓-app→cst-out r (code-glue-path {_} {_} {B} x y)) (ΣColim→ColimΣM.ncglue-β A B x) ⟩
                                    ↓-app→cst-out (ΣColim→ColimΣg x) (code-glue-path {_}{_}{B} x y)
                                    =⟨ ↓-app→cst-β (ΣColim→ColimΣgf x) (code-glue-path {_}{_}{B} x y) ⟩
                                    ΣColim→ColimΣgf x (code-glue-path {_}{_}{B} x y)
                                    =⟨ ΣColim→ColimΣgf' x y ⟩
                                    ΣColim→ColimΣiM.nc-lift-β (A , B , x) y =∎

abstract
  ColimΣ→←ΣColimᴹg : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) (y : fst B O x) →
                     idp == idp [ (λ z → ΣColim→ColimΣ (ColimΣ→ΣColim {i}{A}{B} z) == z) ↓ ncglue O (x , y) ]
  ColimΣ→←ΣColimᴹg {i}{A}{B} x y = ↓-='-from-square (vert-degen-square
                                   (ap (λ z → ΣColim→ColimΣ (ColimΣ→ΣColim {i}{A}{B} z)) (ncglue O (x , y))
                                   =⟨ ap-∘ ΣColim→ColimΣ ColimΣ→ΣColim (ncglue O (x , y)) ⟩
                                   ap ΣColim→ColimΣ (ap ColimΣ→ΣColim (ncglue O (x , y)))
                                   =⟨ ap (ap ΣColim→ColimΣ) (ColimΣ→ΣColimM.ncglue-β (A , B) (x , y)) ⟩
                                   ap ΣColim→ColimΣ (pair= (ncglue O x) (code-glue-path' {i} {A} {B} x (ncin O y)))
                                   =⟨ ap (ap ΣColim→ColimΣ) (! (Σ-∙ (! (! (ncglue O y))) (code-glue-path {_} {_} {B} x (ncin O (snd B O x y))))) ⟩
                                   ap ΣColim→ColimΣ (pair= idp (! (! (ncglue O y))) ∙ pair= (ncglue O x) (code-glue-path {_}{_}{B} x (ncin O (snd B O x y))))
                                   =⟨ ap-∙ ΣColim→ColimΣ (pair= idp (! (! (ncglue O y)))) (pair= (ncglue O x) (code-glue-path {_}{_}{B} x (ncin O (snd B O x y)))) ⟩
                                   ap ΣColim→ColimΣ (pair= (idp {a = ncin O x}) (! (! (ncglue {i}{ApplySequence B x} O y)))) ∙
                                   ap ΣColim→ColimΣ (pair= (ncglue O x) (code-glue-path {_}{_}{B} x (ncin O (snd B O x y))))
                                   =⟨ (ap ΣColim→ColimΣ (pair= (idp {a = ncin O x}) (! (! (ncglue O y)))) ∙ₗ ColimΣ→←ΣColimᴹg' x (ncin O (snd B O x y))) ∙ ∙-unit-r _ ⟩
                                   ap ΣColim→ColimΣ (pair= (idp {a = ncin O x}) (! (! (ncglue O y))))
                                   =⟨ ap (λ z → ap ΣColim→ColimΣ (pair= (idp {a = ncin O x}) z)) (!-! (ncglue O y)) ⟩
                                   ap ΣColim→ColimΣ (pair= (idp {a = ncin O x}) (ncglue O y))
                                   =⟨ ∘-ap ΣColim→ColimΣ (_,_ (ncin O x)) (ncglue O y) ⟩
                                   ap (λ z → ΣColim→ColimΣ {_}{A}{B} (ncin O x , z)) (ncglue O y)
                                   =⟨ ΣColim→ColimΣiM.ncglue-β (A , B , x) y ⟩
                                   ncglue O (x , y)
                                   =⟨ ! (ap-idf (ncglue O (x , y))) ⟩
                                   ap (λ z → z) (ncglue O (x , y)) =∎ ))

ColimΣ→←ΣColimᴹ : ∀{i} → ℕColimElimCoindᴹ {_}{_}{i} (SigmaSequenceᴹ {i})
ColimΣ→←ΣColimᴹ {i} = record { P = λ { (A , B) x → ΣColim→ColimΣ (ColimΣ→ΣColim x) == x }
                             ; Pi = λ { (A , B) (x , y) → idp }
                             ; Pl = λ { (A , B) x r → ColimΣ→←ΣColimᴹl x r }
                             ; Pg = λ { (A , B) (x , y) → ColimΣ→←ΣColimᴹg x y } }

ColimΣ→←ΣColim : ∀ {i} {A : Sequence i} {B : DepSequence A} → (x : ℕColim (SigmaSequence B)) → ΣColim→ColimΣ (ColimΣ→ΣColim x) == x
ColimΣ→←ΣColim {i}{A}{B} x = ℕColimElimCoind.f SigmaSequenceᴹ ColimΣ→←ΣColimᴹ (A , B) x

ΣColim→←ColimΣiᴹl' : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) y (q : Σ (ℕColim (shift A)) (code (depShift B))) (r : q == (ncin O (snd A O x) , y)) →
                     idf (Σ (ℕColim A) (code B)) (nc-lift (fst q) , coe! (code-lift-β {_}{A}{B} (fst q)) (snd q)) == (ncin (S O) (snd A O x) , y)
ΣColim→←ColimΣiᴹl' {i}{A}{B} x y (q₁ , q₂) idp = idp

ΣColim→←ColimΣl' : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : ℕColim (shift A)) (y : code B (nc-lift x))
                   (q : Σ (ℕColim (shift A)) (code (depShift B)))
                   (r : q == (x , coe (code-lift-β {i}{A}{B} x) y)) →
                   idf (Σ (ℕColim A) (code B)) (nc-lift (fst q) , coe! (code-lift-β {_}{A}{B} (fst q)) (snd q)) == nc-lift x , y
ΣColim→←ColimΣl' {i} {A} {B} x y _ idp = pair= idp (coe!-inv-l (code-lift-β {i}{A}{B} x) y)

ΣColim→←ColimΣl'' : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) y
                    (q : Σ (ℕColim (shift A)) (code (depShift B)))
                    (r : q == (ncin O (snd A O x) , y)) →
                    ΣColim→←ColimΣl' (ncin O (snd A O x)) y q r == ΣColim→←ColimΣiᴹl' {i}{A}{B} x y q r
ΣColim→←ColimΣl'' {i} {A} {B} x y _ idp = idp




ΣColim→←ColimΣiᴹl₁ : ∀ {i} {A : Sequence i} {B : DepSequence A} x y (r : ColimΣ→ΣColim (ΣColim→ColimΣ (ncin O (snd A O x) , y)) == (ncin O (snd A O x) , y)) →
                     ColimΣ→ΣColim (ΣColim→ColimΣ {i}{A}{B} (ncin O x , nc-lift y)) == (ncin O x , nc-lift y)
ΣColim→←ColimΣiᴹl₁ {i}{A}{B} x y r = transport! (λ z → ColimΣ→ΣColim (ΣColim→ColimΣ z) == z)
                                                (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y))
                                                (ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y) ∙
                                                  ΣColim→←ColimΣiᴹl' {i}{A}{B} x y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) r)

ΣColim→←ColimΣiᴹl₂ : ∀ {i} {A : Sequence i} {B : DepSequence A} x y (r : ColimΣ→ΣColim (ΣColim→ColimΣ (ncin O (snd A O x) , y)) == (ncin O (snd A O x) , y)) →
                      ColimΣ→ΣColim (ΣColim→ColimΣ {i}{A}{B} (ncin O x , nc-lift y)) == (ncin O x , nc-lift y)
ΣColim→←ColimΣiᴹl₂ {i}{A}{B} x y r = ap ColimΣ→ΣColim (ΣColim→ColimΣiM.nc-lift-β (A , B , x) y) ∙
                                     (ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y) ∙
                                      ΣColim→←ColimΣiᴹl' {i}{A}{B} x y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) r) ∙
                                     ! (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y))

abstract
  ΣColim→←ColimΣiᴹl₁₂ : ∀ {i} {A : Sequence i} {B : DepSequence A} x y (r : ColimΣ→ΣColim (ΣColim→ColimΣ (ncin O (snd A O x) , y)) == (ncin O (snd A O x) , y)) →
                      ΣColim→←ColimΣiᴹl₁ x y r == ΣColim→←ColimΣiᴹl₂ {i}{A}{B} x y r
  ΣColim→←ColimΣiᴹl₁₂ {i}{A}{B} x y r =
    transport!-= (λ z → ColimΣ→ΣColim (ΣColim→ColimΣ z)) (λ z → z)
                 (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y))
                 (ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y) ∙
                   ΣColim→←ColimΣiᴹl' {i}{A}{B} x y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) r)
                 (ap ColimΣ→ΣColim (ΣColim→ColimΣiM.nc-lift-β (A , B , x) y))
                 (ap-∘ ColimΣ→ΣColim ΣColim→ColimΣ (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y)) ∙ ap (ap ColimΣ→ΣColim) (ColimΣ→←ΣColimᴹg' x y))
                 (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y))
                 (ap-idf (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y)))

ΣColim→←ColimΣiᴹ : ∀{i} → ℕColimElimCoindᴹ {_}{_}{i} (ApplySequenceᴹ {i})
ΣColim→←ColimΣiᴹ {i} = record
  { P = λ { (A , B , x) y → ColimΣ→ΣColim (ΣColim→ColimΣi x y) == (ncin O x , y) }
  ; Pi = λ { (A , B , x) y → idp }
  ; Pl = λ { (A , B , x) y r → ΣColim→←ColimΣiᴹl₂ x y r }
  ; Pg = λ { (A , B , x) y → let sq : Square idp
                                             (ap (λ y → ColimΣ→ΣColim (ΣColim→ColimΣi x y)) (ncglue O y))
                                             (ap (λ y → ncin O x , y) (ncglue O y))
                                             (! (pair= (ncglue O x) (code-glue-path {i}{A}{B} x (ncin O (snd B O x y)))))
                                 sq = (ap-∘ ColimΣ→ΣColim (ΣColim→ColimΣi x) (ncglue O y) ∙
                                       ap (ap ColimΣ→ΣColim) (ΣColim→ColimΣiM.ncglue-β (A , B , x) y) ∙
                                       ColimΣ→ΣColimM.ncglue-β (A , B) (x , y)) ∙v⊡
                                       (pair==-from-squareover (tr-square (ncglue O x)) (code-glue-path'-ncin x y))
                                       ⊡h∙ ! (Σ-! (code-glue-path x (ncin O (snd B O x y))))
                                       ⊡v∙ (! (ap-cst,id (code B) (ncglue O y)))
                             in ↓-='-from-square sq
           } }

module ΣColim→←ColimΣiM {i} = ℕColimElimCoind {i} _ ΣColim→←ColimΣiᴹ

ΣColim→←ColimΣl : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : ℕColim (shift A)) (y : code B (nc-lift x)) →
                  (r : idf (Σ (ℕColim (shift A)) (code (depShift B))) (ColimΣ→ΣColim (ΣColim→ColimΣ (x , coe (code-lift-β {i}{A}{B} x) y))) == (x , coe (code-lift-β {i}{A}{B} x) y)) →
                  ColimΣ→ΣColim (ΣColim→ColimΣ (nc-lift x , y)) == (nc-lift x , y)
ΣColim→←ColimΣl {i}{A}{B} x y r = ap ColimΣ→ΣColim (app= (ΣColim→ColimΣM.nc-lift-β A B x) y) ∙
                                  ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣ (x , coe (code-lift-β {i}{A}{B} x) y)) ∙
                                  ΣColim→←ColimΣl' x y (ColimΣ→ΣColim (ΣColim→ColimΣ (x , coe (code-lift-β {i}{A}{B} x) y))) r

abstract
  ΣColim→←ColimΣg' : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O)
                       (P : Σ (ℕColim A) (code B) → Type i)
                       (T : (y : code B (ncin O x)) → P (ncin O x , y))
                     → (λ y → T y)
                       ==
                       (λ y → transport P (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y)) (T (nc-lift {i} {ApplySequence B x} y)))
                       [ (λ x → (y : code B x) → P (x , y)) ↓ ncglue O x ]
  ΣColim→←ColimΣg' {i}{A}{B} x P T = ↓-Π-in (λ { {y} {y'} q →
                                                 from-transp P
                                                 (pair= (ncglue O x) q)
                                                 (ap (λ { (y , q) → transport P (pair= (ncglue O x) q) (T y) })
                                                                    (contr-has-all-paths {{pathoverto-is-contr (code B) (ncglue O x) y'}} (y , q) (nc-lift y' , code-glue-path x y'))) })

abstract
  ΣColim→←ColimΣg'' : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) (y : ℕColim (ApplySequence (depShift B) (snd A O x))) →
                        (ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y) ∙
                         ΣColim→←ColimΣl' {i}{A}{B} (ncin O (snd A O x)) y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) (ΣColim→←ColimΣiM.f (shift A , depShift B , snd A O x) y))
                        ==
                        transport (λ z → (ColimΣ→ΣColim (ΣColim→ColimΣ z)) == z)
                                  (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y))
                                  (ΣColim→←ColimΣiM.f (A , B , x) (nc-lift y))
  ΣColim→←ColimΣg'' {i}{A}{B} x y = (ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y) ∙
                                     ΣColim→←ColimΣl' {i}{A}{B} (ncin O (snd A O x)) y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) (ΣColim→←ColimΣiM.f (shift A , depShift B , snd A O x) y))
                                    =⟨ ap (λ p → ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y) ∙ p)
                                          (ΣColim→←ColimΣl'' x y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) (ΣColim→←ColimΣiM.f (shift A , depShift B , snd A O x) y)) ⟩
                                    (ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y) ∙
                                     ΣColim→←ColimΣiᴹl' {i}{A}{B} x y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) (ΣColim→←ColimΣiM.f (shift A , depShift B , snd A O x) y))
                                    =⟨ ! (coe!-inv-r (ap (λ z → (ColimΣ→ΣColim (ΣColim→ColimΣ z)) == z) (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y)))
                                                     (ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y) ∙
                                                      ΣColim→←ColimΣiᴹl' {i}{A}{B} x y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) (ΣColim→←ColimΣiM.f (shift A , depShift B , snd A O x) y))) ⟩
                                    (transport (λ z → (ColimΣ→ΣColim (ΣColim→ColimΣ z)) == z)
                                               (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y))
                                               (ΣColim→←ColimΣiᴹl₁ x y (ΣColim→←ColimΣiM.f (shift A , depShift B , snd A O x) y)))
                                    =⟨ ap (λ w → transport (λ z → (ColimΣ→ΣColim (ΣColim→ColimΣ z)) == z) (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y)) w)
                                          (! (ΣColim→←ColimΣiM.nc-lift-β (A , B , x) y ∙ ! (ΣColim→←ColimΣiᴹl₁₂ x y (ΣColim→←ColimΣiM.f (shift A , depShift B , snd A O x) y)))) ⟩
                                    (transport (λ z → (ColimΣ→ΣColim (ΣColim→ColimΣ z)) == z)
                                               (pair= (ncglue O x) (code-glue-path {i}{A}{B} x y))
                                               (ΣColim→←ColimΣiM.f (A , B , x) (nc-lift y)))
                                    =⟨ idp ⟩ idp


abstract
  ΣColim→←ColimΣg : ∀ {i} {A : Sequence i} {B : DepSequence A} (x : fst A O) →
                    (λ y → ΣColim→←ColimΣiM.f (A , B , x) y)
                    ==
                    (λ y → (ColimΣ→ΣColimM.nc-lift-β (A , B) (ΣColim→ColimΣi (snd A O x) y)) ∙
                           ΣColim→←ColimΣl' {i}{A}{B} (ncin O (snd A O x)) y (ColimΣ→ΣColim (ΣColim→ColimΣi (snd A O x) y)) (ΣColim→←ColimΣiM.f (shift A , depShift B , snd A O x) y))
                    [ (λ x → (y : code B x) → ColimΣ→ΣColim (ΣColim→ColimΣ {i}{A}{B} (x , y)) == (x , y)) ↓ ncglue O x ]
  ΣColim→←ColimΣg {i}{A}{B} x = ΣColim→←ColimΣg' x (λ z → ColimΣ→ΣColim (ΣColim→ColimΣ z) == z) (ΣColim→←ColimΣiM.f (A , B , x)) ▹ ! (λ= (ΣColim→←ColimΣg'' x))

module ΣColim→←ColimΣM {i} = ℕColimElimAlt DepSequence depShift (λ (A : Sequence i) B x → (y : code B x) → ColimΣ→ΣColim (ΣColim→ColimΣ (x , y)) == (x , y))
  (λ { A B x y → ΣColim→←ColimΣiM.f (A , B , x) y })
  (λ { A B x r y → ΣColim→←ColimΣl x y (r (coe (code-lift-β {_}{A}{B} x) y)) })
  (λ { A B x → ΣColim→←ColimΣg x })

ΣColim→←ColimΣ : ∀{i}{A}{B} z → ColimΣ→ΣColim {i}{A}{B} (ΣColim→ColimΣ z) == z
ΣColim→←ColimΣ {i}{A}{B} (x , y) = ΣColim→←ColimΣM.f A B x y
