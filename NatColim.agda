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
open import lib.types.Paths

open import Other

module NatColim where

Sequence : (i : ULevel) → Type (lsucc i)
Sequence i = Σ (ℕ → Type i) (λ D → (n : ℕ) → D n → D (S n))

shift : ∀ {i} → Sequence i → Sequence i
shift (D , d) = (λ n → D (S n)) , (λ n x → d (S n) x)

-- The type of Seq-coalgebras
record CoindSeqᴹ {i j} : Type (lsucc (lmax i j)) where
  field
    T : Type j
    nx : T → T
    D : T → Type i
    d : ∀ t → D t → D (nx t)

-- Seq-coalgebras coinductively define sequences.
module CoindSeq {i j} (m : CoindSeqᴹ {i} {j}) where
  open CoindSeqᴹ m

  coind-seq-D : T → ℕ → Type i
  coind-seq-D x O = D x
  coind-seq-D x (S n) = coind-seq-D (nx x) n

  coind-seq-d : ∀(x : T) (n : ℕ) → coind-seq-D x n → coind-seq-D x (S n)
  coind-seq-d x O = d x
  coind-seq-d x (S n) = coind-seq-d (nx x) n

  coind-seq : T → Sequence i
  coind-seq x = coind-seq-D x , coind-seq-d x

DepSequence : ∀ {i} → Sequence i → Type (lsucc i)
DepSequence {i} (D , d) = Σ ((n : ℕ) → D n → Type i) (λ G → ∀ (n : ℕ) (a : D n) → G n a → G (S n) (d n a))

depShift : ∀ {i} {A : Sequence i} → DepSequence A → DepSequence (shift A)
depShift {i} {A , a} (B , b) = (λ n x → B (S n) x) , (λ n x y → b (S n) x y)

-- It is also possible to defined dependent sequences coinductively
-- Another principle would be needed to define dependent sequences coinductively over coinductively generated sequences
record CoindDepSeqᴹ {i j} : Type (lsucc (lmax i j)) where
  open CoindSeqᴹ
  field
    T : Sequence i → Type j
    nx : ∀ {A} → T A → T (shift A)
    E : ∀ {A} (t : T A) → fst A O → Type i
    e : ∀ {A} (t : T A) x → E t x → E (nx t) (snd A O x)

module CoindDepSeq {i j} (m : CoindDepSeqᴹ {i} {j}) where
  open CoindDepSeqᴹ m

  coind-depseq-D : ∀ {A} (t : T A) n → fst A n → Type i
  coind-depseq-D t O x = E t x
  coind-depseq-D t (S n) x = coind-depseq-D (nx t) n x

  coind-depseq-d : ∀ {A} (t : T A) n x → coind-depseq-D t n x → coind-depseq-D (nx t) n (snd A n x)
  coind-depseq-d t O x y = e t x y
  coind-depseq-d t (S n) x y = coind-depseq-d (nx t) n x y

  coind-depseq : ∀ {A} (t : T A) → DepSequence A
  coind-depseq t = coind-depseq-D t , coind-depseq-d t

--
SigmaSequenceᴹ : ∀ {i} → CoindSeqᴹ {i} {lsucc i}
SigmaSequenceᴹ {i} = record
  { T = Σ (Sequence i) DepSequence
  ; nx = λ { (A , B) → shift A , depShift B }
  ; D = λ { (A , B) → Σ (fst A O) (fst B O) }
  ; d = λ { (A , B) (x , y) → snd A O x , snd B O x y } }

module SigmaSequenceM {i} = CoindSeq (SigmaSequenceᴹ {i})

SigmaSequence : ∀ {i} {A : Sequence i} → DepSequence A → Sequence i
SigmaSequence {i} {A} B = SigmaSequenceM.coind-seq (A , B)

--
ApplySequenceᴹ : ∀ {i} → CoindSeqᴹ {i} {lsucc i}
ApplySequenceᴹ {i} = record
  { T = Σ (Sequence i) (λ A → DepSequence A × fst A O)
  ; nx = λ { (A , B , x) → shift A , depShift B , snd A O x }
  ; D = λ { (A , B , x) → fst B O x }
  ; d = λ { (A , B , x) y → snd B O x y } }

module ApplySequenceM {i} = CoindSeq (ApplySequenceᴹ {i})

ApplySequence : ∀ {i} {A : Sequence i} → DepSequence A → fst A O → Sequence i
ApplySequence {i} {A} B x = ApplySequenceM.coind-seq (A , B , x)

-- The definition of the sequential colimit as a higher inductive type
module _ {i} (Dd : Sequence i) where
  private
    D = fst Dd
    d = snd Dd
  postulate  -- HIT
    ℕColim : Type i
    ncin' : (n : ℕ) → D n → ℕColim
    ncglue' : (n : ℕ) → (x : D n) → ncin' n x == ncin' (S n) (d n x)

module _ {i} {Dd : Sequence i} where
  ncin = ncin' Dd
  ncglue = ncglue' Dd

module _ {i} (Dd : Sequence i) where
  private
    D = fst Dd
    d = snd Dd
  module ℕColimElim {j} {P : ℕColim Dd → Type j}
    (ncin* : (n : ℕ) (x : D n) → P (ncin n x))
    (ncglue* : (n : ℕ) (x : D n)
      → ncin* n x == ncin* (S n) (d n x) [ P ↓ ncglue n x ])
    where

    postulate  -- HIT
      f : Π (ℕColim Dd) P
      ncin-β : ∀ n x → f (ncin n x) ↦ ncin* n x
    {-# REWRITE ncin-β #-}

    postulate  -- HIT
      ncglue-β : (n : ℕ) (x : D n) → apd f (ncglue n x) == ncglue* n x

  open ℕColimElim public using () renaming (f to ℕColim-elim)

  module ℕColimRec {j} {A : Type j}
    (ncin* : (n : ℕ) → D n → A)
    (ncglue* : (n : ℕ) → (x : D n) → ncin* n x == ncin* (S n) (d n x))
    where

    private
      module M = ℕColimElim ncin* (λ n x → ↓-cst-in (ncglue* n x))

    f : ℕColim Dd → A
    f = M.f

    abstract
      ncglue-β : (n : ℕ) (x : D n) → ap f (ncglue n x) == ncglue* n x
      ncglue-β n x = apd=cst-in {f = f} (M.ncglue-β n x)

-- Definition of the equivalence lift-e : ℕColim (shift A) ≃ ℕColim A
module _ {i} {A : Sequence i} where
  private
    D = fst A
    d = snd A

  module ℕCLift = ℕColimRec (shift A) {A = ℕColim A}
    (λ n x → ncin (S n) x)
    (λ n x → ncglue (S n) x)
  nc-lift = ℕCLift.f
  nc-lift-glue-β = ℕCLift.ncglue-β

  module ℕCLift⁻¹ = ℕColimRec A {A = ℕColim (shift A)}
    (λ n x → ncin n (d n x))
    (λ n x → ncglue n (d n x))
  nc-lift⁻¹ = ℕCLift⁻¹.f
  nc-lift⁻¹-glue-β = ℕCLift⁻¹.ncglue-β

  module ℕCLiftLift⁻¹ = ℕColimElim (shift A) {P = λ x → x == nc-lift⁻¹ (nc-lift x)}
    (λ n x → ncglue n x)
    (λ n x → ↓-='-from-square (ap-idf (ncglue n x) ∙v⊡ connection2 ⊡v∙ ! (ap-∘ nc-lift⁻¹ nc-lift (ncglue n x) ∙ ap (ap nc-lift⁻¹) (nc-lift-glue-β n x) ∙ nc-lift⁻¹-glue-β (S n) x)))
  nc-lift-lift⁻¹ : ∀ x → nc-lift⁻¹ (nc-lift x) == x
  nc-lift-lift⁻¹ x = ! (ℕCLiftLift⁻¹.f x)

  module ℕCLift⁻¹Lift = ℕColimElim A {P = λ x → x == nc-lift (nc-lift⁻¹ x)}
    (λ n x → ncglue n x)
    (λ n x → ↓-='-from-square (ap-idf (ncglue n x) ∙v⊡ connection2 ⊡v∙ ! (ap-∘ nc-lift nc-lift⁻¹ (ncglue n x) ∙ ap (ap nc-lift) (nc-lift⁻¹-glue-β n x) ∙ nc-lift-glue-β n (snd A n x))))
  nc-lift⁻¹-lift : ∀ x → nc-lift (nc-lift⁻¹ x) == x
  nc-lift⁻¹-lift x = ! (ℕCLift⁻¹Lift.f x)

  abstract
    nc-lift-lift⁻¹-abstract : ∀ x → nc-lift⁻¹ (nc-lift x) == x
    nc-lift-lift⁻¹-abstract = nc-lift-lift⁻¹
    nc-lift⁻¹-lift-abstract : ∀ x → nc-lift (nc-lift⁻¹ x) == x
    nc-lift⁻¹-lift-abstract = nc-lift⁻¹-lift

  nc-lift-e : ℕColim (shift A) ≃ ℕColim A
  nc-lift-e = nc-lift , is-eq nc-lift nc-lift⁻¹ nc-lift⁻¹-lift-abstract nc-lift-lift⁻¹-abstract

  nc-lift⁻¹-e : ℕColim A ≃ ℕColim (shift A)
  nc-lift⁻¹-e = nc-lift⁻¹ , is-eq nc-lift⁻¹ nc-lift nc-lift-lift⁻¹-abstract nc-lift⁻¹-lift-abstract

-- This elimination principles corresponds to the indexed higher inductive type
--   ncin0   : fst A 0 → ℕColim A
--   lift    : ℕColim (shift A) → ℕColim A
--   ncglue0 : ∀ (x : fst A 0) → ncin0 x == lift (ncin0 (snd A 0 x))
module ℕColimElimAlt {i j k} (B : Sequence i → Type k) (nxB : ∀ {A} → B A → B (shift A))
                     (P : ∀ (A : Sequence i) → B A → ℕColim A → Type j)
                     (Pi : ∀ A b x → P A b (ncin O x))
                     (Pl : ∀ A b x → P (shift A) (nxB b) x → P A b (nc-lift x))
                     (Pg : ∀ A b x → Pi A b x == Pl A b (ncin O (snd A O x)) (Pi (shift A) (nxB b) (snd A O x)) [ P A b ↓ ncglue O x ])
       where
  private
    coind-elim-i : ∀ (n : ℕ) (A : Sequence i) b (x : fst A n) → P A b (ncin n x)
    coind-elim-i O A b x = Pi A b x
    coind-elim-i (S n) A b x = Pl A b (ncin n x) (coind-elim-i n (shift A) (nxB b) x)

    coind-elim-g : ∀ (n : ℕ) (A : Sequence i) b (x : fst A n) → coind-elim-i n A b x == coind-elim-i (S n) A b (snd A n x) [ P A b ↓ ncglue n x ]
    coind-elim-g O A x = Pg A x
    coind-elim-g (S n) A b x = ↓-ap-in= (P A b) nc-lift (ncglue n x) (nc-lift-glue-β n x) (ap↓ (λ {x} → Pl A b x) (coind-elim-g n (shift A) (nxB b) x))

    module ℕC (A : Sequence i) b = ℕColimElim A {P = λ x → P A b x}
      (λ n x → coind-elim-i n A b x)
      (λ n x → coind-elim-g n A b x)

  f : ∀ (A : Sequence i) b (x : ℕColim A) → P A b x
  f = ℕC.f

  private
    module ℕC2 (A : Sequence i) b = ℕColimElim (shift A) {P = λ x → f A b (nc-lift x) == Pl _ _ _ (f (shift A) (nxB b) x)}
               (λ n x → idp)
               (λ n x → ↓-=-from-squareover ((apd (λ x₁ → f A b (nc-lift x₁)) (ncglue n x)
                                            =⟨ apd-∘'' (f A b) (nc-lift {A = A}) (ncglue n x) (nc-lift-glue-β n x) ⟩
                                            ↓-ap-out= (P A b) nc-lift (ncglue n x) (nc-lift-glue-β n x) (apd (f A b) (ncglue (S n) x))
                                            =⟨ ap (↓-ap-out= (P A b) nc-lift (ncglue n x) (nc-lift-glue-β n x)) (ℕC.ncglue-β A b (S n) x) ⟩
                                            ↓-ap-out= (P A b) nc-lift (ncglue n x) (nc-lift-glue-β n x)
                                              (↓-ap-in= (P A b) nc-lift (ncglue n x) (nc-lift-glue-β n x) (ap↓ (λ {x} → Pl A b x) (coind-elim-g n (shift A) (nxB b) x)))
                                            =⟨ ↓-ap-out=-β (P A b) nc-lift (ncglue n x) (nc-lift-glue-β n x) (ap↓ (λ {x} → Pl A b x) (coind-elim-g n (shift A) (nxB b) x)) ⟩
                                            ap↓ (λ {x} → Pl A b x) (coind-elim-g n (shift A) (nxB b) x)
                                            =⟨ ap (ap↓ (λ {x₁} → Pl A b x₁)) (! (ℕC.ncglue-β (shift A) (nxB b) n x)) ⟩
                                            ap↓ (λ {x} → Pl A b x) (apd (f (shift A) (nxB b)) (ncglue n x))
                                            =⟨ ! (apd-∘' (λ {x} → Pl A b x) (f (shift A) (nxB b)) (ncglue n x)) ⟩
                                            apd (λ x₁ → Pl (fst A , snd A) b x₁ (f (shift A) (nxB b) x₁)) (ncglue n x) =∎)
               ∙v↓⊡ vid-squareover))
  nc-lift-β : ∀ A b x → f A b (nc-lift x) == Pl _ _ _ (f (shift A) (nxB b) x)
  nc-lift-β = ℕC2.f

  abstract
    ncglue-β : ∀ (A : Sequence i) b x → apd (f A b) (ncglue O x) == Pg A b x
    ncglue-β A b x = ℕC.ncglue-β A b 0 x

-- Non-dependent variant
module ℕColimRecAlt {i j k} (B : Sequence i → Type k) (nxB : ∀ {A} → B A → B (shift A))
                    (P : ∀ (A : Sequence i) → B A → Type j)
                    (Pi : ∀ A b x → P A b)
                    (Pl : ∀ A b → P (shift A) (nxB b) → P A b)
                    (Pg : ∀ A b x → Pi A b x == Pl A b (Pi (shift A) (nxB b) (snd A O x)))
       where
  private
    module ℕC = ℕColimElimAlt B nxB (λ A b _ → P A b)
                (λ A b x → Pi A b x)
                (λ A b x r → Pl A b r)
                (λ A b x → ↓-cst-in (Pg A b x))
  f : ∀ (A : Sequence i) b (x : ℕColim A) → P A b
  f = ℕC.f

  nc-lift-β : ∀ (A : Sequence i) b (x : ℕColim (shift A)) → f A b (nc-lift x) == Pl A b (f (shift A) (nxB b) x)
  nc-lift-β = ℕC.nc-lift-β

  abstract
    ncglue-β : ∀ (A : Sequence i) b x → ap (f A b) (ncglue O x) == Pg A b x
    ncglue-β A b x = apd=cst-in (ℕC.ncglue-β A b x)

-- This is the data needed to eliminate from a family of sequences generated coinductively by m
record ℕColimElimCoindᴹ {i j k} (m : CoindSeqᴹ {i} {j}) : Type (lsucc (lmax i (lmax j k))) where
  field
    P : ∀ t → ℕColim (CoindSeq.coind-seq m t) → Type k
    Pi : ∀ t x → P t (ncin O x)
    Pl : ∀ t x → P (CoindSeqᴹ.nx m t) x → P t (nc-lift x)
    Pg : ∀ t x → Pi t x == Pl t (ncin O (snd (CoindSeq.coind-seq m t) O x)) (Pi (CoindSeqᴹ.nx m t) (snd (CoindSeq.coind-seq m t) O x)) [ P t ↓ ncglue O x ]

module ℕColimElimCoind {i j k} (m : CoindSeqᴹ {i} {j}) (m2 : ℕColimElimCoindᴹ {i}{j}{k} m)
  where
  private
    open CoindSeqᴹ m
    open CoindSeq m
    open ℕColimElimCoindᴹ m2
    P₀ : ∀ (A : Sequence i) → ⊤ → ℕColim A → Type _
    P₀ A _ x = ∀ (tp : Σ _ (λ t → A == coind-seq t)) → P (fst tp) (transport ℕColim (snd tp) x)
    Pi₀ : ∀ A t x → P₀ A t (ncin O x)
    Pi₀ _ _ x (t , idp) = Pi t x
    Pl₀ : ∀ A t x → P₀ (shift A) t x → P₀ A t (nc-lift x)
    Pl₀ _ _ x r (t , idp) = Pl t x (r (nx t , idp))
    Pg₀₀ : ∀ (A : Sequence i) t x b → Pi₀ A t x b == Pl₀ A t (ncin O (snd A O x)) (Pi₀ (shift A) t (snd A O x)) b [ P (fst b) ∘ transport ℕColim (snd b) ↓ ncglue O x ]
    Pg₀₀ A _ x (t , idp) = Pg t x
    Pg₀ : ∀ A t x → Pi₀ A t x == Pl₀ A t (ncin O (snd A O x)) (Pi₀ (shift A) t (snd A O x)) [ P₀ A t ↓ ncglue O x ]
    Pg₀ A t x = ↓-Π-cst-app-in (Pg₀₀ A t x)

    module ℕC = ℕColimElimAlt (λ _ → ⊤) (λ _ → tt) P₀ Pi₀ Pl₀ Pg₀

  f : ∀ t x → P t x
  f t x = ℕC.f (coind-seq t) tt x (t , idp)

  nc-lift-β : ∀ t x → f t (nc-lift x) == Pl t x (f (nx t) x)
  nc-lift-β t x = app= (ℕC.nc-lift-β (coind-seq t) tt x) (t , idp)

  abstract
    ncglue-β : ∀ t x → apd (f t) (ncglue O x) == Pg t x
    ncglue-β t x = apd (f t) (ncglue O x)
                   =⟨ apd-∘''' (ℕC.f (coind-seq t) tt) (ncglue O x) (t , idp) ⟩
                   ↓-Π-cst-app-out (apd (ℕC.f (coind-seq t) unit) (ncglue O x)) (t , idp)
                   =⟨ ap (λ x → ↓-Π-cst-app-out x (t , idp)) (ℕC.ncglue-β (coind-seq t) tt x) ⟩
                   ↓-Π-cst-app-out (Pg₀ (coind-seq t) tt x) (t , idp)
                   =⟨ ↓-Π-cst-app-β (Pg₀₀ (coind-seq t) tt x) (t , idp) ⟩
                   Pg t x =∎

-- Non-dependent variant
record ℕColimRecCoindᴹ {i j k} (m : CoindSeqᴹ {i} {j}) : Type (lsucc (lmax i (lmax j k))) where
  field
    P : ∀ t → Type k
    Pi : ∀ t (x : fst (CoindSeq.coind-seq m t) O) → P t
    Pl : ∀ t → P (CoindSeqᴹ.nx m t) → P t
    Pg : ∀ t (x : fst (CoindSeq.coind-seq m t) O) → Pi t x == Pl t (Pi (CoindSeqᴹ.nx m t) (snd (CoindSeq.coind-seq m t) O x))

module ℕColimRecCoind {i j k} (m : CoindSeqᴹ {i} {j}) (m2 : ℕColimRecCoindᴹ {i}{j}{k} m)
  where
  private
    open CoindSeqᴹ m
    open CoindSeq m
    open ℕColimRecCoindᴹ m2
    P₀ : ∀ (A : Sequence i) → ⊤ → Type _
    P₀ A _ = ∀ (tp : Σ _ (λ t → A == coind-seq t)) → P (fst tp)
    Pi₀ : ∀ A t (x : fst A O) → P₀ A t
    Pi₀ _ _ x (t , idp) = Pi t x
    Pl₀ : ∀ A t → P₀ (shift A) t → P₀ A t
    Pl₀ _ _ r (t , idp) = Pl t (r (nx t , idp))
    Pg₀₀ : ∀ (A : Sequence i) t (x : fst A O) → Pi₀ A t x ∼ Pl₀ A t (Pi₀ (shift A) t (snd A O x))
    Pg₀₀ A _ x (t , idp) = Pg t x
    Pg₀ : ∀ A t (x : fst A O) → Pi₀ A t x == Pl₀ A t (Pi₀ (shift A) t (snd A O x))
    Pg₀ A t x = λ= (Pg₀₀ A t x)

    module ℕC = ℕColimRecAlt (λ _ → ⊤) (λ _ → tt) P₀ Pi₀ Pl₀ Pg₀

  f : ∀ t (x : ℕColim (CoindSeq.coind-seq m t)) → P t
  f t x = ℕC.f (coind-seq t) tt x (t , idp)

  nc-lift-β : ∀ t x → f t (nc-lift x) == Pl t (f (nx t) x)
  nc-lift-β t x = app= (ℕC.nc-lift-β (coind-seq t) tt x) (t , idp)

  abstract
    ncglue-β : ∀ t x → ap (f t) (ncglue O x) == Pg t x
    ncglue-β t x = ap (f t) (ncglue O x)
                   =⟨ ap-∘ (λ u → u (t , idp)) (ℕC.f (coind-seq t) tt) (ncglue O x) ⟩
                   app= (ap (ℕC.f (coind-seq t) tt) (ncglue O x)) (t , idp)
                   =⟨ ap (λ x → app= x (t , idp)) (ℕC.ncglue-β (coind-seq t) unit x) ⟩
                   app= (Pg₀ (coind-seq t) tt x) (t , idp)
                   =⟨ app=-β (Pg₀₀ (coind-seq t) tt x) (t , idp) ⟩
                   Pg t x =∎


IdfSequenceᴹ : ∀ {i} → Type i → CoindSeqᴹ {i} {_}
IdfSequenceᴹ {i} A = record
  { T = Unit
  ; nx = λ _ → unit
  ; D = λ _ → A
  ; d = λ _ → idf A }
module IdfSequenceM {i} A = CoindSeq (IdfSequenceᴹ {i} A)

IdfSequence : ∀ {i} → Type i → Sequence i
IdfSequence A = IdfSequenceM.coind-seq A unit

ColimIdfSeqᴹ : ∀ {i} (A : Type i) → ℕColimElimCoindᴹ (IdfSequenceᴹ A)
ColimIdfSeqᴹ A = record
  { P = λ _ x → Σ A (λ y → ncin O y == x)
  ; Pi = λ _ x → x , idp
  ; Pl = λ { _ x (y , p) → y , (ncglue O y ∙ ap nc-lift p) }
  ; Pg = λ _ x → ↓-cst×app-in (ncglue O x) idp (↓-over-×-in' (λ z y → ncin O y == z) {p = ncglue O x} {v = idp} idp (↓-cst=idf-in' (! (∙-unit-r (ncglue O x))))) }
module ColimIdfSeqM {i} A = ℕColimElimCoind {i} _ (ColimIdfSeqᴹ A)

colim-idf-seq : ∀ {i} (A : Type i) → ℕColim (IdfSequence A) ≃ A
colim-idf-seq A = (fst ∘ ColimIdfSeqM.f A unit) , is-eq (fst ∘ ColimIdfSeqM.f A unit) (ncin O) (λ _ → idp) (snd ∘ ColimIdfSeqM.f A unit)
