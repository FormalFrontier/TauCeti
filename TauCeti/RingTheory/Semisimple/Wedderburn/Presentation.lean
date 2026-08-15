/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: the types occurring in the exported signatures.
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
-- Non-public: used only inside proofs.
import TauCeti.RingTheory.Semisimple.BlockCount

/-!
# Chosen Wedderburn presentations

The Artin--Wedderburn theorem in Mathlib gives an existential decomposition of a semisimple ring
as a finite product of matrix rings over division rings.  This file packages one such decomposition
as a `WedderburnPresentation`.  It also packages three refinements supplied by Mathlib: the algebra
form, its finite form, and the split form over an algebraically closed field.  Finally,
`WedderburnEndomorphismAlgebraPresentation` records the more intrinsic version in which each
division ring is the opposite of the endomorphism ring of a chosen simple left ideal.

These presentations deliberately retain all choices made by the existence theorems.  In particular,
their block order and the representatives of their division rings are not canonical, and the
classical `DecidableEq` choice on endomorphism rings enters the exposed division ring instance of
the endomorphism form.  However, the number of blocks is an invariant of the ring (`blockCount_eq`).
None of the other data below should be used as an invariant of the source ring without a separate
uniqueness theorem.

## Main definitions

* `TauCeti.WedderburnPresentation`: a chosen ring equivalence with a product of matrix rings over
  division rings.
* `TauCeti.WedderburnAlgebraPresentation`: the corresponding algebra equivalence over a base.
* `TauCeti.FiniteWedderburnAlgebraPresentation`: an algebra presentation whose division algebras
  are finite over the base.
* `TauCeti.SplitWedderburnAlgebraPresentation`: a presentation by matrix algebras over the base
  field itself.
* `TauCeti.WedderburnEndomorphismAlgebraPresentation`: a presentation whose coefficient rings are
  opposites of endomorphism rings of simple left ideals.
* `TauCeti.IsSemisimpleRing.wedderburnPresentation`: choose an Artin--Wedderburn presentation of a
  semisimple ring.
* `TauCeti.IsSemisimpleRing.wedderburnAlgebraPresentation`: choose an algebraic Artin--Wedderburn
  presentation of a semisimple algebra.
* `TauCeti.IsSemisimpleRing.finiteWedderburnAlgebraPresentation`: choose an algebraic
  Artin--Wedderburn presentation whose coefficient division algebras are finite over the base.
* `TauCeti.IsSemisimpleRing.splitWedderburnAlgebraPresentation`: choose a split Artin--Wedderburn
  presentation of a finite-dimensional semisimple algebra over an algebraically closed field.
* `TauCeti.IsSemisimpleRing.wedderburnEndomorphismAlgebraPresentation`: choose the endomorphism
  form of an algebraic Artin--Wedderburn presentation.

## Main results

* `TauCeti.WedderburnPresentation.blockCount_eq`: the number of blocks is the same for any two
  Wedderburn presentations of the same ring.
* `TauCeti.WedderburnPresentation.isSemisimpleRing`: a ring admitting a Wedderburn presentation is
  semisimple.

## References

This implements the Layer 2 target "the presentation, named (choice-laden)" of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, §3, or C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace TauCeti

universe u v w

/-- A chosen Artin--Wedderburn presentation of a ring as a finite product of matrix rings over
division rings.

The order of the blocks and the representatives of their division rings are arbitrary choices. -/
structure WedderburnPresentation (R : Type u) [Ring R] where
  /-- The number of matrix blocks. -/
  blockCount : ℕ
  /-- The division ring underlying each block. -/
  divisionRing : Fin blockCount → Type w
  /-- The degree of each matrix block. -/
  degree : Fin blockCount → ℕ
  /-- Each coefficient ring is a division ring. -/
  [instDivisionRing : ∀ i, DivisionRing (divisionRing i)]
  /-- Every matrix block has positive degree. -/
  [instNeZeroDegree : ∀ i, NeZero (degree i)]
  /-- The chosen product decomposition. -/
  equiv : R ≃+* ∀ i, Matrix (Fin (degree i)) (Fin (degree i)) (divisionRing i)

attribute [instance] WedderburnPresentation.instDivisionRing WedderburnPresentation.instNeZeroDegree

/-- A chosen Artin--Wedderburn presentation of an algebra, with every coefficient division ring
carrying a compatible algebra structure over the base. -/
structure WedderburnAlgebraPresentation (K : Type v) (A : Type u) [CommSemiring K] [Ring A]
    [Algebra K A] where
  /-- The number of matrix blocks. -/
  blockCount : ℕ
  /-- The division algebra underlying each block. -/
  divisionRing : Fin blockCount → Type w
  /-- The degree of each matrix block. -/
  degree : Fin blockCount → ℕ
  /-- Each coefficient ring is a division ring. -/
  [instDivisionRing : ∀ i, DivisionRing (divisionRing i)]
  /-- Each coefficient division ring is an algebra over the base. -/
  [instAlgebra : ∀ i, Algebra K (divisionRing i)]
  /-- Every matrix block has positive degree. -/
  [instNeZeroDegree : ∀ i, NeZero (degree i)]
  /-- The chosen product decomposition as an equivalence of algebras. -/
  equiv : A ≃ₐ[K] ∀ i, Matrix (Fin (degree i)) (Fin (degree i)) (divisionRing i)

attribute [instance] WedderburnAlgebraPresentation.instDivisionRing
  WedderburnAlgebraPresentation.instAlgebra WedderburnAlgebraPresentation.instNeZeroDegree

/-- A chosen algebraic Wedderburn presentation whose coefficient division algebras are finite over
the base. -/
structure FiniteWedderburnAlgebraPresentation (K : Type v) (A : Type u) [CommSemiring K]
    [Ring A] [Algebra K A] extends WedderburnAlgebraPresentation K A where
  /-- Every coefficient division algebra is finite as a module over the base. -/
  [instModuleFinite : ∀ i, Module.Finite K (divisionRing i)]

attribute [instance] FiniteWedderburnAlgebraPresentation.instModuleFinite

/-- A chosen split Wedderburn presentation over a field: all coefficient division algebras are the
base field itself. -/
structure SplitWedderburnAlgebraPresentation (K : Type v) (A : Type u) [Field K] [Ring A]
    [Algebra K A] where
  /-- The number of matrix blocks. -/
  blockCount : ℕ
  /-- The degree of each matrix block. -/
  degree : Fin blockCount → ℕ
  /-- Every matrix block has positive degree. -/
  [instNeZeroDegree : ∀ i, NeZero (degree i)]
  /-- The chosen product decomposition as an equivalence of algebras. -/
  equiv : A ≃ₐ[K] ∀ i, Matrix (Fin (degree i)) (Fin (degree i)) K

attribute [instance] SplitWedderburnAlgebraPresentation.instNeZeroDegree

/-- A chosen Artin--Wedderburn presentation in which each coefficient division ring is the
opposite of the endomorphism ring of a chosen simple left ideal. -/
structure WedderburnEndomorphismAlgebraPresentation (K : Type v) (A : Type u) [CommSemiring K]
    [Ring A] [Algebra K A] where
  /-- The number of matrix blocks. -/
  blockCount : ℕ
  /-- A simple left ideal representing each block. -/
  simpleIdeal : Fin blockCount → Ideal A
  /-- The degree of each matrix block. -/
  degree : Fin blockCount → ℕ
  /-- Each chosen left ideal is a simple module. -/
  [instIsSimpleModule : ∀ i, IsSimpleModule A (simpleIdeal i)]
  /-- Every matrix block has positive degree. -/
  [instNeZeroDegree : ∀ i, NeZero (degree i)]
  /-- The chosen product decomposition as an equivalence of algebras. -/
  equiv : A ≃ₐ[K] ∀ i,
    Matrix (Fin (degree i)) (Fin (degree i)) (Module.End A (simpleIdeal i))ᵐᵒᵖ

attribute [instance] WedderburnEndomorphismAlgebraPresentation.instIsSimpleModule
  WedderburnEndomorphismAlgebraPresentation.instNeZeroDegree

namespace WedderburnAlgebraPresentation

variable {K : Type v} {A : Type u} [CommSemiring K] [Ring A] [Algebra K A]

/-- Forget the algebra structures in an algebraic Wedderburn presentation. -/
@[expose]
def toWedderburnPresentation (P : WedderburnAlgebraPresentation K A) :
    WedderburnPresentation A where
  blockCount := P.blockCount
  divisionRing := P.divisionRing
  degree := P.degree
  equiv := P.equiv.toRingEquiv

@[simp]
theorem toWedderburnPresentation_blockCount (P : WedderburnAlgebraPresentation K A) :
    P.toWedderburnPresentation.blockCount = P.blockCount :=
  rfl

@[simp]
theorem toWedderburnPresentation_divisionRing (P : WedderburnAlgebraPresentation K A) :
    P.toWedderburnPresentation.divisionRing = P.divisionRing :=
  rfl

@[simp]
theorem toWedderburnPresentation_degree (P : WedderburnAlgebraPresentation K A) :
    P.toWedderburnPresentation.degree = P.degree :=
  rfl

@[simp]
theorem toWedderburnPresentation_equiv (P : WedderburnAlgebraPresentation K A) :
    P.toWedderburnPresentation.equiv = P.equiv.toRingEquiv :=
  rfl

end WedderburnAlgebraPresentation

namespace SplitWedderburnAlgebraPresentation

variable {K : Type v} {A : Type u} [Field K] [Ring A] [Algebra K A]

/-- View a split Wedderburn presentation as a general algebraic Wedderburn presentation whose
division rings are all `K`. -/
@[expose]
def toWedderburnAlgebraPresentation (P : SplitWedderburnAlgebraPresentation K A) :
    WedderburnAlgebraPresentation.{u, v, v} K A where
  blockCount := P.blockCount
  divisionRing := fun _ ↦ K
  degree := P.degree
  equiv := P.equiv

@[simp]
theorem toWedderburnAlgebraPresentation_blockCount (P : SplitWedderburnAlgebraPresentation K A) :
    P.toWedderburnAlgebraPresentation.blockCount = P.blockCount :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_divisionRing (P : SplitWedderburnAlgebraPresentation K A)
    (i : Fin P.blockCount) :
    P.toWedderburnAlgebraPresentation.divisionRing i = K :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_degree (P : SplitWedderburnAlgebraPresentation K A) :
    P.toWedderburnAlgebraPresentation.degree = P.degree :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_equiv (P : SplitWedderburnAlgebraPresentation K A) :
    P.toWedderburnAlgebraPresentation.equiv = P.equiv :=
  rfl

end SplitWedderburnAlgebraPresentation

namespace WedderburnEndomorphismAlgebraPresentation

variable {K : Type v} {A : Type u} [CommSemiring K] [Ring A] [Algebra K A]

/-- View an endomorphism Wedderburn presentation as a general algebraic Wedderburn presentation
whose division rings are opposites of endomorphism rings of simple left ideals. -/
@[expose]
noncomputable def toWedderburnAlgebraPresentation
    (P : WedderburnEndomorphismAlgebraPresentation K A) :
    WedderburnAlgebraPresentation.{u, v, u} K A :=
  -- `Module.End.instDivisionRing` requires `DecidableEq`; this arbitrary `Classical.decEq` choice
  -- becomes part of the exposed `instDivisionRing` field. Downstream results should use
  -- `P.toWedderburnAlgebraPresentation.instDivisionRing` rather than re-synthesizing.
  letI : ∀ i, DecidableEq (Module.End A (P.simpleIdeal i)) := fun _ ↦ Classical.decEq _
  { blockCount := P.blockCount
    divisionRing := fun i ↦ (Module.End A (P.simpleIdeal i))ᵐᵒᵖ
    degree := P.degree
    -- The ring structure on `(Module.End A (P.simpleIdeal i))ᵐᵒᵖ` inferred from `Module.End` and
    -- the ring structure coming from the chosen `DivisionRing` instance (via Schur's Lemma) agree
    -- by defeq only up to unfolding.
    equiv := P.equiv }

@[simp]
theorem toWedderburnAlgebraPresentation_blockCount
    (P : WedderburnEndomorphismAlgebraPresentation K A) :
    P.toWedderburnAlgebraPresentation.blockCount = P.blockCount :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_divisionRing
    (P : WedderburnEndomorphismAlgebraPresentation K A) (i : Fin P.blockCount) :
    P.toWedderburnAlgebraPresentation.divisionRing i = (Module.End A (P.simpleIdeal i))ᵐᵒᵖ :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_degree
    (P : WedderburnEndomorphismAlgebraPresentation K A) :
    P.toWedderburnAlgebraPresentation.degree = P.degree :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_equiv
    (P : WedderburnEndomorphismAlgebraPresentation K A) :
    P.toWedderburnAlgebraPresentation.equiv = P.equiv :=
  rfl

end WedderburnEndomorphismAlgebraPresentation

namespace IsSemisimpleRing

private theorem nonempty_wedderburnPresentation (R : Type u) [Ring R] [IsSemisimpleRing R] :
    Nonempty (WedderburnPresentation.{u, u} R) := by
  obtain ⟨n, D, d, hD, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  let : ∀ i, DivisionRing (D i) := hD
  let : ∀ i, NeZero (d i) := hd
  exact ⟨{ blockCount := n, divisionRing := D, degree := d, equiv := e }⟩

/-- Choose an Artin--Wedderburn presentation of a semisimple ring. -/
noncomputable def wedderburnPresentation (R : Type u) [Ring R] [IsSemisimpleRing R] :
    WedderburnPresentation.{u, u} R :=
  Classical.choice (nonempty_wedderburnPresentation R)

private theorem nonempty_wedderburnAlgebraPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] :
    Nonempty (WedderburnAlgebraPresentation.{u, v, u} K A) := by
  obtain ⟨n, D, d, hD, hKA, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing K A
  let : ∀ i, DivisionRing (D i) := hD
  let : ∀ i, Algebra K (D i) := hKA
  let : ∀ i, NeZero (d i) := hd
  exact ⟨{ blockCount := n, divisionRing := D, degree := d, equiv := e }⟩

/-- Choose an algebraic Artin--Wedderburn presentation of a semisimple algebra. -/
noncomputable def wedderburnAlgebraPresentation (K : Type v) (A : Type u) [CommSemiring K]
    [Ring A] [Algebra K A] [IsSemisimpleRing A] : WedderburnAlgebraPresentation.{u, v, u} K A :=
  Classical.choice (nonempty_wedderburnAlgebraPresentation K A)

private theorem nonempty_finiteWedderburnAlgebraPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] [Module.Finite K A] :
    Nonempty (FiniteWedderburnAlgebraPresentation.{u, v, u} K A) := by
  obtain ⟨n, D, d, hD, hKA, hfinite, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite K A
  let : ∀ i, DivisionRing (D i) := hD
  let : ∀ i, Algebra K (D i) := hKA
  let : ∀ i, Module.Finite K (D i) := hfinite
  let : ∀ i, NeZero (d i) := hd
  exact ⟨{ blockCount := n, divisionRing := D, degree := d, equiv := e }⟩

/-- Choose an algebraic Artin--Wedderburn presentation whose coefficient division algebras are
finite over the base. -/
noncomputable def finiteWedderburnAlgebraPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] [Module.Finite K A] :
    FiniteWedderburnAlgebraPresentation.{u, v, u} K A :=
  Classical.choice (nonempty_finiteWedderburnAlgebraPresentation K A)

private theorem nonempty_splitWedderburnAlgebraPresentation (K : Type v) (A : Type u) [Field K]
    [IsAlgClosed K] [Ring A] [Algebra K A] [IsSemisimpleRing A] [FiniteDimensional K A] :
    Nonempty (SplitWedderburnAlgebraPresentation K A) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K A
  let : ∀ i, NeZero (d i) := hd
  exact ⟨{ blockCount := n, degree := d, equiv := e }⟩

/-- Choose a split Artin--Wedderburn presentation of a finite-dimensional semisimple algebra over
an algebraically closed field. -/
noncomputable def splitWedderburnAlgebraPresentation (K : Type v) (A : Type u) [Field K]
    [IsAlgClosed K] [Ring A] [Algebra K A] [IsSemisimpleRing A] [FiniteDimensional K A] :
    SplitWedderburnAlgebraPresentation K A :=
  Classical.choice (nonempty_splitWedderburnAlgebraPresentation K A)

private theorem nonempty_wedderburnEndomorphismAlgebraPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] :
    Nonempty (WedderburnEndomorphismAlgebraPresentation K A) := by
  obtain ⟨n, S, d, hS, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite K A
  let : ∀ i, IsSimpleModule A (S i) := hS
  let : ∀ i, NeZero (d i) := hd
  exact ⟨{ blockCount := n, simpleIdeal := S, degree := d, equiv := e }⟩

/-- Choose the endomorphism form of an algebraic Artin--Wedderburn presentation. -/
noncomputable def wedderburnEndomorphismAlgebraPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] :
    WedderburnEndomorphismAlgebraPresentation K A :=
  Classical.choice (nonempty_wedderburnEndomorphismAlgebraPresentation K A)

end IsSemisimpleRing

namespace WedderburnPresentation

variable {R : Type u} [Ring R]

/-- The number of blocks of a Wedderburn presentation is an invariant of the ring. -/
theorem blockCount_eq (P : WedderburnPresentation.{u, w} R)
    (Q : WedderburnPresentation.{u, w'} R) : P.blockCount = Q.blockCount :=
  card_blocks_eq P.equiv Q.equiv

/-- A ring admitting a Wedderburn presentation is semisimple. -/
theorem isSemisimpleRing (P : WedderburnPresentation R) : IsSemisimpleRing R :=
  P.equiv.symm.isSemisimpleRing

end WedderburnPresentation

end TauCeti
