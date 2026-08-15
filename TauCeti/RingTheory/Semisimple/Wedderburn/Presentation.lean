/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import TauCeti.RingTheory.Semisimple.Wedderburn.Blocks

/-!
# Chosen Wedderburn presentations

The Artin--Wedderburn theorem in Mathlib gives an existential decomposition of a semisimple ring
as a finite product of matrix rings over division rings.  This file packages one such decomposition
as a `WedderburnPresentation`.  It also packages three refinements supplied by Mathlib: the algebra
form, its finite form, and the split form over an algebraically closed field.  Finally,
`WedderburnEndomorphismPresentation` records the more intrinsic version in which each division ring
is the opposite of the endomorphism ring of a chosen simple left ideal.

These presentations deliberately retain all choices made by the existence theorems.  In particular,
their block order is not canonical, and none of the data below should be used as an invariant of the
source ring without a separate uniqueness theorem.

## Main definitions

* `TauCeti.WedderburnPresentation`: a chosen ring equivalence with a product of matrix rings over
  division rings.
* `TauCeti.WedderburnAlgebraPresentation`: the corresponding algebra equivalence over a base.
* `TauCeti.FiniteWedderburnAlgebraPresentation`: an algebra presentation whose division algebras
  are finite over the base.
* `TauCeti.SplitWedderburnAlgebraPresentation`: a presentation by matrix algebras over the base
  field itself.
* `TauCeti.WedderburnEndomorphismPresentation`: a presentation whose coefficient rings are
  opposites of endomorphism rings of simple left ideals.

## Main results

* `IsSemisimpleRing.wedderburnPresentation` and its algebraic refinements choose the corresponding
  presentations for a semisimple ring.
* `TauCeti.WedderburnPresentation.exists_simpleSubmodule` shows that the chosen blocks enumerate the
  isomorphism classes of simple left ideals, by applying `TauCeti.blocks_equiv_simpleModules`.

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

/-- A chosen algebraic Wedderburn presentation whose coefficient division algebras are finite over
the base. -/
structure FiniteWedderburnAlgebraPresentation (K : Type v) (A : Type u) [CommSemiring K]
    [Ring A] [Algebra K A] extends WedderburnAlgebraPresentation K A where
  /-- Every coefficient division algebra is finite as a module over the base. -/
  [instModuleFinite : ∀ i, Module.Finite K (divisionRing i)]

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

/-- A chosen Artin--Wedderburn presentation in which each coefficient division ring is the
opposite of the endomorphism ring of a chosen simple left ideal. -/
structure WedderburnEndomorphismPresentation (K : Type v) (A : Type u) [CommSemiring K]
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

namespace WedderburnAlgebraPresentation

variable {K : Type v} {A : Type u} [CommSemiring K] [Ring A] [Algebra K A]

/-- Forget the algebra structures in an algebraic Wedderburn presentation. -/
@[expose]
def toWedderburnPresentation (P : WedderburnAlgebraPresentation K A) :
    WedderburnPresentation A := by
  letI : ∀ i, DivisionRing (P.divisionRing i) := P.instDivisionRing
  letI : ∀ i, Algebra K (P.divisionRing i) := P.instAlgebra
  letI : ∀ i, NeZero (P.degree i) := P.instNeZeroDegree
  exact @WedderburnPresentation.mk.{u, _} A _ P.blockCount P.divisionRing P.degree
    P.instDivisionRing P.instNeZeroDegree P.equiv.toRingEquiv

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
    letI : ∀ i, DivisionRing (P.divisionRing i) := P.instDivisionRing
    letI : ∀ i, Algebra K (P.divisionRing i) := P.instAlgebra
    P.toWedderburnPresentation.equiv = P.equiv.toRingEquiv :=
  rfl

end WedderburnAlgebraPresentation

namespace SplitWedderburnAlgebraPresentation

variable {K : Type v} {A : Type u} [Field K] [Ring A] [Algebra K A]

/-- View a split Wedderburn presentation as a general algebraic Wedderburn presentation whose
division rings are all `K`. -/
@[expose]
def toWedderburnAlgebraPresentation (P : SplitWedderburnAlgebraPresentation K A) :
    WedderburnAlgebraPresentation.{u, v, v} K A :=
  @WedderburnAlgebraPresentation.mk.{u, v, v} K A _ _ _
    P.blockCount
    (fun _ ↦ K)
    P.degree
    (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance)
    P.instNeZeroDegree
    P.equiv

/-- Forget the algebra structures in a split Wedderburn presentation. -/
@[expose]
def toWedderburnPresentation (P : SplitWedderburnAlgebraPresentation K A) :
    WedderburnPresentation.{u, v} A :=
  P.toWedderburnAlgebraPresentation.toWedderburnPresentation

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

@[simp]
theorem toWedderburnPresentation_blockCount (P : SplitWedderburnAlgebraPresentation K A) :
    P.toWedderburnPresentation.blockCount = P.blockCount :=
  rfl

@[simp]
theorem toWedderburnPresentation_divisionRing (P : SplitWedderburnAlgebraPresentation K A)
    (i : Fin P.blockCount) :
    P.toWedderburnPresentation.divisionRing i = K :=
  rfl

@[simp]
theorem toWedderburnPresentation_degree (P : SplitWedderburnAlgebraPresentation K A) :
    P.toWedderburnPresentation.degree = P.degree :=
  rfl

@[simp]
theorem toWedderburnPresentation_equiv (P : SplitWedderburnAlgebraPresentation K A) :
    P.toWedderburnPresentation.equiv = P.equiv.toRingEquiv :=
  rfl
end SplitWedderburnAlgebraPresentation

namespace WedderburnEndomorphismPresentation

variable {K : Type v} {A : Type u} [CommSemiring K] [Ring A] [Algebra K A]

/-- View an endomorphism Wedderburn presentation as a general algebraic Wedderburn presentation
whose division rings are opposites of endomorphism rings of simple left ideals. -/
@[expose]
noncomputable def toWedderburnAlgebraPresentation (P : WedderburnEndomorphismPresentation K A) :
    WedderburnAlgebraPresentation.{u, v, u} K A :=
  open Classical in
  let _ : ∀ i, IsSimpleModule A (P.simpleIdeal i) := P.instIsSimpleModule
  let _ : ∀ i, DivisionRing (Module.End A (P.simpleIdeal i))ᵐᵒᵖ := fun _ ↦ inferInstance
  let _ : ∀ i, Algebra K (Module.End A (P.simpleIdeal i))ᵐᵒᵖ := fun _ ↦ inferInstance
  @WedderburnAlgebraPresentation.mk.{u, v, u} K A _ _ _
    P.blockCount
    (fun i ↦ (Module.End A (P.simpleIdeal i))ᵐᵒᵖ)
    P.degree
    (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance)
    P.instNeZeroDegree
    P.equiv

/-- Forget the algebra structures in an endomorphism Wedderburn presentation. -/
@[expose]
noncomputable def toWedderburnPresentation (P : WedderburnEndomorphismPresentation K A) :
    WedderburnPresentation.{u, u} A :=
  P.toWedderburnAlgebraPresentation.toWedderburnPresentation

@[simp]
theorem toWedderburnAlgebraPresentation_blockCount (P : WedderburnEndomorphismPresentation K A) :
    P.toWedderburnAlgebraPresentation.blockCount = P.blockCount :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_divisionRing (P : WedderburnEndomorphismPresentation K A)
    (i : Fin P.blockCount) :
    P.toWedderburnAlgebraPresentation.divisionRing i = (Module.End A (P.simpleIdeal i))ᵐᵒᵖ :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_degree (P : WedderburnEndomorphismPresentation K A) :
    P.toWedderburnAlgebraPresentation.degree = P.degree :=
  rfl

@[simp]
theorem toWedderburnAlgebraPresentation_equiv (P : WedderburnEndomorphismPresentation K A) :
    P.toWedderburnAlgebraPresentation.equiv = P.equiv :=
  rfl

@[simp]
theorem toWedderburnPresentation_blockCount (P : WedderburnEndomorphismPresentation K A) :
    P.toWedderburnPresentation.blockCount = P.blockCount :=
  rfl

@[simp]
theorem toWedderburnPresentation_divisionRing (P : WedderburnEndomorphismPresentation K A)
    (i : Fin P.blockCount) :
    P.toWedderburnPresentation.divisionRing i = (Module.End A (P.simpleIdeal i))ᵐᵒᵖ :=
  rfl

@[simp]
theorem toWedderburnPresentation_degree (P : WedderburnEndomorphismPresentation K A) :
    P.toWedderburnPresentation.degree = P.degree :=
  rfl

@[simp]
theorem toWedderburnPresentation_equiv (P : WedderburnEndomorphismPresentation K A) :
    P.toWedderburnPresentation.equiv = P.equiv.toRingEquiv :=
  rfl
end WedderburnEndomorphismPresentation

namespace IsSemisimpleRing

private theorem nonempty_wedderburnPresentation (R : Type u) [Ring R] [IsSemisimpleRing R] :
    Nonempty (WedderburnPresentation.{u, u} R) := by
  obtain ⟨n, D, d, hD, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  exact ⟨@WedderburnPresentation.mk.{u, u} R _ n D d hD hd e⟩

/-- Choose an Artin--Wedderburn presentation of a semisimple ring. -/
noncomputable def wedderburnPresentation (R : Type u) [Ring R] [IsSemisimpleRing R] :
    WedderburnPresentation.{u, u} R :=
  Classical.choice (nonempty_wedderburnPresentation R)

private theorem nonempty_wedderburnAlgebraPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] :
    Nonempty (WedderburnAlgebraPresentation.{u, v, u} K A) := by
  obtain ⟨n, D, d, hD, hKA, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing K A
  exact ⟨@WedderburnAlgebraPresentation.mk.{u, v, u} K A _ _ _ n D d hD hKA hd e⟩

/-- Choose an algebraic Artin--Wedderburn presentation of a semisimple algebra. -/
noncomputable def wedderburnAlgebraPresentation (K : Type v) (A : Type u) [CommSemiring K]
    [Ring A] [Algebra K A] [IsSemisimpleRing A] : WedderburnAlgebraPresentation.{u, v, u} K A :=
  Classical.choice (nonempty_wedderburnAlgebraPresentation K A)

private theorem nonempty_finiteWedderburnAlgebraPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] [Module.Finite K A] :
    Nonempty (FiniteWedderburnAlgebraPresentation.{u, v, u} K A) := by
  obtain ⟨n, D, d, hD, hKA, hfinite, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite K A
  exact ⟨@FiniteWedderburnAlgebraPresentation.mk.{u, v, u} K A _ _ _
    (@WedderburnAlgebraPresentation.mk.{u, v, u} K A _ _ _ n D d hD hKA hd e) hfinite⟩

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
  exact ⟨@SplitWedderburnAlgebraPresentation.mk.{u, v} K A _ _ _ n d hd e⟩

/-- Choose a split Artin--Wedderburn presentation of a finite-dimensional semisimple algebra over
an algebraically closed field. -/
noncomputable def splitWedderburnAlgebraPresentation (K : Type v) (A : Type u) [Field K]
    [IsAlgClosed K] [Ring A] [Algebra K A] [IsSemisimpleRing A] [FiniteDimensional K A] :
    SplitWedderburnAlgebraPresentation K A :=
  Classical.choice (nonempty_splitWedderburnAlgebraPresentation K A)

private theorem nonempty_wedderburnEndomorphismPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] :
    Nonempty (WedderburnEndomorphismPresentation K A) := by
  obtain ⟨n, S, d, hS, hd, ⟨e⟩⟩ :=
    _root_.IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite K A
  exact ⟨@WedderburnEndomorphismPresentation.mk.{u, v} K A _ _ _ n S d hS hd e⟩

/-- Choose the endomorphism form of an algebraic Artin--Wedderburn presentation. -/
noncomputable def wedderburnEndomorphismPresentation (K : Type v) (A : Type u)
    [CommSemiring K] [Ring A] [Algebra K A] [IsSemisimpleRing A] :
    WedderburnEndomorphismPresentation K A :=
  Classical.choice (nonempty_wedderburnEndomorphismPresentation K A)

end IsSemisimpleRing

namespace WedderburnPresentation

variable {R : Type u} [Ring R]

/-- The blocks in a chosen Wedderburn presentation enumerate the isomorphism classes of simple
left ideals: they determine a pairwise non-isomorphic, exhaustive family of simple left ideals. -/
theorem exists_simpleSubmodule (P : WedderburnPresentation R) :
    ∃ S : Fin P.blockCount → Submodule R R,
      (∀ i, IsSimpleModule R (S i)) ∧
      (∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) ∧
      ∀ I : Submodule R R, IsSimpleModule R I → ∃ i, Nonempty (I ≃ₗ[R] S i) := by
  let _ : ∀ i, DivisionRing (P.divisionRing i) := P.instDivisionRing
  let _ : ∀ i, NeZero (P.degree i) := P.instNeZeroDegree
  have : IsSemisimpleRing R := P.equiv.symm.isSemisimpleRing
  exact blocks_equiv_simpleModules P.equiv

end WedderburnPresentation

end TauCeti
