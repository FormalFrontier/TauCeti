/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Matrix.Frobenius
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# The carrier of symmetric-matrix distributions

The symmetric-matrix distributions of the standard-distributions roadmap live on Mathlib's
self-adjoint subspace `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)`. Over `ℝ`, `star` is
transpose, so this is exactly the subspace of symmetric matrices, and
`Matrix.isHermitian_iff_isSelfAdjoint` connects membership to the spectral API.

This file equips that subspace with the ambient Frobenius norm and inner product while keeping
the subtype topology and uniformity it already carries: the norm structure is induced from
`Matrix.frobeniusNormedAddCommGroup`, whose topology and uniformity are definitionally the
product ones, so the induced structures agree definitionally with the subtype instances. The
`example` blocks record these definitional equalities. The measurable structure is the Borel
structure of the subtype topology, and `volume` is supplied by `measureSpaceOfInnerProductSpace`.

It also fixes the upper-triangular coordinate system used to normalize Lebesgue measure on the
subspace: `TauCeti.symmetricCoordinates` reads off the entries above the diagonal.

## Main declarations

* `TauCeti.upperTriangle` — the index type of upper-triangular positions.
* `TauCeti.card_upperTriangle` — there are `p * (p + 1) / 2` such positions.
* `TauCeti.symmetricMatrixNormedAddCommGroup`, `TauCeti.symmetricMatrixInnerProductSpace` —
  the Frobenius structure on the symmetric subspace.
* `TauCeti.symmetricCoordinates` — the continuous linear equivalence with `upperTriangle p → ℝ`.
* `TauCeti.symmetricCoordinatesMeasurableEquiv` — its measurable-equivalence form.
* `TauCeti.symmetricBasis` — the basis dual to the upper-triangular coordinates.
* `TauCeti.finrank_symmetricMatrix` — the dimension is `p * (p + 1) / 2`.
* `TauCeti.inner_symmetricMatrix_eq_trace_mul` — the Frobenius pairing is the trace pairing.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 1,
  **Symmetric matrices and their Lebesgue measure**.
-/

public section

noncomputable section

open MeasureTheory Module

open scoped RealInnerProductSpace

namespace TauCeti

/-- The index type for the on-or-above-diagonal positions of a `p × p` matrix. A symmetric
matrix is determined by these entries, and `TauCeti.symmetricCoordinates` reads them off. -/
abbrev upperTriangle (p : ℕ) := {ij : Fin p × Fin p // ij.1 ≤ ij.2}

theorem card_upperTriangle (p : ℕ) : Fintype.card (upperTriangle p) = p * (p + 1) / 2 := by
  rw [← Fintype.card_congr (Sym2.sortEquiv (α := Fin p)), Sym2.card, Fintype.card_fin,
    Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

/-! ### The Frobenius structure on the symmetric subspace

The instances below install the Frobenius norm and inner product on the symmetric subspace by
inducing them from the ambient (scoped) Frobenius instances. Because the Frobenius norm is
definitionally compatible with the product topology and uniformity of `Matrix`, the induced
structures agree definitionally with the subtype instances already present; the `example`
blocks at the end of the section check this. -/

section instances

variable (p : ℕ)

instance symmetricMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusNormedAddCommGroup
  letI base : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
    Submodule.normedAddCommGroup _
  -- Forces the uniformity field of the metric to be the subtype uniformity itself, so that
  -- downstream instance search unifies the two syntactically rather than only up to `rfl`.
  { base with toMetricSpace := base.toMetricSpace.replaceUniformity rfl }

instance symmetricMatrixInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusNormedAddCommGroup
  letI : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusInnerProductSpace
  Submodule.innerProductSpace _

instance symmetricMatrixIsUniformAddGroup :
    IsUniformAddGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance symmetricMatrixSecondCountableTopology :
    SecondCountableTopology (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  secondCountable_of_proper

instance symmetricMatrixCompleteSpace :
    CompleteSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  FiniteDimensional.complete ℝ _

instance symmetricMatrixContinuousENorm :
    ContinuousENorm (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) where
  continuous_enorm := by
    let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusNormedAddCommGroup
    change Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      ((‖(A : Matrix (Fin p) (Fin p) ℝ)‖₊ : NNReal) : ENNReal)
    fun_prop

/-- The measurable structure is the Borel structure of the subtype topology. Declared explicitly
so that instance search finds it regardless of which (definitionally equal) route it takes to
the topology. -/
instance symmetricMatrixBorelSpace :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  Subtype.borelSpace _

/-- The uniformity of the Frobenius structure is definitionally the subtype uniformity. -/
example :
    (symmetricMatrixNormedAddCommGroup p).toMetricSpace.toUniformSpace =
      (instUniformSpaceSubtype :
        UniformSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) := by
  with_reducible_and_instances rfl

/-- The uniformity of the Frobenius structure induces the subtype topology definitionally. -/
example :
    (symmetricMatrixNormedAddCommGroup p).toMetricSpace.toUniformSpace.toTopologicalSpace =
      (instTopologicalSpaceSubtype :
        TopologicalSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) := by
  with_reducible_and_instances rfl

/-- The selected topology is the subtype topology. -/
example :
    (inferInstance :
        TopologicalSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) =
      @instTopologicalSpaceSubtype _ _ inferInstance := by
  with_reducible_and_instances rfl

/-- `volume` is supplied by `measureSpaceOfInnerProductSpace`. -/
example :
    (inferInstance : MeasureSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) =
      measureSpaceOfInnerProductSpace :=
  rfl

end instances

/-! ### Symmetry of the entries -/

/-- An element of the symmetric subspace is a Hermitian matrix; over `ℝ` this says that it is
symmetric, as spelled out by `TauCeti.coe_apply_comm`. -/
theorem isHermitian_coe {p : ℕ} (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (A : Matrix (Fin p) (Fin p) ℝ).IsHermitian :=
  A.2

/-- The entries of a symmetric matrix are unchanged by swapping the two indices. -/
theorem coe_apply_comm {p : ℕ} (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))
    (i j : Fin p) :
    (A : Matrix (Fin p) (Fin p) ℝ) i j = (A : Matrix (Fin p) (Fin p) ℝ) j i := by
  simpa using (isHermitian_coe A).apply j i

/-! ### Upper-triangular coordinates -/

section coordinates

variable (p : ℕ)

/-- The continuous linear equivalence reading off the on-or-above-diagonal entries of a
symmetric matrix. Its inverse reconstructs the matrix by reflecting them across the diagonal.

This coordinate system fixes the normalization of `TauCeti.symmetricLebesgue`. -/
@[expose]
def symmetricCoordinates :
    (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ≃L[ℝ] (upperTriangle p → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun A ij := (A : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2
      map_add' A B := rfl
      map_smul' c A := rfl
      invFun x :=
        ⟨Matrix.of fun i j =>
            if h : i ≤ j then x ⟨(i, j), h⟩ else x ⟨(j, i), le_of_not_ge h⟩, by
          refine Matrix.IsHermitian.ext fun i j => ?_
          simp only [Matrix.of_apply, star_trivial]
          rcases le_total i j with h | h
          · rcases h.lt_or_eq with hlt | rfl
            · rw [dite_eq_right (not_le.2 hlt), dite_eq_left h]
            · rfl
          · rcases h.lt_or_eq with hlt | rfl
            · rw [dite_eq_left h, dite_eq_right (not_le.2 hlt)]
            · rfl⟩
      left_inv A := by
        refine Subtype.ext ?_
        ext i j
        simp only [Matrix.of_apply]
        by_cases h : i ≤ j
        · exact dite_eq_left h
        · rw [dite_eq_right h]
          exact coe_apply_comm A j i
      right_inv x := by
        funext ij
        obtain ⟨⟨i, j⟩, hij⟩ := ij
        exact dite_eq_left hij }

@[simp]
theorem symmetricCoordinates_apply (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))
    (ij : upperTriangle p) :
    symmetricCoordinates p A ij = (A : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 :=
  rfl

theorem coe_symmetricCoordinates_symm_apply_of_le (x : upperTriangle p → ℝ) {i j : Fin p}
    (h : i ≤ j) :
    ((symmetricCoordinates p).symm x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(i, j), h⟩ :=
  dite_eq_left h

theorem coe_symmetricCoordinates_symm_apply_of_ge (x : upperTriangle p → ℝ) {i j : Fin p}
    (h : j ≤ i) :
    ((symmetricCoordinates p).symm x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(j, i), h⟩ := by
  by_cases h' : i ≤ j
  · obtain rfl : i = j := le_antisymm h' h
    exact dite_eq_left h'
  · exact dite_eq_right h'

/-- The measurable equivalence induced by `TauCeti.symmetricCoordinates`. -/
@[expose]
def symmetricCoordinatesMeasurableEquiv :
    (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ≃ᵐ (upperTriangle p → ℝ) :=
  (symmetricCoordinates p).toHomeomorph.toMeasurableEquiv

@[simp]
theorem symmetricCoordinatesMeasurableEquiv_coe :
    (symmetricCoordinatesMeasurableEquiv p : _ → upperTriangle p → ℝ) =
      symmetricCoordinates p :=
  rfl

theorem finrank_symmetricMatrix :
    Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) =
      p * (p + 1) / 2 := by
  rw [(symmetricCoordinates p).toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    card_upperTriangle]

/-- The basis of the symmetric subspace dual to the upper-triangular coordinates: its vector at
an on-or-above-diagonal position is the symmetric matrix carrying a one at that position and at
its mirror image, and nothing else. -/
@[expose]
def symmetricBasis :
    Basis (upperTriangle p) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (Pi.basisFun ℝ (upperTriangle p)).map (symmetricCoordinates p).symm.toLinearEquiv

theorem symmetricBasis_apply (ij : upperTriangle p) :
    symmetricBasis p ij = (symmetricCoordinates p).symm (Pi.single ij 1) := by
  simp [symmetricBasis]

theorem coe_symmetricBasis_apply_of_le (ij : upperTriangle p) {k l : Fin p} (h : k ≤ l) :
    ((symmetricBasis p ij : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) k l = if ij = ⟨(k, l), h⟩ then 1 else 0 := by
  rw [symmetricBasis_apply, coe_symmetricCoordinates_symm_apply_of_le p _ h, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

theorem coe_symmetricBasis_apply_of_ge (ij : upperTriangle p) {k l : Fin p} (h : l ≤ k) :
    ((symmetricBasis p ij : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) k l = if ij = ⟨(l, k), h⟩ then 1 else 0 := by
  rw [symmetricBasis_apply, coe_symmetricCoordinates_symm_apply_of_ge p _ h, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

/-- On the diagonal, the coordinate basis vector is a single matrix unit. -/
theorem coe_symmetricBasis_diag (i : Fin p) :
    ((symmetricBasis p ⟨(i, i), le_rfl⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      Matrix (Fin p) (Fin p) ℝ) = Matrix.single i i 1 := by
  ext k l
  rw [Matrix.single_apply]
  rcases le_total k l with h | h
  · rw [coe_symmetricBasis_apply_of_le _ _ h]
    simp [Subtype.ext_iff, Prod.ext_iff]
  · rw [coe_symmetricBasis_apply_of_ge _ _ h]
    simp [Subtype.ext_iff, Prod.ext_iff, and_comm]

/-- Off the diagonal, the coordinate basis vector is a symmetrized pair of matrix units. -/
theorem coe_symmetricBasis_offDiag {i j : Fin p} (hij : i ≤ j) (hne : i ≠ j) :
    ((symmetricBasis p ⟨(i, j), hij⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      Matrix (Fin p) (Fin p) ℝ) = Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  rcases le_total k l with h | h
  · have h2 : ¬(j = k ∧ i = l) := by
      rintro ⟨rfl, rfl⟩
      exact hne (le_antisymm hij h)
    rw [coe_symmetricBasis_apply_of_le _ _ h, ite_eq_right h2, add_zero]
    simp [Subtype.ext_iff, Prod.ext_iff]
  · have h2 : ¬(i = k ∧ j = l) := by
      rintro ⟨rfl, rfl⟩
      exact hne (le_antisymm hij h)
    rw [coe_symmetricBasis_apply_of_ge _ _ h, ite_eq_right h2, zero_add]
    simp [Subtype.ext_iff, Prod.ext_iff, and_comm]

end coordinates

/-! ### The trace pairing -/

/-- On the symmetric subspace, the Frobenius inner product is the trace pairing. This makes
`MeasureTheory.charFun` on the subspace use the same pairing as the Wishart trace statistics. -/
theorem inner_symmetricMatrix_eq_trace_mul {p : ℕ}
    (A Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ⟪A, Θ⟫ = ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace := by
  let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusInnerProductSpace
  rw [Submodule.coe_inner, Matrix.frobenius_inner_eq_trace_transpose_mul,
    (Matrix.isHermitian_iff_isSymm.1 (isHermitian_coe A)).eq, Matrix.trace_mul_comm]

end TauCeti
