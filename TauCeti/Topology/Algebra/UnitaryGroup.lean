/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# The unitary and special unitary matrix groups are compact

For a finite index type `n` and `𝕜 = ℝ` or `ℂ` (any `RCLike` field), the unitary group
`Matrix.unitaryGroup n 𝕜` and the special unitary group `Matrix.specialUnitaryGroup n 𝕜` are
compact subsets of `Matrix n n 𝕜` in the entrywise topology, hence compact topological groups.

The argument is the classical one. A unitary matrix has unit rows, so all its entries lie in the
closed unit ball (Mathlib's `entry_norm_bound_of_unitary`); the unitary group is therefore contained
in the compact set of matrices with entries in that ball, and it is closed because it is cut out by
the equations `star A * A = 1` and `A * star A = 1`. The special unitary group adds the closed
condition `det A = 1`.

Mathlib already supplies the topological group structure on `unitary R` for a topological star
monoid `R` (`isClosed_unitary` and the `IsTopologicalGroup (unitary R)` instance), so for the
unitary group only compactness is new. The special unitary group is a different submonoid, carrying
its own `Group` instance in `Mathlib/LinearAlgebra/UnitaryGroup.lean`, so its `ContinuousInv` and
`IsTopologicalGroup` instances are recorded here too. Those instances, and the description of the
special unitary group as the unitary group cut out by `det A = 1`, need no `RCLike` hypothesis, and
are stated over a topological commutative star ring instead. Hausdorffness is not proved here: it
is inherited from the ambient matrix topology whenever `𝕜` is Hausdorff.

This is the setup the compact-group representation theory of `SU(2)` runs on; see
`TauCeti/RepresentationTheory/SU2/Basic.lean`.
-/

public section

open Metric Set

namespace TauCeti

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable [CommRing 𝕜] [StarRing 𝕜]

/-- The special unitary group is the unitary group intersected with the set of matrices of
determinant one. -/
theorem coe_specialUnitaryGroup :
    (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜))
      = (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) ∩ {A | A.det = 1} := by
  ext A
  simpa using Matrix.mem_specialUnitaryGroup_iff

variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [ContinuousStar 𝕜]

instance : ContinuousInv (Matrix.specialUnitaryGroup n 𝕜) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

instance : IsTopologicalGroup (Matrix.specialUnitaryGroup n 𝕜) where

end CommRing

section RCLike

variable [RCLike 𝕜]

/-- The unitary group of `n × n` matrices over `ℝ` or `ℂ` is a compact subset of `Matrix n n 𝕜`. -/
theorem isCompact_unitaryGroup :
    IsCompact (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact ((isCompact_closedBall (0 : 𝕜) 1).matrix).of_isClosed_subset isClosed_unitary
    fun _ hA _ _ => mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hA _ _)

instance : CompactSpace (Matrix.unitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryGroup

/-- The special unitary group of `n × n` matrices over `ℝ` or `ℂ` is a closed subset of
`Matrix n n 𝕜`: it is cut out of the closed unitary group by the closed condition `det A = 1`. -/
theorem isClosed_specialUnitaryGroup :
    IsClosed (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  rw [coe_specialUnitaryGroup]
  exact isClosed_unitary.inter
    (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)

/-- The special unitary group of `n × n` matrices over `ℝ` or `ℂ` is a compact subset of
`Matrix n n 𝕜`. -/
theorem isCompact_specialUnitaryGroup :
    IsCompact (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) :=
  isCompact_unitaryGroup.of_isClosed_subset isClosed_specialUnitaryGroup
    fun _ hA => Matrix.specialUnitaryGroup_le_unitaryGroup hA

instance : CompactSpace (Matrix.specialUnitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitaryGroup

end RCLike

end Matrix

end TauCeti
