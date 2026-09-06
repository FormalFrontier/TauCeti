/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# The points modulo torsion, and the Néron-Tate pairing on them

The Néron-Tate pairing vanishes as soon as either argument is torsion, so it descends to the
quotient of the points by their torsion submodule, unconditionally. Under
`[Northcott (Point.canonicalHeight (W := W))]` — the hypothesis that makes height zero force
torsion — the descended pairing is moreover positive definite. That quotient is where the
regulator is defined.

## Main definitions

* `WeierstrassCurve.Affine.PointModTorsion`: the points modulo torsion. Neither its freeness nor
  its rank is restated here, both being Mathlib's: under `[AddGroup.FG W.Point]` the quotient is
  free of finite rank by `Module.free_of_finite_type_torsion_free'`, and its rank is
  `Module.finrank ℤ W.Point` by `finrank_quotient_eq_of_le_torsion` at `le_rfl`. The definition
  itself assumes neither, so the name says only what the quotient is.
* `WeierstrassCurve.Affine.neronTatePairingModTorsion`: the Néron-Tate pairing on that quotient.
* `WeierstrassCurve.Affine.neronTateGramMatrix`: its matrix in a basis, whose determinant is the
  regulator.

## Main results

* `WeierstrassCurve.Affine.torsion_le_ker_neronTatePairing`: the pairing kills the torsion
  submodule, which is what the descent consumes.
* `WeierstrassCurve.Affine.neronTatePairingModTorsion_mk`: the descended pairing agrees with the
  original on representatives.
* `WeierstrassCurve.Affine.neronTatePairingModTorsion_self_eq_zero_iff`: the descended pairing is
  positive definite, given the `Northcott` hypothesis. This is what dividing by the torsion buys;
  on `W.Point` itself the pairing is only semidefinite.
* `WeierstrassCurve.Affine.isSymm_neronTateGramMatrix`: the Gram matrix is symmetric. The
  regulator is the determinant of this matrix in a basis of the quotient, and is defined
  separately.
-/

public section

open Height

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [AdmissibleAbsValues F] [DecidableEq F]

variable (W) in
/-- **The points modulo torsion**, the Mordell-Weil group with its torsion divided out. -/
abbrev PointModTorsion := W.Point ⧸ Submodule.torsion ℤ W.Point

/-- The pairing vanishes on the torsion submodule, which is what the descent consumes. -/
theorem torsion_le_ker_neronTatePairing [W.toAffine.IsElliptic] :
    Submodule.torsion ℤ W.Point ≤ (neronTatePairing W).ker := by
  intro P hP
  refine LinearMap.ext fun Q ↦ neronTatePairing_eq_zero_of_isOfFinAddOrder_left ?_ Q
  -- `Submodule.torsion_int` identifies the module-theoretic torsion with the group-theoretic one
  rwa [← AddCommGroup.mem_torsion, ← Submodule.torsion_int]

variable (W) in
/-- **The Néron-Tate pairing on the points modulo torsion.** -/
noncomputable def neronTatePairingModTorsion [W.toAffine.IsElliptic] :
    LinearMap.BilinMap ℤ (PointModTorsion W) ℝ :=
  LinearMap.IsRefl.liftQ₂ (neronTatePairing W) (Submodule.torsion ℤ W.Point)
    isRefl_neronTatePairing torsion_le_ker_neronTatePairing

/-- The descended pairing agrees with the pairing on representatives. -/
@[simp]
theorem neronTatePairingModTorsion_mk [W.toAffine.IsElliptic] (P Q : W.Point) :
    neronTatePairingModTorsion W (Submodule.Quotient.mk P) (Submodule.Quotient.mk Q)
      = neronTatePairing W P Q := by
  simp [neronTatePairingModTorsion]

/-- **The descended pairing is symmetric.** -/
theorem neronTatePairingModTorsion_comm [W.toAffine.IsElliptic] (x y : PointModTorsion W) :
    neronTatePairingModTorsion W x y = neronTatePairingModTorsion W y x := by
  -- Both arguments are classes of representatives, where symmetry is `neronTatePairing_comm`.
  induction x using Submodule.Quotient.induction_on with
  | _ P =>
    induction y using Submodule.Quotient.induction_on with
    | _ Q => simpa using neronTatePairing_comm P Q

/-- **The descended pairing is symmetric**, as an equality of bilinear maps. -/
@[simp]
theorem neronTatePairingModTorsion_flip [W.toAffine.IsElliptic] :
    (neronTatePairingModTorsion W).flip = neronTatePairingModTorsion W :=
  (LinearMap.BilinMap.isSymm_iff_eq_flip.1 neronTatePairingModTorsion_comm).symm

/-! ### Positive definiteness -/

/-- **The descended pairing is non-negative on the diagonal**, the canonical height being so. -/
theorem neronTatePairingModTorsion_self_nonneg [W.toAffine.IsElliptic] (x : PointModTorsion W) :
    0 ≤ neronTatePairingModTorsion W x x := by
  induction x using Submodule.Quotient.induction_on with
  | _ P =>
    rw [neronTatePairingModTorsion_mk, neronTatePairing_self]
    exact P.canonicalHeight_nonneg

/-- **The descended pairing is positive definite**: its diagonal vanishes only at zero. This is
what dividing by the torsion buys, the canonical height vanishing exactly on the torsion. The
Northcott hypothesis is the one that makes height zero force torsion, and it is what
`Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder` consumes. -/
@[simp]
theorem neronTatePairingModTorsion_self_eq_zero_iff [W.toAffine.IsElliptic]
    [Northcott (Point.canonicalHeight (W := W))] (x : PointModTorsion W) :
    neronTatePairingModTorsion W x x = 0 ↔ x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ P =>
    rw [neronTatePairingModTorsion_mk, neronTatePairing_self,
      Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder, Submodule.Quotient.mk_eq_zero,
      ← AddCommGroup.mem_torsion, ← Submodule.torsion_int]
    exact Iff.rfl

/-! ### The Gram matrix -/

variable (W) in
/-- **The Gram matrix of the Néron-Tate pairing** in a basis of the quotient. -/
-- `LinearMap.toMatrix₂Aux` is the general-target combinator: its entries lie in the form's
-- codomain, so it applies here, where the scalars are `ℤ` and the values real.
-- `LinearMap.BilinForm.toMatrixAux` would not, a `BilinForm R M` having target `R`. The `Aux`
-- form takes the indexing family as a plain function, so no finiteness or decidable equality is
-- needed until a determinant is taken.
noncomputable def neronTateGramMatrix [W.toAffine.IsElliptic] {ι : Type*}
    (b : Module.Basis ι ℤ (PointModTorsion W)) : Matrix ι ι ℝ :=
  LinearMap.toMatrix₂Aux ℤ b b (neronTatePairingModTorsion W)

/-- Each Gram-matrix entry is the descended pairing of the corresponding basis vectors. -/
@[simp]
theorem neronTateGramMatrix_apply [W.toAffine.IsElliptic] {ι : Type*}
    (b : Module.Basis ι ℤ (PointModTorsion W)) (i j : ι) :
    neronTateGramMatrix W b i j = neronTatePairingModTorsion W (b i) (b j) := by
  simp [neronTateGramMatrix]

/-- **Reindexing the basis permutes the Gram matrix.** -/
@[simp]
theorem neronTateGramMatrix_reindex [W.toAffine.IsElliptic] {ι ι' : Type*}
    (b : Module.Basis ι ℤ (PointModTorsion W)) (σ : ι ≃ ι') :
    neronTateGramMatrix W (b.reindex σ) = (neronTateGramMatrix W b).submatrix σ.symm σ.symm := by
  ext i j
  simp [neronTateGramMatrix]

/-- **The Gram matrix is symmetric**, the pairing being so. -/
theorem isSymm_neronTateGramMatrix [W.toAffine.IsElliptic] {ι : Type*}
    (b : Module.Basis ι ℤ (PointModTorsion W)) : (neronTateGramMatrix W b).IsSymm := by
  ext i j
  simpa using neronTatePairingModTorsion_comm (b j) (b i)

end WeierstrassCurve.Affine
