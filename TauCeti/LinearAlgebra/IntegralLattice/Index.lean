/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.Gram

/-!
# The determinant of a full sublattice

Whenever two integral lattices share their ambient rational form and the carrier of one lies
inside the carrier of the other, their invariants differ by the square of the index:

```text
det(L) = det(M) · [M : L]²,      disc(L) = disc(M) · [M : L]².
```

Nondegeneracy is not needed: in the degenerate case both determinants vanish and the equalities
are `0 = 0`.

Extending carrier bases of the two lattices to bases of the ambient rational space, the index is
the absolute determinant of the change-of-basis matrix by `AddSubgroup.relIndex_eq_abs_det`,
while the Gram determinants differ by the square of that same determinant because a bilinear
form's matrix transforms by congruence.

## Main results

* `TauCeti.IntegralLattice.determinant_eq_mul_relIndex_sq` and
  `TauCeti.IntegralLattice.discriminant_eq_mul_relIndex_sq`: the determinant and the discriminant
  of a full sublattice scale by the square of the index.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
-/

public section

open Matrix Module

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

open Classical in
/-- **The signed determinant of a full sublattice scales by the square of the index.** If two
integral lattices share their ambient rational form and one carrier lies inside the other, the
determinant of the smaller carrier `L.carrier` is the determinant of the larger carrier
`M.carrier` times the square of the index `[M : L]`. -/
theorem determinant_eq_mul_relIndex_sq (L M : IntegralLattice V) (hform : L.form = M.form)
    (hle : L.carrier ≤ M.carrier) :
    L.determinant =
      M.determinant * (L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup : ℤ) ^ 2 := by
  classical
  let bM : Basis (Module.Free.ChooseBasisIndex ℤ M) ℤ M := Module.Free.chooseBasis ℤ M
  let eM := bM.extendOfIsLattice ℚ
  let σ := (Module.Free.chooseBasis ℤ L).extendOfIsLattice ℚ |>.indexEquiv eM
  let bL : Basis (Module.Free.ChooseBasisIndex ℤ M) ℤ L :=
    (Module.Free.chooseBasis ℤ L).reindex σ
  let eL := bL.extendOfIsLattice ℚ
  have hidx : ((L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup : ℕ) : ℚ)
      = |eM.det eL| :=
    AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hle) eL eM
      (Submodule.IsLattice.toAddSubgroup_eq_closure_range_extendOfIsLattice bL)
      (Submodule.IsLattice.toAddSubgroup_eq_closure_range_extendOfIsLattice bM)
  have hmat : (eM.toMatrix eL)ᵀ * LinearMap.BilinForm.toMatrix eM L.form * eM.toMatrix eL
      = LinearMap.BilinForm.toMatrix eL L.form :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := eM) eL L.form
  have hdetL : (L.determinant : ℚ) = Matrix.det (LinearMap.BilinForm.toMatrix eL L.form) := by
    rw [L.determinant_eq_gramDet bL, L.intCast_gramDet bL]
  have hdetM : (M.determinant : ℚ) = Matrix.det (LinearMap.BilinForm.toMatrix eM L.form) := by
    rw [M.determinant_eq_gramDet bM, M.intCast_gramDet bM, hform]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hdetL, ← hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hdetM,
    ← Basis.det_apply, hidx]
  rw [sq_abs]
  ring

/-- **The discriminant of a full sublattice scales by the square of the index.** -/
theorem discriminant_eq_mul_relIndex_sq (L M : IntegralLattice V) (hform : L.form = M.form)
    (hle : L.carrier ≤ M.carrier) :
    L.discriminant =
      M.discriminant * (L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup) ^ 2 := by
  rw [discriminant_def, discriminant_def, L.determinant_eq_mul_relIndex_sq M hform hle,
    Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]

end IntegralLattice

end TauCeti
