/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Analysis.Calculus.SecondDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Derivatives of extended coordinate changes

Mathlib represents the change from `β`-coordinates to `α`-coordinates by the
partial equivalence `I.extendCoordChange (chartAt H β) (chartAt H α)`. This
module develops the additional derivative formulas needed by manifold
calculus: its derivative is the tangent-coordinate change, its second
derivative is symmetric, and its first-derivative coordinate entries have the
expected derivative.

`extendCoordChange` is Mathlib's partial equivalence,
so its source, target, inverse, and invertibility API remain available without
translation lemmas.

The derivative entries below package the first and second coordinate derivatives used by
second-order coordinate equations. They use only the manifold structure, so no Riemannian metric
or vector bundle is required.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2, Section 2, Proposition 2.2
  (Birkhauser, 1992; ISBN 978-0-8176-3490-2).
* John M. Lee, *Introduction to Riemannian Manifolds*, Chapter 4, Proposition 4.7,
  equation (4.10) (2nd ed., Springer, 2018;
  [DOI 10.1007/978-3-319-91755-9](https://doi.org/10.1007/978-3-319-91755-9)).
-/

public section

noncomputable section

open Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Boundaryless

variable [I.Boundaryless]

/-- The extended coordinate change is `C^n` at every point of its source. -/
theorem contDiffAt_extendCoordChange {n : WithTop ℕ∞} [IsManifold I n M]
    {β α : M} {y : E}
    (hy : y ∈ (I.extendCoordChange (chartAt H β) (chartAt H α)).source) :
    ContDiffAt ℝ n (I.extendCoordChange (chartAt H β) (chartAt H α)) y := by
  have hsource : (I.extendCoordChange (chartAt H β) (chartAt H α)).source ∈ 𝓝 y := by
    have hsourceWithin :=
      I.extendCoordChange_source_mem_nhdsWithin
        (e := chartAt H β) (e' := chartAt H α) hy
    simpa only [I.range_eq_univ, nhdsWithin_univ] using hsourceWithin
  have hcont :=
    (contDiffOn_ext_coord_change (I := I) (n := n) α β).contDiffAt hsource
  simpa only [ModelWithCorners.extendCoordChange, extChartAt, PartialEquiv.coe_trans]
    using hcont

section FirstDerivative

variable [IsManifold I 1 M]

/-- The derivative of the extended coordinate change is the
tangent-coordinate change ([doCarmo1992]). -/
theorem hasFDerivAt_extendCoordChange {β α : M} {y : E}
    (hy : y ∈ (I.extendCoordChange (chartAt H β) (chartAt H α)).source) :
    HasFDerivAt (I.extendCoordChange (chartAt H β) (chartAt H α))
      (tangentCoordChange I β α ((extChartAt I β).symm y)) y := by
  have hmem := hy
  have hchange :
      I.extendCoordChange (chartAt H β) (chartAt H α) =
        (extChartAt I β).symm ≫ extChartAt I α := rfl
  rw [hchange, PartialEquiv.trans_source, PartialEquiv.symm_source,
    extChartAt_source] at hmem
  have hβ : (extChartAt I β).symm y ∈ (extChartAt I β).source := by
    simpa only [extChartAt_source] using (extChartAt I β).map_target hmem.1
  have hα : (extChartAt I β).symm y ∈ (extChartAt I α).source := by
    simpa only [extChartAt_source, mem_preimage] using hmem.2
  have hw := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hβ, hα⟩
  rw [I.range_eq_univ, (extChartAt I β).right_inv hmem.1] at hw
  simpa only [ModelWithCorners.extendCoordChange, extChartAt, PartialEquiv.coe_trans]
    using hasFDerivWithinAt_univ.mp hw

/-- The Frechet derivative of the extended coordinate change at a point of its
source. -/
theorem fderiv_extendCoordChange {β α : M} {y : E}
    (hy : y ∈ (I.extendCoordChange (chartAt H β) (chartAt H α)).source) :
    fderiv ℝ (I.extendCoordChange (chartAt H β) (chartAt H α)) y =
      tangentCoordChange I β α ((extChartAt I β).symm y) :=
  (hasFDerivAt_extendCoordChange (I := I) hy).fderiv

end FirstDerivative

end Boundaryless

section CoordinateEntries

variable [FiniteDimensional ℝ E]

/-- The coordinate entries of the first derivative of an extended coordinate
change. -/
def extendCoordChangeDeriv (β α : M) (a i : Fin (Module.finrank ℝ E))
    (y : E) : ℝ :=
  (Module.finBasis ℝ E).coord a
    (fderiv ℝ (I.extendCoordChange (chartAt H β) (chartAt H α)) y
      ((Module.finBasis ℝ E) i))

/-- The second-derivative coefficient of an extended coordinate change:
`∂²x^a/∂y^k∂y^i`. -/
def extendCoordChangeSndDeriv (β α : M)
    (a k i : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (Module.finBasis ℝ E).coord a
    (fderiv ℝ (fderiv ℝ (I.extendCoordChange (chartAt H β) (chartAt H α))) y
      ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) i))

section SecondDerivative

variable [I.Boundaryless] [IsManifold I 2 M]

/-- Schwarz symmetry of the extended coordinate change's second derivative:
`∂²x^a/∂y^k∂y^i = ∂²x^a/∂y^i∂y^k` on its source. -/
theorem extendCoordChangeSndDeriv_symm {β α : M} {y : E}
    (hy : y ∈ (I.extendCoordChange (chartAt H β) (chartAt H α)).source)
    (a k i : Fin (Module.finrank ℝ E)) :
    extendCoordChangeSndDeriv (I := I) β α a k i y =
      extendCoordChangeSndDeriv (I := I) β α a i k y := by
  have hcont : ContDiffAt ℝ 2 (I.extendCoordChange (chartAt H β) (chartAt H α)) y :=
    contDiffAt_extendCoordChange (I := I) hy
  have hsymm : IsSymmSndFDerivAt ℝ (I.extendCoordChange (chartAt H β) (chartAt H α)) y :=
    hcont.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField])
  rw [extendCoordChangeSndDeriv, extendCoordChangeSndDeriv, hsymm.eq]

/-- The matrix-entry function of the first derivative has partial derivatives
given by the second-derivative coefficients. -/
theorem hasFDerivAt_extendCoordChangeDeriv {β α : M} {y : E}
    (hy : y ∈ (I.extendCoordChange (chartAt H β) (chartAt H α)).source)
    (a i : Fin (Module.finrank ℝ E)) :
    HasFDerivAt (extendCoordChangeDeriv (I := I) β α a i)
      (((Module.finBasis ℝ E).coord a).toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).comp
          (fderiv ℝ (fderiv ℝ (I.extendCoordChange (chartAt H β) (chartAt H α))) y))) y := by
  have h2 := TauCeti.ContDiffAt.hasFDerivAt_fderiv
    (contDiffAt_extendCoordChange (I := I) hy) le_rfl
  have h3 :=
    ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).hasFDerivAt.comp
      y h2)
  exact ((Module.finBasis ℝ E).coord a).toContinuousLinearMap.hasFDerivAt.comp y h3

/-- The derivative of a first-coordinate entry, evaluated on a basis vector, is the corresponding
second-coordinate entry. -/
@[simp]
theorem fderiv_extendCoordChangeDeriv_apply {β α : M} {y : E}
    (hy : y ∈ (I.extendCoordChange (chartAt H β) (chartAt H α)).source)
    (a i k : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ (extendCoordChangeDeriv (I := I) β α a i) y)
        ((Module.finBasis ℝ E) k) =
      extendCoordChangeSndDeriv (I := I) β α a k i y := by
  rw [(hasFDerivAt_extendCoordChangeDeriv (I := I) hy a i).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    LinearMap.coe_toContinuousLinearMap', extendCoordChangeSndDeriv]

end SecondDerivative

end CoordinateEntries

end TauCeti.Manifold

end
