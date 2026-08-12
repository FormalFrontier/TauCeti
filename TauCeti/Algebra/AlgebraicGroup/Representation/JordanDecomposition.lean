/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Equivalence
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.JordanDecomposition

/-!
# Jordan decomposition of algebraic-group points

Let `H` be a commutative Hopf algebra over a field `k`, and let `K` be a perfect extension
field. Every `K`-valued point `g` of the affine group represented by `H` acts on each
finite-dimensional `H`-comodule. The multiplicative Jordan decompositions of these actions are
natural in the comodule and compatible with tensor products, so Tannakian reconstruction turns
their semisimple and unipotent factors back into `K`-valued points of the original group.

This file defines those two reconstructed points. They commute, their product is `g`, and their
actions in every finite-dimensional representation are exactly the semisimple and unipotent parts
of the action of `g`. Thus the decomposition stays inside the affine group rather than merely
inside each ambient general linear group.

## Main declarations

* `TauCeti.HopfAlgebra.semisimplePart`: the semisimple part of an algebraic-group point.
* `TauCeti.HopfAlgebra.unipotentPart`: the unipotent part of an algebraic-group point.
* `TauCeti.HopfAlgebra.jordanDecomposition`: the ordered pair of the two parts.
* `TauCeti.HopfAlgebra.commute_semisimplePart_unipotentPart`: the two parts commute.
* `TauCeti.HopfAlgebra.semisimplePart_mul_unipotentPart`: their product is the original point.
* `TauCeti.HopfAlgebra.endOfPoint_semisimplePart` and
  `TauCeti.HopfAlgebra.endOfPoint_unipotentPart`: every finite-dimensional representation sees
  the corresponding linear Jordan factors.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u

variable (k H K : Type u) [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [Field K] [Algebra k K] [PerfectField K]

/-- The semisimple part of a point of an affine group over a perfect extension field.

It is reconstructed from the tensor automorphism whose component on every finite-dimensional
comodule is the semisimple part of the original point action. -/
noncomputable def semisimplePart (g : WithConv (H →ₐ[k] K)) : WithConv (H →ₐ[k] K) :=
  (Tannaka.fgPointTensorIsoEquiv k H K).symm
    (Tannaka.fgPointSemisimplePartTensorIso k H K g)

/-- The unipotent part of a point of an affine group over a perfect extension field.

It is reconstructed from the tensor automorphism whose component on every finite-dimensional
comodule is the unipotent part of the original point action. -/
noncomputable def unipotentPart (g : WithConv (H →ₐ[k] K)) : WithConv (H →ₐ[k] K) :=
  (Tannaka.fgPointTensorIsoEquiv k H K).symm
    (Tannaka.fgPointUnipotentPartTensorIso k H K g)

/-- The multiplicative Jordan decomposition of an algebraic-group point, with the semisimple
part first and the unipotent part second. -/
noncomputable def jordanDecomposition (g : WithConv (H →ₐ[k] K)) :
    WithConv (H →ₐ[k] K) × WithConv (H →ₐ[k] K) :=
  (semisimplePart k H K g, unipotentPart k H K g)

/-- The first component of a point's Jordan decomposition is its semisimple part. -/
@[simp]
theorem jordanDecomposition_fst (g : WithConv (H →ₐ[k] K)) :
    (jordanDecomposition k H K g).1 = semisimplePart k H K g :=
  (rfl)

/-- The second component of a point's Jordan decomposition is its unipotent part. -/
@[simp]
theorem jordanDecomposition_snd (g : WithConv (H →ₐ[k] K)) :
    (jordanDecomposition k H K g).2 = unipotentPart k H K g :=
  (rfl)

/-- The Tannakian action of the semisimple part is the semisimple-factor tensor
automorphism. -/
@[simp]
theorem fgPointTensorIso_semisimplePart (g : WithConv (H →ₐ[k] K)) :
    Tannaka.fgPointTensorIso k H K (semisimplePart k H K g) =
      Tannaka.fgPointSemisimplePartTensorIso k H K g := by
  rw [← Tannaka.fgPointTensorIsoEquiv_apply]
  exact (Tannaka.fgPointTensorIsoEquiv k H K).apply_symm_apply _

/-- The Tannakian action of the unipotent part is the unipotent-factor tensor
automorphism. -/
@[simp]
theorem fgPointTensorIso_unipotentPart (g : WithConv (H →ₐ[k] K)) :
    Tannaka.fgPointTensorIso k H K (unipotentPart k H K g) =
      Tannaka.fgPointUnipotentPartTensorIso k H K g := by
  rw [← Tannaka.fgPointTensorIsoEquiv_apply]
  exact (Tannaka.fgPointTensorIsoEquiv k H K).apply_symm_apply _

/-- In every finite-dimensional comodule, the reconstructed semisimple point acts by the
semisimple part of the original point action. -/
@[simp]
theorem endOfPoint_semisimplePart (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, u, u} k H) :
    Comodule.endOfPoint M (semisimplePart k H K g).ofConv =
      (GeneralLinearGroup.semisimplePart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
          Module.End K (K ⊗[k] M)) := by
  rw [← Comodule.pointsAction_toLinearMap,
    ← Tannaka.scalarExtensionComponent_fgPointTensorIso,
    fgPointTensorIso_semisimplePart,
    Tannaka.scalarExtensionComponent_fgPointSemisimplePartTensorIso]

/-- In every finite-dimensional comodule, the reconstructed unipotent point acts by the
unipotent part of the original point action. -/
@[simp]
theorem endOfPoint_unipotentPart (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, u, u} k H) :
    Comodule.endOfPoint M (unipotentPart k H K g).ofConv =
      (GeneralLinearGroup.unipotentPart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
          Module.End K (K ⊗[k] M)) := by
  rw [← Comodule.pointsAction_toLinearMap,
    ← Tannaka.scalarExtensionComponent_fgPointTensorIso,
    fgPointTensorIso_unipotentPart,
    Tannaka.scalarExtensionComponent_fgPointUnipotentPartTensorIso]

/-- As an element of the general linear group of any finite-dimensional comodule, the action of
the reconstructed semisimple point is the canonical semisimple part of the original action. -/
theorem ofLinearEquiv_pointsAction_semisimplePart (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, u, u} k H) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction M (semisimplePart k H K g)) =
      GeneralLinearGroup.semisimplePart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) := by
  apply Units.ext
  exact (Comodule.pointsAction_toLinearMap M (semisimplePart k H K g)).trans
    (endOfPoint_semisimplePart k H K g M)

/-- As an element of the general linear group of any finite-dimensional comodule, the action of
the reconstructed unipotent point is the canonical unipotent part of the original action. -/
theorem ofLinearEquiv_pointsAction_unipotentPart (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, u, u} k H) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction M (unipotentPart k H K g)) =
      GeneralLinearGroup.unipotentPart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) := by
  apply Units.ext
  exact (Comodule.pointsAction_toLinearMap M (unipotentPart k H K g)).trans
    (endOfPoint_unipotentPart k H K g M)

/-- The semisimple part acts semisimply in every finite-dimensional representation. -/
theorem isSemisimple_pointsAction_semisimplePart (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, u, u} k H) :
    GeneralLinearGroup.IsSemisimple
      (LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction M (semisimplePart k H K g))) := by
  rw [ofLinearEquiv_pointsAction_semisimplePart]
  exact GeneralLinearGroup.isSemisimple_semisimplePart _

/-- The unipotent part acts unipotently in every finite-dimensional representation. -/
theorem isUnipotent_pointsAction_unipotentPart (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, u, u} k H) :
    GeneralLinearGroup.IsUnipotent
      (LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction M (unipotentPart k H K g))) := by
  rw [ofLinearEquiv_pointsAction_unipotentPart]
  exact GeneralLinearGroup.isUnipotent_unipotentPart _

/-- The semisimple and unipotent parts of an algebraic-group point commute. -/
theorem commute_semisimplePart_unipotentPart (g : WithConv (H →ₐ[k] K)) :
    Commute (semisimplePart k H K g) (unipotentPart k H K g) := by
  rw [commute_iff_eq]
  apply (Tannaka.fgPointTensorIsoEquiv k H K).injective
  simp only [map_mul, Tannaka.fgPointTensorIsoEquiv_apply,
    fgPointTensorIso_semisimplePart, fgPointTensorIso_unipotentPart]
  exact (Tannaka.commute_fgPointSemisimplePartTensorIso_fgPointUnipotentPartTensorIso
    k H K g).eq

/-- Multiplying the semisimple and unipotent parts recovers the original algebraic-group
point. -/
@[simp]
theorem semisimplePart_mul_unipotentPart (g : WithConv (H →ₐ[k] K)) :
    semisimplePart k H K g * unipotentPart k H K g = g := by
  apply (Tannaka.fgPointTensorIsoEquiv k H K).injective
  simp only [map_mul, Tannaka.fgPointTensorIsoEquiv_apply,
    fgPointTensorIso_semisimplePart, fgPointTensorIso_unipotentPart,
    Tannaka.fgPointSemisimplePartTensorIso_mul_fgPointUnipotentPartTensorIso]
  rfl

end TauCeti.HopfAlgebra
