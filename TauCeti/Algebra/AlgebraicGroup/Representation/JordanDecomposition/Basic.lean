/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Equivalence
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.JordanDecomposition
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
import TauCeti.LinearAlgebra.GeneralLinearGroup.Intertwining

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

* `TauCeti.HopfAlgebra.Point.semisimplePart`: the semisimple part of an algebraic-group point.
* `TauCeti.HopfAlgebra.Point.unipotentPart`: the unipotent part of an algebraic-group point.
* `TauCeti.HopfAlgebra.Point.jordanDecomposition`: the ordered pair of the two parts.
* `TauCeti.HopfAlgebra.Point.jordanDecomposition_spec`: the defining properties of the ordered
  decomposition.
* `TauCeti.HopfAlgebra.Point.isSemisimple_isUnipotent_unique`: uniqueness of a commuting
  semisimple-unipotent factorization.
* `TauCeti.HopfAlgebra.Point.eq_jordanDecomposition_iff`: characterization of the canonical
  ordered pair.
* `TauCeti.HopfAlgebra.Point.commute_semisimplePart_unipotentPart`: the two parts commute.
* `TauCeti.HopfAlgebra.Point.semisimplePart_mul_unipotentPart`: their product is the original
  point.
* `TauCeti.HopfAlgebra.Point.endOfPoint_semisimplePart` and
  `TauCeti.HopfAlgebra.Point.endOfPoint_unipotentPart`: every finite-dimensional representation
  sees the corresponding linear Jordan factors.
* `TauCeti.HopfAlgebra.Point.isUnipotentPoint_iff_unipotentPart_eq_self` and
  `TauCeti.HopfAlgebra.Point.isUnipotentPoint_iff_semisimplePart_eq_one`: pointwise
  characterizations of unipotence by the Jordan factors.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open LinearMap WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra
namespace Point

universe u

variable (k H K : Type u) [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [Field K] [Algebra k K] [PerfectField K]

/-- The semisimple part of a point of an affine group over a perfect extension field.

It is reconstructed from the tensor automorphism whose component on every finite-dimensional
comodule is the semisimple part of the original point action. -/
noncomputable def semisimplePart (g : WithConv (H →ₐ[k] K)) : WithConv (H →ₐ[k] K) :=
  (Tannaka.fgPointTensorIsoEquiv k H K).symm
    (Tannaka.fgPointSemisimplePartTensorIso k H K g)

/-- The semisimple part is reconstructed from the semisimple-factor tensor automorphism. -/
theorem semisimplePart_def (g : WithConv (H →ₐ[k] K)) :
    semisimplePart k H K g =
      (Tannaka.fgPointTensorIsoEquiv k H K).symm
        (Tannaka.fgPointSemisimplePartTensorIso k H K g) :=
  (rfl)

/-- The unipotent part of a point of an affine group over a perfect extension field.

It is reconstructed from the tensor automorphism whose component on every finite-dimensional
comodule is the unipotent part of the original point action. -/
noncomputable def unipotentPart (g : WithConv (H →ₐ[k] K)) : WithConv (H →ₐ[k] K) :=
  (Tannaka.fgPointTensorIsoEquiv k H K).symm
    (Tannaka.fgPointUnipotentPartTensorIso k H K g)

/-- The unipotent part is reconstructed from the unipotent-factor tensor automorphism. -/
theorem unipotentPart_def (g : WithConv (H →ₐ[k] K)) :
    unipotentPart k H K g =
      (Tannaka.fgPointTensorIsoEquiv k H K).symm
        (Tannaka.fgPointUnipotentPartTensorIso k H K g) :=
  (rfl)

/-- The multiplicative Jordan decomposition of an algebraic-group point, with the semisimple
part first and the unipotent part second. -/
noncomputable def jordanDecomposition (g : WithConv (H →ₐ[k] K)) :
    WithConv (H →ₐ[k] K) × WithConv (H →ₐ[k] K) :=
  (semisimplePart k H K g, unipotentPart k H K g)

/-- The first component of the Jordan decomposition is the semisimple part. -/
@[simp]
theorem jordanDecomposition_fst (g : WithConv (H →ₐ[k] K)) :
    (jordanDecomposition k H K g).1 = semisimplePart k H K g :=
  (rfl)

/-- The second component of the Jordan decomposition is the unipotent part. -/
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
  rw [semisimplePart_def, Tannaka.fgPointTensorIsoEquiv_symm_apply,
    Tannaka.endOfPoint_reconstructedPoint,
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
  rw [unipotentPart_def, Tannaka.fgPointTensorIsoEquiv_symm_apply,
    Tannaka.endOfPoint_reconstructedPoint,
    Tannaka.scalarExtensionComponent_fgPointUnipotentPartTensorIso]

/-- As an element of the general linear group of any finite-dimensional comodule, the action of
the reconstructed semisimple point is the canonical semisimple part of the original action. -/
@[simp]
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
@[simp]
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
  refine Commute.of_map (Tannaka.fgPointTensorIsoEquiv k H K).injective ?_
  simp only [Tannaka.fgPointTensorIsoEquiv_apply, fgPointTensorIso_semisimplePart,
    fgPointTensorIso_unipotentPart]
  exact Tannaka.commute_fgPointSemisimplePartTensorIso_fgPointUnipotentPartTensorIso k H K g

/-- Multiplying the semisimple and unipotent parts recovers the original algebraic-group
point. -/
@[simp]
theorem semisimplePart_mul_unipotentPart (g : WithConv (H →ₐ[k] K)) :
    semisimplePart k H K g * unipotentPart k H K g = g := by
  apply (Tannaka.fgPointTensorIsoEquiv k H K).injective
  simp only [map_mul, Tannaka.fgPointTensorIsoEquiv_apply,
    fgPointTensorIso_semisimplePart, fgPointTensorIso_unipotentPart,
    Tannaka.fgPointSemisimplePartTensorIso_mul_fgPointUnipotentPartTensorIso]
  -- Both sides are now the same point-induced tensor automorphism; the remaining equality is
  -- only between the instance paths selected by the two constructions.
  rfl

/-- A commuting factorization of a point into factors acting semisimply and unipotently in every
finite-dimensional comodule is its canonical Jordan decomposition. -/
theorem isSemisimple_isUnipotent_unique (g s u : WithConv (H →ₐ[k] K))
    (hc : Commute s u) (hmul : s * u = g)
    (hs : ∀ M : FGComoduleCat.{u, u, u} k H,
      GeneralLinearGroup.IsSemisimple
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M s)))
    (hu : IsUnipotentPoint u) :
    s = semisimplePart k H K g ∧ u = unipotentPart k H K g := by
  have h_unique (M : FGComoduleCat.{u, u, u} k H) :
      LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M s) =
          LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M (semisimplePart k H K g)) ∧
        LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M u) =
          LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M (unipotentPart k H K g)) := by
    apply GeneralLinearGroup.isSemisimple_isUnipotent_unique
    · exact hs M
    · exact (isUnipotentPoint_def u).mp hu M
    · exact (GeneralLinearGroup.commute_ofLinearEquiv_iff _ _).2
        (hc.map (Comodule.pointsAction M))
    · exact isSemisimple_pointsAction_semisimplePart k H K g M
    · exact isUnipotent_pointsAction_unipotentPart k H K g M
    · exact (GeneralLinearGroup.commute_ofLinearEquiv_iff _ _).2
        ((commute_semisimplePart_unipotentPart k H K g).map (Comodule.pointsAction M))
    · rw [← LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
        ← LinearMap.GeneralLinearGroup.ofLinearEquiv_mul, ← map_mul, ← map_mul, hmul,
        semisimplePart_mul_unipotentPart]
  constructor
  · apply Tannaka.fgPoint_ext_of_forall_ofLinearEquiv_pointsAction k H K
    intro M
    exact (h_unique M).1
  · apply Tannaka.fgPoint_ext_of_forall_ofLinearEquiv_pointsAction k H K
    intro M
    exact (h_unique M).2

/-- The canonical point-level Jordan decomposition has the defining semisimple, unipotent,
commutation, and product properties. -/
theorem jordanDecomposition_spec (g : WithConv (H →ₐ[k] K)) :
    (∀ M : FGComoduleCat.{u, u, u} k H,
      GeneralLinearGroup.IsSemisimple
        (LinearMap.GeneralLinearGroup.ofLinearEquiv
          (Comodule.pointsAction M (jordanDecomposition k H K g).1))) ∧
      IsUnipotentPoint (jordanDecomposition k H K g).2 ∧
      Commute (jordanDecomposition k H K g).1 (jordanDecomposition k H K g).2 ∧
      g = (jordanDecomposition k H K g).1 * (jordanDecomposition k H K g).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M
    exact isSemisimple_pointsAction_semisimplePart k H K g M
  · rw [isUnipotentPoint_def]
    intro M
    exact isUnipotent_pointsAction_unipotentPart k H K g M
  · exact commute_semisimplePart_unipotentPart k H K g
  · exact (semisimplePart_mul_unipotentPart k H K g).symm

/-- A pair is the canonical point-level Jordan decomposition exactly when it is a commuting
semisimple-unipotent factorization in every finite-dimensional comodule. -/
theorem eq_jordanDecomposition_iff (g s u : WithConv (H →ₐ[k] K)) :
    (s, u) = jordanDecomposition k H K g ↔
      (∀ M : FGComoduleCat.{u, u, u} k H,
        GeneralLinearGroup.IsSemisimple
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M s))) ∧
      IsUnipotentPoint u ∧
      Commute s u ∧ g = s * u := by
  constructor
  · intro h
    have hs : s = (jordanDecomposition k H K g).1 := congrArg Prod.fst h
    have hu : u = (jordanDecomposition k H K g).2 := congrArg Prod.snd h
    subst s
    subst u
    exact jordanDecomposition_spec k H K g
  · intro h
    have h_unique := isSemisimple_isUnipotent_unique k H K g s u h.2.2.1 h.2.2.2.symm
      h.1 h.2.1
    exact Prod.ext h_unique.1 h_unique.2

/-- A point acting semisimply in every finite-dimensional comodule is its own semisimple part. -/
@[simp]
theorem semisimplePart_eq_self {g : WithConv (H →ₐ[k] K)}
    (hg : ∀ M : FGComoduleCat.{u, u, u} k H,
      GeneralLinearGroup.IsSemisimple
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))) :
    semisimplePart k H K g = g :=
  ((isSemisimple_isUnipotent_unique k H K g g 1 (Commute.one_right g) (mul_one g) hg
    (isUnipotentPoint_one (k := k) (H := H) (K := K))).1).symm

/-- A point acting semisimply in every finite-dimensional comodule has trivial unipotent part. -/
@[simp]
theorem unipotentPart_eq_one_of_isSemisimple {g : WithConv (H →ₐ[k] K)}
    (hg : ∀ M : FGComoduleCat.{u, u, u} k H,
      GeneralLinearGroup.IsSemisimple
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))) :
    unipotentPart k H K g = 1 :=
  ((isSemisimple_isUnipotent_unique k H K g g 1 (Commute.one_right g) (mul_one g) hg
    (isUnipotentPoint_one (k := k) (H := H) (K := K))).2).symm

/-- A point acting unipotently in every finite-dimensional comodule has trivial semisimple part. -/
@[simp]
theorem semisimplePart_eq_one_of_isUnipotent {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotentPoint g) :
    semisimplePart k H K g = 1 :=
  ((isSemisimple_isUnipotent_unique k H K g 1 g (Commute.one_left g) (one_mul g)
    (by intro M; rw [map_one]; exact GeneralLinearGroup.isSemisimple_one) hg).1).symm

/-- A point acting unipotently in every finite-dimensional comodule is its own unipotent part. -/
@[simp]
theorem unipotentPart_eq_self {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotentPoint g) :
    unipotentPart k H K g = g :=
  ((isSemisimple_isUnipotent_unique k H K g 1 g (Commute.one_left g) (one_mul g)
    (by intro M; rw [map_one]; exact GeneralLinearGroup.isSemisimple_one) hg).2).symm

/-- A point is unipotent exactly when its unipotent part is the point itself. -/
theorem isUnipotentPoint_iff_unipotentPart_eq_self (g : WithConv (H →ₐ[k] K)) :
    IsUnipotentPoint g ↔ unipotentPart k H K g = g := by
  constructor
  · exact unipotentPart_eq_self k H K
  · intro hg
    rw [isUnipotentPoint_def]
    intro M
    rw [← hg]
    exact isUnipotent_pointsAction_unipotentPart k H K g M

/-- A point is unipotent exactly when its semisimple part is the identity. -/
theorem isUnipotentPoint_iff_semisimplePart_eq_one (g : WithConv (H →ₐ[k] K)) :
    IsUnipotentPoint g ↔ semisimplePart k H K g = 1 := by
  constructor
  · exact semisimplePart_eq_one_of_isUnipotent k H K
  · intro hg
    rw [isUnipotentPoint_iff_unipotentPart_eq_self]
    calc
      unipotentPart k H K g = 1 * unipotentPart k H K g := (one_mul _).symm
      _ = semisimplePart k H K g * unipotentPart k H K g := by rw [hg]
      _ = g := semisimplePart_mul_unipotentPart k H K g

/-- The semisimple part of the identity point is the identity. -/
theorem semisimplePart_one :
    semisimplePart k H K (1 : WithConv (H →ₐ[k] K)) = 1 :=
  semisimplePart_eq_self k H K
    (by intro M; rw [map_one]; exact GeneralLinearGroup.isSemisimple_one)

/-- The unipotent part of the identity point is the identity. -/
theorem unipotentPart_one :
    unipotentPart k H K (1 : WithConv (H →ₐ[k] K)) = 1 :=
  unipotentPart_eq_self k H K
    (isUnipotentPoint_one (k := k) (H := H) (K := K))

end Point
end TauCeti.HopfAlgebra
