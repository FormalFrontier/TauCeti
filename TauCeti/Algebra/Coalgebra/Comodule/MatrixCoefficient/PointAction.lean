/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Unipotent
public import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Point actions and coefficient matrices

Let `M` be a finite free comodule over a coalgebra `C`. In a basis `b`, the matrix of the
endomorphism induced by an algebra-valued point `g : C →ₐ[R] A` is obtained by applying `g`
entrywise to the coefficient matrix of `M`. Thus the coefficient matrix records all point actions
simultaneously.

When `C` is a reduced finite-type commutative algebra over a field, its points valued in an
algebraically closed extension separate elements. It follows that the coefficient matrix is upper
triangular, or upper unitriangular, exactly when every point-action matrix has the corresponding
property. The reverse implications are the important ones: they lift a common invariant flag
found on geometric points to an actual flag by subcomodules.

## Main declarations

* `TauCeti.Comodule.toMatrix_endOfPoint`: the matrix of a point action is the evaluated
  coefficient matrix.
* `TauCeti.Comodule.charpoly_endOfPoint_comp`: characteristic polynomials of point actions
  commute with scalar extension.
* `TauCeti.Comodule.isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq`: a universal
  characteristic-polynomial identity makes every point action unipotent.
* `TauCeti.Comodule.coefficientMatrix_isUpperTriangular_iff_forall_toMatrix_endOfPoint`:
  pointwise detection of upper triangularity.
* `TauCeti.Comodule.coefficientMatrix_isUpperUnitriangular_iff_forall_toMatrix_endOfPoint`:
  pointwise detection of upper unitriangularity.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This is the point-separation bridge in Layer 5, "Lie–Kolchin; solvable groups", of the
ReductiveGroups roadmap. Lie–Kolchin produces a basis in which every geometric point acts
triangularly; for a unipotent group the diagonal characters are trivial, and the results here
turn that pointwise statement into the upper-unitriangular comodule flag used to embed the group
in `Uₙ`.
-/

public section

open Module

namespace TauCeti.Comodule

universe u v w x y

noncomputable section

section Matrix

variable {R : Type u} {C : Type v} {M : Type w} {A : Type x} {i : Type y}
variable [CommSemiring R] [Semiring C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [CommSemiring A] [Algebra R A]
variable [Fintype i] [DecidableEq i]

/-- The matrix of the endomorphism induced by an algebra-valued point is obtained by applying
that point entrywise to the comodule's coefficient matrix. The bases on the scalar extension are
the base changes of the chosen basis of the comodule. -/
@[simp]
theorem toMatrix_endOfPoint (b : Basis i R M) (g : C →ₐ[R] A) :
    LinearMap.toMatrix (b.baseChange A) (b.baseChange A) (endOfPoint M g) =
      (coefficientMatrix (C := C) b).map g := by
  ext p q
  rw [LinearMap.toMatrix_apply, Basis.baseChange_apply, Matrix.map_apply,
    endOfPoint_tmul, coact_basis_eq_sum_coefficientMatrix]
  simp [Finsupp.single_apply]

end Matrix

section Charpoly

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R] [Semiring C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Composing a point with a morphism of value algebras maps the characteristic polynomial of
its action along that morphism. -/
@[simp]
theorem charpoly_endOfPoint_comp [Module.Free R M] [Module.Finite R M]
    {B D : Type*} [CommRing B] [Algebra R B]
    [CommRing D] [Algebra R D] (g : C →ₐ[R] B) (f : B →ₐ[R] D) :
    (endOfPoint M (f.comp g)).charpoly = (endOfPoint M g).charpoly.map f := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [← LinearMap.charpoly_toMatrix (endOfPoint M (f.comp g)) (b.baseChange D),
    ← LinearMap.charpoly_toMatrix (endOfPoint M g) (b.baseChange B),
    toMatrix_endOfPoint, toMatrix_endOfPoint, ← Matrix.charpoly_map, Matrix.map_map]
  apply congrArg Matrix.charpoly
  ext p q
  simp [Matrix.map_apply]

/-- A universal `X - 1` characteristic-polynomial identity makes the action of every point on
the comodule unipotent. -/
theorem isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]
    [Module.Free k M] [Module.Finite k M] {L : Type x} [CommRing L] [Algebra k L]
    (g : WithConv (H →ₐ[k] L)) {ι : Type y} [Fintype ι] [DecidableEq ι] (b : Basis ι k M)
    (hCcharpoly : (coefficientMatrix (C := H) b).charpoly =
      ((Polynomial.X - (1 : Polynomial k)) ^ Module.finrank k M).map
        (algebraMap k H)) :
    LinearMap.GeneralLinearGroup.IsUnipotent
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (pointsAction M g)) := by
  let C := coefficientMatrix (C := H) b
  let d := Module.finrank k M
  let P : Polynomial k := (Polynomial.X - 1) ^ d
  have hgcharpoly : (endOfPoint M g.ofConv).charpoly =
      P.map (algebraMap k L) := by
    let e : H →ₐ[k] H := AlgHom.id k H
    calc
      (endOfPoint M g.ofConv).charpoly =
          (endOfPoint M e).charpoly.map g.ofConv := by
        simpa only [e, AlgHom.comp_id] using
          (charpoly_endOfPoint_comp e g.ofConv)
      _ = C.charpoly.map g.ofConv := by
        congr 1
        rw [← LinearMap.charpoly_toMatrix (endOfPoint M e) (b.baseChange H),
          toMatrix_endOfPoint]
        exact congrArg Matrix.charpoly (by
          simpa only [e, AlgHom.coe_id] using Matrix.map_id C)
      _ = _ := by
        rw [hCcharpoly, Polynomial.map_map]
        congr 1
        ext x
        exact g.ofConv.commutes x
  apply LinearMap.GeneralLinearGroup.isUnipotent_of_charpoly_eq (n := d)
  have hcoe :
      ((LinearMap.GeneralLinearGroup.ofLinearEquiv (pointsAction M g)) :
        Module.End _ _) = endOfPoint M g.ofConv :=
    pointsAction_toLinearMap M g
  rw [hcoe]
  exact hgcharpoly.trans (by simp [P])

end Charpoly

section PointSeparation

variable {k : Type u} {C : Type v} {M : Type w} {K : Type x} {i : Type y}
variable [Field k] [CommRing C] [Algebra k C] [Coalgebra k C]
variable [Algebra.FiniteType k C] [IsReduced C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]
variable [Field K] [Algebra k K] [IsAlgClosed K]
variable [Fintype i] [LinearOrder i]

/-- Over a reduced finite-type coordinate algebra, a coefficient matrix is upper triangular if
and only if every algebraically closed point-action matrix is upper triangular. -/
theorem coefficientMatrix_isUpperTriangular_iff_forall_toMatrix_endOfPoint
    (b : Basis i k M) :
    (coefficientMatrix (C := C) b).IsUpperTriangular ↔
      ∀ g : C →ₐ[k] K,
        (LinearMap.toMatrix (b.baseChange K) (b.baseChange K)
          (endOfPoint M g)).IsUpperTriangular := by
  constructor
  · intro h g
    rw [toMatrix_endOfPoint]
    exact h.map g
  · intro h p q hqp
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := K)
    intro g
    have hg := h g hqp
    rw [toMatrix_endOfPoint, Matrix.map_apply] at hg
    simpa using hg

/-- Over a reduced finite-type coordinate algebra, a coefficient matrix is upper unitriangular
if and only if every algebraically closed point-action matrix is upper unitriangular. -/
theorem coefficientMatrix_isUpperUnitriangular_iff_forall_toMatrix_endOfPoint
    (b : Basis i k M) :
    (coefficientMatrix (C := C) b).IsUpperUnitriangular ↔
      ∀ g : C →ₐ[k] K,
        (LinearMap.toMatrix (b.baseChange K) (b.baseChange K)
          (endOfPoint M g)).IsUpperUnitriangular := by
  constructor
  · intro h g
    rw [toMatrix_endOfPoint]
    exact h.map g
  · intro h
    rw [Matrix.isUpperUnitriangular_def]
    constructor
    · exact (coefficientMatrix_isUpperTriangular_iff_forall_toMatrix_endOfPoint b).2
        fun g ↦ (h g).isUpperTriangular
    · intro p
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := K)
      intro g
      have hg := (h g).apply_diag p
      rw [toMatrix_endOfPoint, Matrix.map_apply] at hg
      simpa using hg

end PointSeparation

end

end TauCeti.Comodule
