/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# The orthogonal subgroup scheme of `GLₙ`

For a commutative ring `R` and `n : ℕ`, the orthogonal subgroup scheme `Oₙ` of `GL n` is the
subgroup scheme preserving the constant form `1`: the specialization of
`TauCeti.ConstantForm` at `C = 1`, cut out of `GL n` by the entries of

```text
X Xᵀ - 1
```

for `X` the localized generic matrix. On every commutative `R`-algebra `A`, its group of points
is Mathlib's existing group `Matrix.orthogonalGroup (Fin n) A` of matrices with `M * Mᵀ = 1`,
and that identification is what this file adds to the general construction.

This is the orthogonal group of the **standard symmetric bilinear form**, the scheme of the
functor `A ↦ {M | M Mᵀ = 1}` over every commutative ring. It is the classical worked example in
every characteristic except two, where the bilinear-form and quadratic-form orthogonal groups
differ and smoothness becomes sensitive to the rank and regularity of the form; no smoothness
is claimed here, so the construction is stated over an arbitrary commutative ring without
restriction. This is the ambient stage of the `SOₙ` worked example of the ReductiveGroups
roadmap, built at the same boundary as the symplectic example (`TauCeti.Symplectic`):
construction and points identification, with no smoothness or reductivity claim. The
determinant-one cut `SOₙ` itself is built on top of this file in `TauCeti.SpecialOrthogonal`.

The Hopf-ideal closure conditions, the quotient, the group scheme with its closed immersion
into `GLₙ`, and the ambient membership criterion `M C Mᵀ = C` all come from
`TauCeti.ConstantForm`, which proves them for an arbitrary constant matrix `C` (local finite
type is the generic instance for Hopf-ideal quotients of the `GLₙ` coordinate algebra); the
specializations below fix `C = 1` and the constant form becomes the identity matrix in every
value algebra. The construction includes `n = 0` and the zero ring.

## Main declarations

* `TauCeti.Orthogonal.relationMatrix`: the matrix of defining relations `X Xᵀ - 1`.
* `TauCeti.Orthogonal.definingHopfIdeal`: the Hopf ideal its entries generate.
* `TauCeti.Orthogonal.coordinateHopfAlgebra`: the orthogonal coordinate Hopf algebra, the
  quotient by the defining Hopf ideal.
* `TauCeti.Orthogonal.groupScheme` and `TauCeti.Orthogonal.inclusion`: the orthogonal subgroup
  scheme and its closed immersion into the general linear group scheme.
* `TauCeti.Orthogonal.pointsMulEquiv`: the group of algebra-valued points of the orthogonal
  coordinate Hopf algebra is `Matrix.orthogonalGroup (Fin n) A`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3, where `Oₙ` is introduced among the basic
  examples of algebraic groups as the subgroup of `GLₙ` cut out by the entries of the standard
  form relation.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), Chapter 1, for the
  orthogonal group as a representable functor on commutative rings.
* The Stacks Project, [Tag 022W](https://stacks.math.columbia.edu/tag/022W), for the ambient
  general linear group scheme.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.Orthogonal

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The orthogonal specialization of the constant-form construction -/

/-- **The matrix of defining relations** of the orthogonal subgroup scheme: `X Xᵀ - 1` over the
coordinate Hopf algebra of `GL n`, the constant-form relation matrix at `C = 1`. -/
noncomputable abbrev relationMatrix :
    Matrix (Fin n) (Fin n) (GeneralLinear.coordinateHopfAlgebra R n) :=
  ConstantForm.relationMatrix R n 1

/-- The set of defining relations: the entries of the relation matrix. -/
abbrev relationSet : Set (GeneralLinear.coordinateHopfAlgebra R n) :=
  ConstantForm.relationSet R n 1

/-- **The orthogonal Hopf ideal**: the ideal of the coordinate Hopf algebra of `GL n` generated
by the entries of `X Xᵀ - 1`. -/
noncomputable abbrev definingHopfIdeal :
    HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n) :=
  ConstantForm.definingHopfIdeal R n 1

/-- The coordinate Hopf algebra of the orthogonal subgroup scheme of `GL n`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  ConstantForm.coordinateHopfAlgebra R n 1

/-- The orthogonal subgroup scheme of `GL n`. -/
noncomputable abbrev groupScheme := ConstantForm.groupScheme R n 1

/-- The closed-subgroup inclusion from the orthogonal subgroup scheme into the named general
linear group scheme. -/
noncomputable abbrev inclusion : groupScheme R n ⟶ GeneralLinear.groupScheme R n :=
  ConstantForm.inclusion R n 1

/-! ### Algebra-valued points -/

section Points

-- `Matrix.orthogonalGroup` reads the transpose as a `star`, through the trivial star structure
-- on the commutative coefficient ring, exactly as in `Mathlib.LinearAlgebra.UnitaryGroup`.
attribute [local instance] starRingOfComm

variable {A : Type w} [CommRing A] [Algebra R A]

/-- An ambient point belongs to the subgroup cut out by the orthogonal Hopf ideal exactly when
its matrix is orthogonal. This is the ambient membership criterion that further cuts consume;
the determinant-one cut (`TauCeti.SpecialOrthogonal`) combines it with the special-linear
one. -/
@[simp]
theorem mem_definingPointsSubgroup_iff
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
        (CommAlgCat.of R A) ↔
      (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) ∈
        Matrix.orthogonalGroup (Fin n) A := by
  rw [ConstantForm.mem_definingPointsSubgroup_iff,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mem_orthogonalGroup_iff]

/-- Read a cut-out ambient point as an orthogonal matrix. -/
private noncomputable def pointsSubgroupToOrthogonalGroup
    (g : CommHopfAlgCat.quotientPointsSubgroup
      (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
      (CommAlgCat.of R A)) : Matrix.orthogonalGroup (Fin n) A :=
  ⟨(GeneralLinear.pointsMulEquiv n g.1 : Matrix (Fin n) (Fin n) A),
    (mem_definingPointsSubgroup_iff R n g.1).mp g.2⟩

/-- Regard an orthogonal matrix as a point in the cut-out ambient subgroup, through the unit
`Unitary.toUnits` it defines in the matrix ring. -/
private noncomputable def orthogonalGroupToPointsSubgroup
    (g : Matrix.orthogonalGroup (Fin n) A) :
    CommHopfAlgCat.quotientPointsSubgroup
      (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
      (CommAlgCat.of R A) :=
  ⟨(GeneralLinear.pointsMulEquiv (R := R) (A := A) n).symm (Unitary.toUnits g),
    (mem_definingPointsSubgroup_iff R n _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact Unitary.val_toUnits_apply g ▸ g.2)⟩

/-- The unit attached to an orthogonal matrix wrapped from a general linear element is that
element: both have the same underlying matrix. -/
theorem toUnits_mk (M : GL (Fin n) A)
    (h : (M : Matrix (Fin n) (Fin n) A) ∈ Matrix.orthogonalGroup (Fin n) A) :
    Unitary.toUnits (⟨(M : Matrix (Fin n) (Fin n) A), h⟩ :
        Matrix.orthogonalGroup (Fin n) A) = M :=
  Units.ext (Unitary.val_toUnits_apply _)

/-- The subgroup of `GL n (A)` cut out by the orthogonal Hopf ideal is
`Matrix.orthogonalGroup (Fin n) A`. -/
private noncomputable def definingPointsSubgroupMulEquiv :
    CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
        (CommAlgCat.of R A) ≃*
      Matrix.orthogonalGroup (Fin n) A where
  toFun := pointsSubgroupToOrthogonalGroup R n
  invFun := orthogonalGroupToPointsSubgroup R n
  left_inv g := by
    apply Subtype.ext
    unfold orthogonalGroupToPointsSubgroup pointsSubgroupToOrthogonalGroup
    dsimp only
    rw [toUnits_mk, MulEquiv.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    unfold pointsSubgroupToOrthogonalGroup orthogonalGroupToPointsSubgroup
    dsimp only
    rw [MulEquiv.apply_symm_apply]
    exact Unitary.val_toUnits_apply g
  map_mul' g h :=
    Subtype.ext (congrArg (fun M : GL (Fin n) A => (M : Matrix (Fin n) (Fin n) A))
      (map_mul (GeneralLinear.pointsMulEquiv (R := R) (A := A) n) g.1 h.1))

/-- **The points identification**: the group of algebra-valued points of the orthogonal
coordinate Hopf algebra is the orthogonal group of the value algebra. -/
noncomputable def pointsMulEquiv :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A) ≃*
      Matrix.orthogonalGroup (Fin n) A :=
  ((CommHopfAlgCat.quotientPointsSubgroupNatIso
      (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)).app
      (CommAlgCat.of R A)).groupIsoToMulEquiv.trans
    (definingPointsSubgroupMulEquiv R n)

/-- Internally, the orthogonal point equivalence first forms the cut-out ambient subgroup point
and then reads it as an orthogonal matrix. -/
private theorem pointsMulEquiv_apply_eq
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    pointsMulEquiv R n (A := A) f =
      pointsSubgroupToOrthogonalGroup R n
        (((CommHopfAlgCat.quotientPointsSubgroupNatIso
          (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)).app
          (CommAlgCat.of R A)).hom f) :=
  rfl

/-- Under the orthogonal and general-linear point equivalences, the quotient-point inclusion is
the ordinary inclusion of orthogonal matrices into `GL n`. -/
theorem pointsMulEquiv_coe
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    ((GeneralLinear.pointsMulEquiv n
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
          (CommAlgCat.of R A) f) : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      (pointsMulEquiv R n (A := A) f : Matrix (Fin n) (Fin n) A) := by
  have hcomponent := CommHopfAlgCat.quotientPointsSubgroupNatIso_hom_app_apply
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
    (CommAlgCat.of R A) f
  rw [pointsMulEquiv_apply_eq]
  exact congrArg
    (fun g => (pointsSubgroupToOrthogonalGroup R n g : Matrix (Fin n) (Fin n) A))
    hcomponent.symm

/-- The ambient point attached to an orthogonal matrix is the general-linear point attached to
its unit. -/
@[simp]
theorem quotientPointsHom_pointsMulEquiv_symm (g : Matrix.orthogonalGroup (Fin n) A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
        (CommAlgCat.of R A) ((pointsMulEquiv R n (A := A)).symm g) =
      (GeneralLinear.pointsMulEquiv (R := R) (A := A) n).symm (Unitary.toUnits g) := by
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) n).injective
  apply Units.ext
  rw [MulEquiv.apply_symm_apply, Unitary.val_toUnits_apply,
    pointsMulEquiv_coe R n, MulEquiv.apply_symm_apply]

end Points

end TauCeti.Orthogonal
