/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# The orthogonal subgroup scheme of `GLₙ`

For a commutative ring `R` and `n : ℕ`, the entries of the matrix relation

```text
X Xᵀ - 1
```

— `X` the localized generic matrix of `GL n` — generate a Hopf ideal in the coordinate Hopf
algebra of `GL n`. Its quotient represents the closed subgroup scheme `Oₙ` of orthogonal
matrices. On every commutative `R`-algebra `A`, its group of points is Mathlib's existing
group `Matrix.orthogonalGroup (Fin n) A` of matrices with `M * Mᵀ = 1`.

This is the orthogonal group of the **standard symmetric bilinear form**, the scheme of the
functor `A ↦ {M | M Mᵀ = 1}` over every commutative ring. It is the classical worked example in
every characteristic except two, where the quadratic-form orthogonal group (which is the smooth
object) differs from it; no smoothness is claimed here, so the construction is stated over an
arbitrary commutative ring without restriction. This is the ambient stage of the `SOₙ` worked
example of the ReductiveGroups roadmap, built at the same boundary as the symplectic example
(`TauCeti.Symplectic`): construction and points identification, with no smoothness or
reductivity claim. The determinant-one cut `SOₙ` itself is the immediate follow-up on top of
this file.

The three Hopf-ideal closure conditions are proved by matrix algebra rather than coordinate by
coordinate, specializing the computations of the symplectic example to the constant form `1`.
Writing `f := X Xᵀ - 1` for the matrix of generators and mapping it entrywise through the
relevant algebra morphisms:

* the counit sends `X` to the identity matrix, so it sends `f` to `1 * 1ᵀ - 1 = 0`;
* the comultiplication sends `X` to `Y Z`, where `Y` and `Z` are the two tensor inclusions of
  `X`, and

  ```text
  (Y Z) (Y Z)ᵀ - 1 = Y (Z Zᵀ - 1) Yᵀ + (Y Yᵀ - 1),
  ```

  whose two summands are the right and left tensor inclusions of `f` framed by matrices, so
  every entry lies in the right or left tensor ideal;
* the antipode sends `X` to its inverse matrix, and

  ```text
  X⁻¹ (X⁻¹)ᵀ - 1 = -(X⁻¹ (X Xᵀ - 1) (X⁻¹)ᵀ),
  ```

  so every entry of the antipode image is a combination of the generators.

The construction includes `n = 0` and the zero ring.

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

The matrix form of the closure computations follows `TauCeti.Symplectic` (there for the
alternating form `J`, here for the constant form `1`); the framing identities are recorded in
the module docstring.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.Orthogonal

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The defining relation matrix -/

/-- The localized generic matrix of `GL n`, read in the bundled coordinate Hopf algebra. -/
noncomputable def genericMatrix :
    Matrix (Fin n) (Fin n) (GeneralLinear.coordinateHopfAlgebra R n) :=
  (GeneralLinear.localizedGenericMatrix R n).map
    (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n)

/-- An entry of the bundled generic matrix is the bundled image of the corresponding polynomial
generator. -/
theorem genericMatrix_apply (i j : Fin n) :
    genericMatrix R n i j =
      GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
        (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j))) := by
  rw [genericMatrix, Matrix.map_apply, GeneralLinear.localizedGenericMatrix_apply]

/-- The inverse of the localized generic matrix, read in the bundled coordinate Hopf algebra. -/
private noncomputable def genericMatrixInv :
    Matrix (Fin n) (Fin n) (GeneralLinear.coordinateHopfAlgebra R n) :=
  ((GeneralLinear.localizedGenericMatrix R n)⁻¹).map
    (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n)

/-- The bundled generic matrix and its bundled inverse multiply to the identity. -/
private theorem genericMatrix_mul_genericMatrixInv :
    genericMatrix R n * genericMatrixInv R n = 1 := by
  rw [genericMatrix, genericMatrixInv, ← Matrix.map_mul,
    Matrix.mul_nonsing_inv _ (GeneralLinear.isUnit_det_localizedGenericMatrix R n)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- The bundled inverse and the bundled generic matrix multiply to the identity. -/
private theorem genericMatrixInv_mul_genericMatrix :
    genericMatrixInv R n * genericMatrix R n = 1 := by
  rw [genericMatrix, genericMatrixInv, ← Matrix.map_mul,
    Matrix.nonsing_inv_mul _ (GeneralLinear.isUnit_det_localizedGenericMatrix R n)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- **The matrix of defining relations** of the orthogonal subgroup scheme:
`X Xᵀ - 1` over the coordinate Hopf algebra of `GL n`. -/
noncomputable def relationMatrix :
    Matrix (Fin n) (Fin n) (GeneralLinear.coordinateHopfAlgebra R n) :=
  genericMatrix R n * (genericMatrix R n)ᵀ - 1

/-- The set of defining relations: the entries of the relation matrix. -/
def relationSet : Set (GeneralLinear.coordinateHopfAlgebra R n) :=
  Set.range fun ij : Fin n × Fin n => relationMatrix R n ij.1 ij.2

/-- Every entry of the relation matrix is a defining relation. -/
theorem relationMatrix_mem_relationSet (i j : Fin n) :
    relationMatrix R n i j ∈ relationSet R n :=
  ⟨(i, j), rfl⟩

/-- Mapping the relation matrix through an algebra morphism gives the relation of the images:
the generic matrix maps entrywise, and the constant matrix `1` maps to `1`. -/
private theorem relationMatrix_map {T : Type*} [CommRing T] [Algebra R T]
    (phi : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] T) :
    (relationMatrix R n).map phi =
      (genericMatrix R n).map phi * ((genericMatrix R n).map phi)ᵀ - 1 := by
  rw [relationMatrix, Matrix.map_sub _ (fun a b => map_sub phi a b), Matrix.map_mul,
    Matrix.transpose_map, Matrix.map_one _ (map_zero phi) (map_one phi)]

/-- An entry of a framed relation matrix `P (X Xᵀ - 1) Q` lies in any ideal containing the
entries of the middle factor. This is the only membership computation the closure proofs need. -/
private theorem entry_mul_mul_mem {S : Type*} [CommRing S] (K : Ideal S) {μ : ℕ}
    {M : Matrix (Fin μ) (Fin μ) S} (hM : ∀ k l, M k l ∈ K)
    (P Q : Matrix (Fin μ) (Fin μ) S) (i j : Fin μ) : (P * M * Q) i j ∈ K := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Ideal.sum_mem _ fun t _ => ?_
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hM t k))

/-! ### The three Hopf-ideal closure conditions -/

/-- The counit sends the bundled generic matrix to the identity matrix. -/
private theorem genericMatrix_map_counit :
    (genericMatrix R n).map
        (Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) = 1 := by
  ext i j
  rw [Matrix.map_apply, genericMatrix_apply, Bialgebra.counitAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_counit_X, Matrix.one_apply]

/-- The counit vanishes on every defining relation. -/
private theorem counit_relationMatrix (i j : Fin n) :
    Coalgebra.counit (R := R) (relationMatrix R n i j) = 0 := by
  have h := congrFun (congrFun (relationMatrix_map R n
    (Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R n))) i) j
  rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply] at h
  rw [h, genericMatrix_map_counit, Matrix.transpose_one, Matrix.mul_one, sub_self,
    Matrix.zero_apply]

/-- The comultiplication sends the bundled generic matrix to the product of its two tensor
inclusions: `Δ X = (X ⊗ 1)(1 ⊗ X)`. -/
private theorem genericMatrix_map_comul :
    (genericMatrix R n).map
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) =
      (genericMatrix R n).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (genericMatrix R n).map (Algebra.TensorProduct.includeRight (R := R)) := by
  ext i j
  rw [Matrix.map_apply, genericMatrix_apply, Bialgebra.comulAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_comul_X, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, genericMatrix_apply, genericMatrix_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The comultiplication of the relation matrix decomposes as a right-tensor-framed copy of the
relations plus the left tensor inclusion of the relations. -/
private theorem relationMatrix_map_comul :
    (relationMatrix R n).map
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) =
      (genericMatrix R n).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
          (relationMatrix R n).map (Algebra.TensorProduct.includeRight (R := R)) *
          ((genericMatrix R n).map
            (Algebra.TensorProduct.includeLeft (R := R) (S := R)))ᵀ +
        (relationMatrix R n).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) := by
  rw [relationMatrix_map R n, relationMatrix_map R n, relationMatrix_map R n,
    genericMatrix_map_comul, Matrix.transpose_mul]
  conv_rhs => rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sub_add_sub_cancel]
  simp only [Matrix.mul_assoc]

/-- The comultiplication of every defining relation lies in the sum of the left and right tensor
ideals of the span of the relations. -/
private theorem comul_relationMatrix_mem (i j : Fin n) :
    Coalgebra.comul (R := R) (relationMatrix R n i j) ∈
      HopfIdeal.leftTensorIdeal (R := R)
          (H := GeneralLinear.coordinateHopfAlgebra R n)
          (Ideal.span (relationSet R n)) ⊔
        HopfIdeal.rightTensorIdeal (R := R)
          (H := GeneralLinear.coordinateHopfAlgebra R n)
          (Ideal.span (relationSet R n)) := by
  have h := congrFun (congrFun (relationMatrix_map_comul R n) i) j
  rw [Matrix.map_apply, Bialgebra.comulAlgHom_apply] at h
  rw [h, Matrix.add_apply]
  refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left ?_)
  · refine entry_mul_mul_mem _ (fun k l => ?_) _ _ i j
    rw [Matrix.map_apply]
    exact HopfIdeal.includeRight_mem_rightTensorIdeal (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n)
      (Ideal.subset_span (relationMatrix_mem_relationSet R n k l))
  · rw [Matrix.map_apply]
    exact HopfIdeal.includeLeft_mem_leftTensorIdeal (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n)
      (Ideal.subset_span (relationMatrix_mem_relationSet R n i j))

/-- The antipode sends the bundled generic matrix to its bundled inverse. -/
private theorem genericMatrix_map_antipode :
    (genericMatrix R n).map
        (HopfAlgebra.antipodeAlgHom (R := R)
          (A := GeneralLinear.coordinateHopfAlgebra R n)) =
      genericMatrixInv R n := by
  ext i j
  rw [Matrix.map_apply, genericMatrix_apply, HopfAlgebra.antipodeAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_antipode_X, genericMatrixInv, Matrix.map_apply]

/-- The antipode image of the relation matrix is the negative of the relation matrix framed by
the bundled inverse: `X⁻¹ (X⁻¹)ᵀ - 1 = -(X⁻¹ (X Xᵀ - 1) (X⁻¹)ᵀ)`. -/
private theorem relationMatrix_map_antipode :
    (relationMatrix R n).map
        (HopfAlgebra.antipodeAlgHom (R := R)
          (A := GeneralLinear.coordinateHopfAlgebra R n)) =
      -(genericMatrixInv R n * relationMatrix R n * (genericMatrixInv R n)ᵀ) := by
  have ht : (genericMatrix R n)ᵀ * (genericMatrixInv R n)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, genericMatrixInv_mul_genericMatrix, Matrix.transpose_one]
  have hkey : genericMatrixInv R n * relationMatrix R n * (genericMatrixInv R n)ᵀ =
      1 - genericMatrixInv R n * (genericMatrixInv R n)ᵀ := by
    rw [relationMatrix, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    congr 1
    calc genericMatrixInv R n * (genericMatrix R n * (genericMatrix R n)ᵀ) *
          (genericMatrixInv R n)ᵀ
        = genericMatrixInv R n * genericMatrix R n *
            ((genericMatrix R n)ᵀ * (genericMatrixInv R n)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [genericMatrixInv_mul_genericMatrix, ht, Matrix.mul_one]
  rw [relationMatrix_map R n, genericMatrix_map_antipode, hkey, neg_sub]

/-- The antipode carries every defining relation into the span of the relations. -/
private theorem antipode_relationMatrix_mem (i j : Fin n) :
    HopfAlgebra.antipode R (relationMatrix R n i j) ∈ Ideal.span (relationSet R n) := by
  have h := congrFun (congrFun (relationMatrix_map_antipode R n) i) j
  rw [Matrix.map_apply, HopfAlgebra.antipodeAlgHom_apply] at h
  rw [h, Matrix.neg_apply]
  exact neg_mem (entry_mul_mul_mem _
    (fun k l => Ideal.subset_span (relationMatrix_mem_relationSet R n k l)) _ _ i j)

/-! ### The defining Hopf ideal and quotient -/

/-- **The orthogonal Hopf ideal**: the ideal of the coordinate Hopf algebra of `GL n`
generated by the entries of `X Xᵀ - 1`, with the three closure conditions extended from the
generators across the span. -/
noncomputable def definingHopfIdeal :
    HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n) :=
  HopfIdeal.ofIdeal (Ideal.span (relationSet R n))
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨ij, rfl⟩ := hy; exact comul_relationMatrix_mem R n ij.1 ij.2
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul h x _ hx =>
          rw [smul_eq_mul, Bialgebra.comul_mul]
          exact Ideal.mul_mem_left _ _ hx)
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨ij, rfl⟩ := hy; exact counit_relationMatrix R n ij.1 ij.2
      | zero => rw [map_zero]
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul h x _ hx => rw [smul_eq_mul, Bialgebra.counit_mul, hx, mul_zero])
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨ij, rfl⟩ := hy; exact antipode_relationMatrix_mem R n ij.1 ij.2
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul h x _ hx =>
          rw [smul_eq_mul, HopfAlgebra.antipode_mul_distrib]
          exact Ideal.mul_mem_left _ _ hx)

/-- The underlying ideal of the orthogonal Hopf ideal is the span of the defining relations. -/
@[simp]
theorem definingHopfIdeal_toIdeal :
    (definingHopfIdeal R n).toIdeal = Ideal.span (relationSet R n) := by
  rw [HopfIdeal.toIdeal_carrier, definingHopfIdeal, HopfIdeal.ofIdeal_carrier]

/-- The coordinate Hopf algebra of the orthogonal subgroup scheme of `GL n`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n)

/-- The quotient coordinate morphism from `O(GL n)` to the orthogonal coordinate Hopf
algebra. -/
noncomputable def coordinateMap :
    GeneralLinear.coordinateHopfAlgebra R n ⟶ coordinateHopfAlgebra R n :=
  CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n)

/-- The orthogonal coordinate morphism sends an ambient coordinate to its quotient class. -/
theorem coordinateMap_apply (h : GeneralLinear.coordinateHopfAlgebra R n) :
    (coordinateMap R n).hom h =
      Ideal.Quotient.mkₐ R (definingHopfIdeal R n).toIdeal h := by
  unfold coordinateMap
  exact CommHopfAlgCat.mkQuotient_apply
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n) h

/-- Every defining relation vanishes in the orthogonal coordinate Hopf algebra. -/
@[simp]
theorem coordinateMap_relationMatrix (i j : Fin n) :
    (coordinateMap R n).hom (relationMatrix R n i j) = 0 := by
  rw [coordinateMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (definingHopfIdeal_toIdeal R n ▸
      Ideal.subset_span (relationMatrix_mem_relationSet R n i j))

/-- The orthogonal subgroup scheme of `GL n`. -/
noncomputable def groupScheme :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n)

private noncomputable def groupSchemeι :=
  CommHopfAlgCat.quotientSpecι (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n)

/-- The closed-subgroup inclusion from the orthogonal subgroup scheme into the named general
linear group scheme. -/
noncomputable def inclusion : groupScheme R n ⟶ GeneralLinear.groupScheme R n :=
  groupSchemeι R n ≫ (eqToIso (GeneralLinear.groupScheme_def R n).symm).hom

private theorem inclusion_hom_left :
    (inclusion R n).hom.hom.left =
      (CommHopfAlgCat.quotientSpecι
        (GeneralLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n)).hom.hom.left ≫
      ((eqToIso (GeneralLinear.groupScheme_def R n).symm).hom).hom.hom.left := by
  rw [inclusion]
  unfold groupSchemeι
  rfl

/-- The orthogonal inclusion into the named general linear group scheme is a closed
immersion. -/
instance isClosedImmersion_inclusion :
    AlgebraicGeometry.IsClosedImmersion (inclusion R n).hom.hom.left := by
  let c := (CommHopfAlgCat.quotientSpecι
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)).hom.hom.left
  let e₂ := ((eqToIso (GeneralLinear.groupScheme_def R n).symm).hom).hom.hom.left
  have he₂ : IsIso e₂ :=
    ((Over.forget (AlgebraicGeometry.Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))).mapIso
        (eqToIso (GeneralLinear.groupScheme_def R n).symm))).isIso_hom
  have hc : AlgebraicGeometry.IsClosedImmersion c := by
    infer_instance
  have hc₂ : AlgebraicGeometry.IsClosedImmersion (c ≫ e₂) :=
    (@MorphismProperty.cancel_right_of_respectsIso
      _ _ @AlgebraicGeometry.IsClosedImmersion inferInstance _ _ _ c e₂ he₂).2 hc
  rw [inclusion_hom_left]
  exact hc₂

/-- The orthogonal coordinate Hopf algebra, bundled with its finite-type property. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  FiniteTypeCommHopfAlgCat.quotient
    (⟨GeneralLinear.coordinateHopfAlgebra R n, by
      rw [← GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj]
      exact (GeneralLinear.finiteTypeCoordinateHopfAlgebra R n).property⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R n)

/-- The finite-type package has the orthogonal coordinate Hopf algebra as its underlying
object. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R n).obj = coordinateHopfAlgebra R n := by
  rw [finiteTypeCoordinateHopfAlgebra]

/-- The structural morphism of the orthogonal subgroup scheme is locally of finite type. -/
instance locallyOfFiniteType_groupScheme :
    AlgebraicGeometry.LocallyOfFiniteType (groupScheme R n).X.hom := by
  unfold groupScheme
  exact FiniteTypeCommHopfAlgCat.locallyOfFiniteType_quotientSpec
    (⟨GeneralLinear.coordinateHopfAlgebra R n, by
        rw [← GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj]
        exact (GeneralLinear.finiteTypeCoordinateHopfAlgebra R n).property⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R n)

/-! ### Algebra-valued points -/

section Points

-- `Matrix.orthogonalGroup` reads the transpose as a `star`, through the trivial star structure
-- on the commutative coefficient ring, exactly as in `Mathlib.LinearAlgebra.UnitaryGroup`.
attribute [local instance] starRingOfComm

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Evaluating the relation matrix at a point gives the form relation of its matrix. -/
private theorem ofConv_relationMatrix
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    (relationMatrix R n).map g.ofConv =
      (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A) *
          (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A)ᵀ -
        1 := by
  have hg : (genericMatrix R n).map g.ofConv =
      (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A) := by
    ext i j
    rw [Matrix.map_apply, genericMatrix_apply]
    exact (GeneralLinear.pointToGeneralLinear_apply n g i j).symm
  rw [relationMatrix_map R n g.ofConv, hg]

/-- An ambient point belongs to the subgroup cut out by the orthogonal Hopf ideal exactly when
its matrix is orthogonal. This is the ambient membership criterion that further cuts consume;
the determinant-one cut combines it with the special-linear one. -/
theorem mem_definingPointsSubgroup_iff
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
        (CommAlgCat.of R A) ↔
      (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) ∈
        Matrix.orthogonalGroup (Fin n) A := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, Matrix.mem_orthogonalGroup_iff,
    GeneralLinear.pointsMulEquiv_apply]
  constructor
  · intro h
    have hzero : (relationMatrix R n).map g.ofConv = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply]
      exact h _ (HopfIdeal.mem_toIdeal.mp
        (definingHopfIdeal_toIdeal R n ▸
          Ideal.subset_span (relationMatrix_mem_relationSet R n i j)))
    rw [ofConv_relationMatrix R n g] at hzero
    exact sub_eq_zero.mp hzero
  · intro h y hy
    have hzero : (relationMatrix R n).map g.ofConv = 0 := by
      rw [ofConv_relationMatrix R n g]
      exact sub_eq_zero.mpr h
    have hle : Ideal.span (relationSet R n) ≤
        RingHom.ker (g.ofConv :
          GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] A) := by
      rw [Ideal.span_le]
      rintro _ ⟨ij, rfl⟩
      have := congrFun (congrFun hzero ij.1) ij.2
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    exact hle (definingHopfIdeal_toIdeal R n ▸ HopfIdeal.mem_toIdeal.mpr hy)

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
private theorem toUnits_mk (M : GL (Fin n) A)
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
