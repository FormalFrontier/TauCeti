/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
import TauCeti.CategoryTheory.Comma.Over

/-!
# The symplectic subgroup scheme of `GL₂ₘ`

For a commutative ring `R` and `m : ℕ`, the entries of the matrix relation

```text
X Jₘ Xᵀ - Jₘ
```

— `X` the localized generic matrix of `GL (m + m)`, `Jₘ` the standard alternating form in
`Fin (m + m)` coordinates — generate a Hopf ideal in the coordinate Hopf algebra of
`GL (m + m)`. Its quotient represents the closed subgroup scheme `Sp₂ₘ` of symplectic matrices.
On every commutative `R`-algebra `A`, its points are naturally the existing subgroup
`TauCeti.GLSymplecticFin m A`, equivalently `TauCeti.GLSymplectic (Fin m) A`.

Together with `TauCeti.GLSymplectic`, this completes the `Sp₂ₘ` worked example of the
ReductiveGroups roadmap at the same boundary as the Borel example
(`TauCeti.GeneralLinear.Borel`): construction and points identification, with no smoothness or
reductivity claim.

The three Hopf-ideal closure conditions are proved by matrix algebra rather than coordinate by
coordinate. Writing `f := X Jₘ Xᵀ - Jₘ` for the matrix of generators and mapping it entrywise
through the relevant algebra morphisms:

* the counit sends `X` to the identity matrix, so it sends `f` to `1 Jₘ 1ᵀ - Jₘ = 0`;
* the comultiplication sends `X` to `Y Z`, where `Y` and `Z` are the two tensor inclusions of
  `X`, and

  ```text
  (Y Z) Jₘ (Y Z)ᵀ - Jₘ = Y (Z Jₘ Zᵀ - Jₘ) Yᵀ + (Y Jₘ Yᵀ - Jₘ),
  ```

  whose two summands are the right and left tensor inclusions of `f` framed by matrices, so
  every entry lies in the right or left tensor ideal;
* the antipode sends `X` to its inverse matrix, and

  ```text
  X⁻¹ Jₘ (X⁻¹)ᵀ - Jₘ = -(X⁻¹ (X Jₘ Xᵀ - Jₘ) (X⁻¹)ᵀ),
  ```

  so every entry of the antipode image is a combination of the generators.

The construction includes `m = 0` and the zero ring, and no invertibility of the form is used:
the same three computations apply verbatim to `X C Xᵀ - C` for any constant matrix `C`.

## Main declarations

* `TauCeti.Symplectic.relationMatrix`: the matrix of defining relations `X Jₘ Xᵀ - Jₘ`.
* `TauCeti.Symplectic.definingHopfIdeal`: the Hopf ideal its entries generate.
* `TauCeti.Symplectic.coordinateHopfAlgebra`: the symplectic coordinate Hopf algebra, the
  quotient by the defining Hopf ideal.
* `TauCeti.Symplectic.groupScheme` and `TauCeti.Symplectic.inclusion`: the symplectic subgroup
  scheme and its closed immersion into the general linear group scheme.
* `TauCeti.Symplectic.pointsMulEquiv`: the group of algebra-valued points of the symplectic
  coordinate Hopf algebra is `TauCeti.GLSymplecticFin`, and
  `TauCeti.Symplectic.pointsMulEquivGLSymplectic` reads it in `Fin m ⊕ Fin m` coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3 and §24.6: `Sp₂ₙ` as the subgroup of `GL₂ₙ`
  preserving a nondegenerate alternating form, cut out by the entries of the form relation.
* The Stacks Project, [Tag 022W](https://stacks.math.columbia.edu/tag/022W), for the ambient
  general linear group scheme.

The matrix form of the closure computations is standard; the framing identities used here are
recorded in the module docstring and are not adapted from either reference.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.Symplectic

universe u v w

variable (R : Type u) [CommRing R] (m : ℕ)

/-! ### The defining relation matrix -/

/-- **The matrix of defining relations** of the symplectic subgroup scheme:
`X Jₘ Xᵀ - Jₘ` over the coordinate Hopf algebra of `GL (m + m)`. -/
noncomputable def relationMatrix :
    Matrix (Fin (m + m)) (Fin (m + m)) (GeneralLinear.coordinateHopfAlgebra R (m + m)) :=
  GeneralLinear.genericMatrix R (m + m) *
      (JFin m R).map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R (m + m))) *
      (GeneralLinear.genericMatrix R (m + m))ᵀ -
    (JFin m R).map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R (m + m)))

/-- The set of defining relations: the entries of the relation matrix. -/
def relationSet : Set (GeneralLinear.coordinateHopfAlgebra R (m + m)) :=
  Set.range fun ij : Fin (m + m) × Fin (m + m) => relationMatrix R m ij.1 ij.2

/-- Every entry of the relation matrix is a defining relation. -/
theorem relationMatrix_mem_relationSet (i j : Fin (m + m)) :
    relationMatrix R m i j ∈ relationSet R m :=
  ⟨(i, j), rfl⟩

/-- Mapping the relation matrix through an algebra morphism gives the relation of the images:
the generic matrix maps entrywise, and the constant form maps to the constant form. -/
private theorem relationMatrix_map {T : Type*} [CommRing T] [Algebra R T]
    (phi : GeneralLinear.coordinateHopfAlgebra R (m + m) →ₐ[R] T) :
    (relationMatrix R m).map phi =
      (GeneralLinear.genericMatrix R (m + m)).map phi * (JFin m R).map (algebraMap R T) *
          ((GeneralLinear.genericMatrix R (m + m)).map phi)ᵀ -
        (JFin m R).map (algebraMap R T) := by
  have hJ : ((JFin m R).map
        (algebraMap R (GeneralLinear.coordinateHopfAlgebra R (m + m)))).map phi =
      (JFin m R).map (algebraMap R T) := by
    rw [Matrix.map_map]
    exact congrArg _ (funext fun r => phi.commutes r)
  rw [relationMatrix, Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, hJ, Matrix.transpose_map]
  exact fun a b => map_sub phi a b

/-- An entry of a framed relation matrix `P (X Jₘ Xᵀ - Jₘ) Q` lies in any ideal containing the
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
    (GeneralLinear.genericMatrix R (m + m)).map
        (Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R (m + m))) = 1 := by
  ext i j
  rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply, Bialgebra.counitAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_counit_X, Matrix.one_apply]

/-- The counit vanishes on every defining relation. -/
private theorem counit_relationMatrix (i j : Fin (m + m)) :
    Coalgebra.counit (R := R) (relationMatrix R m i j) = 0 := by
  have h := congrFun (congrFun (relationMatrix_map R m
    (Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R (m + m)))) i) j
  rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply] at h
  rw [h, genericMatrix_map_counit, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id,
    Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, sub_self, Matrix.zero_apply]

/-- The comultiplication sends the bundled generic matrix to the product of its two tensor
inclusions: `Δ X = (X ⊗ 1)(1 ⊗ X)`. -/
private theorem genericMatrix_map_comul :
    (GeneralLinear.genericMatrix R (m + m)).map
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R (m + m))) =
      (GeneralLinear.genericMatrix R (m + m)).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (GeneralLinear.genericMatrix R (m + m)).map
          (Algebra.TensorProduct.includeRight (R := R)) := by
  ext i j
  rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply, Bialgebra.comulAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_comul_X, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, GeneralLinear.genericMatrix_apply,
    GeneralLinear.genericMatrix_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The comultiplication of the relation matrix decomposes as a right-tensor-framed copy of the
relations plus the left tensor inclusion of the relations. -/
private theorem relationMatrix_map_comul :
    (relationMatrix R m).map
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R (m + m))) =
      (GeneralLinear.genericMatrix R (m + m)).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
          (relationMatrix R m).map (Algebra.TensorProduct.includeRight (R := R)) *
          ((GeneralLinear.genericMatrix R (m + m)).map
            (Algebra.TensorProduct.includeLeft (R := R) (S := R)))ᵀ +
        (relationMatrix R m).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) := by
  rw [relationMatrix_map R m, relationMatrix_map R m, relationMatrix_map R m,
    genericMatrix_map_comul, Matrix.transpose_mul]
  conv_rhs => rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_cancel]
  simp only [Matrix.mul_assoc]

/-- The comultiplication of every defining relation lies in the sum of the left and right tensor
ideals of the span of the relations. -/
private theorem comul_relationMatrix_mem (i j : Fin (m + m)) :
    Coalgebra.comul (R := R) (relationMatrix R m i j) ∈
      HopfIdeal.leftTensorIdeal (R := R)
          (H := GeneralLinear.coordinateHopfAlgebra R (m + m))
          (Ideal.span (relationSet R m)) ⊔
        HopfIdeal.rightTensorIdeal (R := R)
          (H := GeneralLinear.coordinateHopfAlgebra R (m + m))
          (Ideal.span (relationSet R m)) := by
  have h := congrFun (congrFun (relationMatrix_map_comul R m) i) j
  rw [Matrix.map_apply, Bialgebra.comulAlgHom_apply] at h
  rw [h, Matrix.add_apply]
  refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left ?_)
  · refine entry_mul_mul_mem _ (fun k l => ?_) _ _ i j
    rw [Matrix.map_apply]
    exact HopfIdeal.includeRight_mem_rightTensorIdeal (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R (m + m))
      (Ideal.subset_span (relationMatrix_mem_relationSet R m k l))
  · rw [Matrix.map_apply]
    exact HopfIdeal.includeLeft_mem_leftTensorIdeal (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R (m + m))
      (Ideal.subset_span (relationMatrix_mem_relationSet R m i j))

/-- The antipode sends the bundled generic matrix to its bundled inverse. -/
private theorem genericMatrix_map_antipode :
    (GeneralLinear.genericMatrix R (m + m)).map
        (HopfAlgebra.antipodeAlgHom (R := R)
          (A := GeneralLinear.coordinateHopfAlgebra R (m + m))) =
      GeneralLinear.genericMatrixInv R (m + m) := by
  ext i j
  rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply, HopfAlgebra.antipodeAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_antipode_X, GeneralLinear.genericMatrixInv_apply]

/-- The antipode image of the relation matrix is the negative of the relation matrix framed by
the bundled inverse:
`X⁻¹ Jₘ (X⁻¹)ᵀ - Jₘ = -(X⁻¹ (X Jₘ Xᵀ - Jₘ) (X⁻¹)ᵀ)`. -/
private theorem relationMatrix_map_antipode :
    (relationMatrix R m).map
        (HopfAlgebra.antipodeAlgHom (R := R)
          (A := GeneralLinear.coordinateHopfAlgebra R (m + m))) =
      -(GeneralLinear.genericMatrixInv R (m + m) * relationMatrix R m *
        (GeneralLinear.genericMatrixInv R (m + m))ᵀ) := by
  have ht : (GeneralLinear.genericMatrix R (m + m))ᵀ *
      (GeneralLinear.genericMatrixInv R (m + m))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, GeneralLinear.genericMatrixInv_mul_genericMatrix,
      Matrix.transpose_one]
  have hkey : GeneralLinear.genericMatrixInv R (m + m) * relationMatrix R m *
      (GeneralLinear.genericMatrixInv R (m + m))ᵀ =
      (JFin m R).map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R (m + m))) -
        GeneralLinear.genericMatrixInv R (m + m) *
          (JFin m R).map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R (m + m))) *
          (GeneralLinear.genericMatrixInv R (m + m))ᵀ := by
    rw [relationMatrix, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    calc GeneralLinear.genericMatrixInv R (m + m) *
          (GeneralLinear.genericMatrix R (m + m) *
            (JFin m R).map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R (m + m))) *
            (GeneralLinear.genericMatrix R (m + m))ᵀ) *
          (GeneralLinear.genericMatrixInv R (m + m))ᵀ
        = GeneralLinear.genericMatrixInv R (m + m) * GeneralLinear.genericMatrix R (m + m) *
            (JFin m R).map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R (m + m))) *
            ((GeneralLinear.genericMatrix R (m + m))ᵀ *
              (GeneralLinear.genericMatrixInv R (m + m))ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (JFin m R).map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R (m + m))) := by
          rw [GeneralLinear.genericMatrixInv_mul_genericMatrix, ht, Matrix.one_mul, Matrix.mul_one]
  rw [relationMatrix_map R m, genericMatrix_map_antipode, hkey, neg_sub]

/-- The antipode carries every defining relation into the span of the relations. -/
private theorem antipode_relationMatrix_mem (i j : Fin (m + m)) :
    HopfAlgebra.antipode R (relationMatrix R m i j) ∈ Ideal.span (relationSet R m) := by
  have h := congrFun (congrFun (relationMatrix_map_antipode R m) i) j
  rw [Matrix.map_apply, HopfAlgebra.antipodeAlgHom_apply] at h
  rw [h, Matrix.neg_apply]
  exact neg_mem (entry_mul_mul_mem _
    (fun k l => Ideal.subset_span (relationMatrix_mem_relationSet R m k l)) _ _ i j)

/-! ### The defining Hopf ideal and quotient -/

/-- **The symplectic Hopf ideal**: the ideal of the coordinate Hopf algebra of `GL (m + m)`
generated by the entries of `X Jₘ Xᵀ - Jₘ`, with the three closure conditions extended from
the generators across the span. -/
noncomputable def definingHopfIdeal :
    HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R (m + m)) :=
  HopfIdeal.ofSpan (relationSet R m)
    (fun _ hx => by
      obtain ⟨ij, rfl⟩ := hx
      exact comul_relationMatrix_mem R m ij.1 ij.2)
    (fun _ hx => by
      obtain ⟨ij, rfl⟩ := hx
      exact counit_relationMatrix R m ij.1 ij.2)
    (fun _ hx => by
      obtain ⟨ij, rfl⟩ := hx
      exact antipode_relationMatrix_mem R m ij.1 ij.2)

/-- The underlying ideal of the symplectic Hopf ideal is the span of the defining relations. -/
@[simp]
theorem definingHopfIdeal_toIdeal :
    (definingHopfIdeal R m).toIdeal = Ideal.span (relationSet R m) := by
  rw [definingHopfIdeal, HopfIdeal.ofSpan_toIdeal]

/-- The coordinate Hopf algebra of the symplectic subgroup scheme of `GL (m + m)`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R (m + m))
    (definingHopfIdeal R m)

/-- The quotient coordinate morphism from `O(GL (m + m))` to the symplectic coordinate Hopf
algebra. -/
noncomputable def coordinateMap :
    GeneralLinear.coordinateHopfAlgebra R (m + m) ⟶ coordinateHopfAlgebra R m :=
  CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R (m + m))
    (definingHopfIdeal R m)

/-- The symplectic coordinate map is the canonical quotient morphism by the defining Hopf
ideal. -/
theorem coordinateMap_def :
    coordinateMap R m =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R (m + m))
        (definingHopfIdeal R m) := by
  unfold coordinateMap
  rfl

/-- The symplectic coordinate morphism sends an ambient coordinate to its quotient class. -/
theorem coordinateMap_apply (h : GeneralLinear.coordinateHopfAlgebra R (m + m)) :
    (coordinateMap R m).hom h =
      Ideal.Quotient.mkₐ R (definingHopfIdeal R m).toIdeal h := by
  unfold coordinateMap
  exact CommHopfAlgCat.mkQuotient_apply
    (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m) h

/-- Every defining relation vanishes in the symplectic coordinate Hopf algebra. -/
@[simp]
theorem coordinateMap_relationMatrix (i j : Fin (m + m)) :
    (coordinateMap R m).hom (relationMatrix R m i j) = 0 := by
  rw [coordinateMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (definingHopfIdeal_toIdeal R m ▸
      Ideal.subset_span (relationMatrix_mem_relationSet R m i j))

/-- The symplectic subgroup scheme of `GL (m + m)`. -/
noncomputable def groupScheme :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R (m + m))
    (definingHopfIdeal R m)

/-- The symplectic group scheme is the quotient spectrum of its coordinate Hopf algebra. -/
theorem groupScheme_def :
    groupScheme R m =
      CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R (m + m))
        (definingHopfIdeal R m) := by
  unfold groupScheme
  rfl

/-- The quotient-spectrum inclusion into the Hopf spectrum of the ambient coordinate algebra. -/
private noncomputable def groupSchemeι :=
  CommHopfAlgCat.quotientSpecι (GeneralLinear.coordinateHopfAlgebra R (m + m))
    (definingHopfIdeal R m)

/-- The closed-subgroup inclusion from the symplectic subgroup scheme into the named general
linear group scheme. -/
noncomputable def inclusion : groupScheme R m ⟶ GeneralLinear.groupScheme R (m + m) :=
  eqToHom (groupScheme_def R m) ≫ groupSchemeι R m ≫
    (eqToIso (GeneralLinear.groupScheme_def R (m + m)).symm).hom

/-- The symplectic inclusion is the relative spectrum of the quotient coordinate map, followed
by transport to the named general-linear presentation. -/
theorem inclusion_def :
    inclusion R m =
      eqToHom (groupScheme_def R m) ≫
        CommHopfAlgCat.quotientSpecι
          (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m) ≫
        (eqToIso (GeneralLinear.groupScheme_def R (m + m)).symm).hom := by
  unfold inclusion groupSchemeι
  rfl

private theorem inclusion_hom_left :
    (inclusion R m).hom.hom.left =
      (CommHopfAlgCat.quotientSpecι
        (GeneralLinear.coordinateHopfAlgebra R (m + m))
        (definingHopfIdeal R m)).hom.hom.left ≫
      ((eqToIso (GeneralLinear.groupScheme_def R (m + m)).symm).hom).hom.hom.left := by
  rw [inclusion]
  unfold groupSchemeι
  rfl

/-- The symplectic inclusion into the named general linear group scheme is a closed
immersion. -/
instance isClosedImmersion_inclusion :
    AlgebraicGeometry.IsClosedImmersion (inclusion R m).hom.hom.left := by
  let c := (CommHopfAlgCat.quotientSpecι
    (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)).hom.hom.left
  let e₂ := ((eqToIso (GeneralLinear.groupScheme_def R (m + m)).symm).hom).hom.hom.left
  have hc : AlgebraicGeometry.IsClosedImmersion c := by
    infer_instance
  have hc₂ : AlgebraicGeometry.IsClosedImmersion (c ≫ e₂) :=
    (MorphismProperty.cancel_right_of_respectsIso _ c e₂).2 hc
  rw [inclusion_hom_left]
  exact hc₂

/-- The symplectic coordinate Hopf algebra, bundled with its finite-type property. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  FiniteTypeCommHopfAlgCat.quotient
    (⟨GeneralLinear.coordinateHopfAlgebra R (m + m), by
      rw [← GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj]
      exact (GeneralLinear.finiteTypeCoordinateHopfAlgebra R (m + m)).property⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R m)

/-- The finite-type package has the symplectic coordinate Hopf algebra as its underlying
object. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R m).obj = coordinateHopfAlgebra R m := by
  rw [finiteTypeCoordinateHopfAlgebra]

/-- The structural morphism of the symplectic subgroup scheme is locally of finite type. -/
instance locallyOfFiniteType_groupScheme :
    AlgebraicGeometry.LocallyOfFiniteType (groupScheme R m).X.hom := by
  unfold groupScheme
  exact FiniteTypeCommHopfAlgCat.locallyOfFiniteType_quotientSpec
    (⟨GeneralLinear.coordinateHopfAlgebra R (m + m), by
        rw [← GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj]
        exact (GeneralLinear.finiteTypeCoordinateHopfAlgebra R (m + m)).property⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R m)

/-! ### Algebra-valued points -/

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Evaluating the relation matrix at a point gives the form relation of its matrix. -/
private theorem ofConv_relationMatrix
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R (m + m)) (CommAlgCat.of R A)) :
    (relationMatrix R m).map g.ofConv =
      (GeneralLinear.pointToGeneralLinear (m + m) g :
            Matrix (Fin (m + m)) (Fin (m + m)) A) *
          JFin m A *
          (GeneralLinear.pointToGeneralLinear (m + m) g :
            Matrix (Fin (m + m)) (Fin (m + m)) A)ᵀ -
        JFin m A := by
  have hg : (GeneralLinear.genericMatrix R (m + m)).map g.ofConv =
      (GeneralLinear.pointToGeneralLinear (m + m) g :
        Matrix (Fin (m + m)) (Fin (m + m)) A) := by
    ext i j
    rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply]
    exact (GeneralLinear.pointToGeneralLinear_apply (m + m) g i j).symm
  rw [relationMatrix_map R m g.ofConv, hg, JFin_map]

/-- An ambient point belongs to the subgroup cut out by the symplectic Hopf ideal exactly when
its matrix is symplectic. -/
private theorem mem_definingPointsSubgroup_iff
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R (m + m)) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
        (CommAlgCat.of R A) ↔
      GeneralLinear.pointsMulEquiv (m + m) g ∈ GLSymplecticFin m A := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, GLSymplecticFin.mem_iff,
    GeneralLinear.pointsMulEquiv_apply]
  constructor
  · intro h
    have hzero : (relationMatrix R m).map g.ofConv = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply]
      exact h _ (HopfIdeal.mem_toIdeal.mp
        (definingHopfIdeal_toIdeal R m ▸
          Ideal.subset_span (relationMatrix_mem_relationSet R m i j)))
    rw [ofConv_relationMatrix R m g] at hzero
    exact sub_eq_zero.mp hzero
  · intro h y hy
    have hzero : (relationMatrix R m).map g.ofConv = 0 := by
      rw [ofConv_relationMatrix R m g]
      exact sub_eq_zero.mpr h
    have hle : Ideal.span (relationSet R m) ≤
        RingHom.ker (g.ofConv :
          GeneralLinear.coordinateHopfAlgebra R (m + m) →ₐ[R] A) := by
      rw [Ideal.span_le]
      rintro _ ⟨ij, rfl⟩
      have := congrFun (congrFun hzero ij.1) ij.2
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    exact hle (definingHopfIdeal_toIdeal R m ▸ HopfIdeal.mem_toIdeal.mpr hy)

/-- Read a cut-out ambient point as a symplectic matrix. -/
private noncomputable def pointsSubgroupToGLSymplecticFin
    (g : CommHopfAlgCat.quotientPointsSubgroup
      (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
      (CommAlgCat.of R A)) : GLSymplecticFin m A :=
  ⟨GeneralLinear.pointsMulEquiv (m + m) g.1,
    (mem_definingPointsSubgroup_iff R m g.1).mp g.2⟩

/-- Regard a symplectic matrix as a point in the cut-out ambient subgroup. -/
private noncomputable def glSymplecticFinToPointsSubgroup (g : GLSymplecticFin m A) :
    CommHopfAlgCat.quotientPointsSubgroup
      (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
      (CommAlgCat.of R A) :=
  ⟨(GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).symm g.1,
    (mem_definingPointsSubgroup_iff R m _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact g.2)⟩

/-- The subgroup of `GL (m + m) (A)` cut out by the symplectic Hopf ideal is
`TauCeti.GLSymplecticFin m A`. -/
private noncomputable def definingPointsSubgroupMulEquiv :
    CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
        (CommAlgCat.of R A) ≃*
      GLSymplecticFin m A where
  toFun := pointsSubgroupToGLSymplecticFin R m
  invFun := glSymplecticFinToPointsSubgroup R m
  left_inv g := by
    apply Subtype.ext
    exact (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).symm_apply_apply g.1
  right_inv g := by
    apply Subtype.ext
    exact (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).apply_symm_apply g.1
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)) g.1 h.1

/-- **The points identification**: the group of algebra-valued points of the symplectic
coordinate Hopf algebra is the symplectic subgroup of the general linear group. -/
noncomputable def pointsMulEquiv :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m) (CommAlgCat.of R A) ≃*
      GLSymplecticFin m A :=
  ((CommHopfAlgCat.quotientPointsSubgroupNatIso
      (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)).app
      (CommAlgCat.of R A)).groupIsoToMulEquiv.trans
    (definingPointsSubgroupMulEquiv R m)

/-- Internally, the symplectic point equivalence first forms the cut-out ambient subgroup point
and then reads it as a symplectic matrix. -/
private theorem pointsMulEquiv_apply_eq
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m) (CommAlgCat.of R A)) :
    pointsMulEquiv R m (A := A) f =
      pointsSubgroupToGLSymplecticFin R m
        (((CommHopfAlgCat.quotientPointsSubgroupNatIso
          (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)).app
          (CommAlgCat.of R A)).hom f) :=
  rfl

/-- Under the symplectic and general-linear point equivalences, the quotient-point inclusion is
the ordinary inclusion of symplectic matrices into `GL (m + m)`. -/
theorem pointsMulEquiv_coe
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m) (CommAlgCat.of R A)) :
    GeneralLinear.pointsMulEquiv (m + m)
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
          (CommAlgCat.of R A) f) =
      (pointsMulEquiv R m (A := A) f : GL (Fin (m + m)) A) := by
  have hcomponent := CommHopfAlgCat.quotientPointsSubgroupNatIso_hom_app_apply
    (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
    (CommAlgCat.of R A) f
  rw [pointsMulEquiv_apply_eq]
  exact congrArg
    (fun g => (pointsSubgroupToGLSymplecticFin R m g : GLSymplecticFin m A).1)
    hcomponent.symm

/-- Mapping a symplectic point along the quotient coordinate morphism gives its ambient
general-linear point. -/
theorem mapPointsFunctor_coordinateMap_app
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m)
      (CommAlgCat.of R A)) :
    (CommHopfAlgCat.mapPointsFunctor (coordinateMap R m)).app (CommAlgCat.of R A) f =
      CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
        (CommAlgCat.of R A) f := by
  apply WithConv.ext
  rfl

/-- The ambient point attached to a symplectic matrix is the general-linear point attached to
its ordinary inclusion. -/
@[simp]
theorem quotientPointsHom_pointsMulEquiv_symm (g : GLSymplecticFin m A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
        (CommAlgCat.of R A) ((pointsMulEquiv R m (A := A)).symm g) =
      (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).symm g.1 := by
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).injective
  rw [pointsMulEquiv_coe, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- The symplectic point equivalence is natural in the value algebra: postcomposition of Hopf
points agrees with entrywise mapping of symplectic matrices. -/
theorem pointsMulEquiv_mapValue (phi : A →ₐ[R] B)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m)
      (CommAlgCat.of R A)) :
    pointsMulEquiv (R := R) (A := B) m
        (AlgHom.mapValue (H := coordinateHopfAlgebra R m) phi f) =
      GLSymplecticFin.map m A phi.toRingHom
        (pointsMulEquiv (R := R) (A := A) m f) := by
  apply Subtype.ext
  have hcoe_lhs := pointsMulEquiv_coe (R := R) (A := B) m
    (AlgHom.mapValue (H := coordinateHopfAlgebra R m) phi f)
  have hcoe_rhs := pointsMulEquiv_coe (R := R) (A := A) m f
  have hnatural :
      CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
          (CommAlgCat.of R B) (AlgHom.mapValue phi f) =
        AlgHom.mapValue phi
          (CommHopfAlgCat.quotientPointsHom
            (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)
            (CommAlgCat.of R A) f) := by
    apply WithConv.ext
    ext h
    -- After extensionality, both sides apply `phi` after `f` and the canonical quotient map.
    rfl
  rw [← hcoe_lhs, hnatural,
    GeneralLinear.pointsMulEquiv_mapValue, hcoe_rhs, GLSymplecticFin.coe_map]

/-- The points identification, read in `Fin m ⊕ Fin m` coordinates: the points of the symplectic
coordinate Hopf algebra are `TauCeti.GLSymplectic (Fin m) A`. -/
noncomputable def pointsMulEquivGLSymplectic :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m) (CommAlgCat.of R A) ≃*
      GLSymplectic (Fin m) A :=
  (pointsMulEquiv R m).trans (GLSymplecticFin.mulEquivGLSymplectic m A)

/-- On underlying general-linear elements, the `Fin m ⊕ Fin m` reading of a point is the
reindexing of its `Fin (m + m)` reading. -/
@[simp]
theorem coe_pointsMulEquivGLSymplectic
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R m) (CommAlgCat.of R A)) :
    ((pointsMulEquivGLSymplectic R m (A := A) f : GLSymplectic (Fin m) A) :
        GL (Fin m ⊕ Fin m) A) =
      reindexGL m A (pointsMulEquiv R m (A := A) f : GL (Fin (m + m)) A) :=
  GLSymplecticFin.coe_mulEquivGLSymplectic m A (pointsMulEquiv R m (A := A) f)

end Points

end TauCeti.Symplectic
