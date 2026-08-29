/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# The subgroup scheme of `GLₙ` preserving a constant matrix

For a commutative ring `R`, a natural number `n`, and a **constant** matrix
`C : Matrix (Fin n) (Fin n) R`, the entries of the matrix relation

```text
X C Xᵀ - C
```

— `X` the localized generic matrix of `GL n`, `C` read in the coordinate Hopf algebra through
the structure morphism — generate a Hopf ideal in the coordinate Hopf algebra of `GL n`. Its
quotient represents the closed subgroup scheme of `GL n` preserving `C`. On every commutative
`R`-algebra `A`, its points are the invertible matrices `M` with `M C Mᵀ = C`.

Nothing is assumed of `C`: it is an arbitrary square matrix over the base, not required to be
invertible, symmetric, alternating, or nondegenerate, and the construction includes `n = 0` and
the zero ring. The classical families are the specializations at a constant form:
`TauCeti.Orthogonal` takes `C = 1` and `TauCeti.Symplectic` takes `C = Jₘ`, each adding its own
identification of the points with the corresponding matrix group. This file supplies everything
those specializations share: the relation matrix, the Hopf ideal with its three closure
conditions, the quotient, the group scheme with its closed immersion into `GLₙ`, and the
ambient membership criterion `M C Mᵀ = C`; local finite type comes from the generic
`GeneralLinear.locallyOfFiniteType_hopfIdealQuotientSpec` instance, which applies to the
reducible `groupScheme` directly.

The three Hopf-ideal closure conditions are proved by matrix algebra rather than coordinate by
coordinate. Writing `f := X C Xᵀ - C` for the matrix of generators and mapping it entrywise
through the relevant algebra morphisms — each of which fixes `C`, being an `R`-algebra
morphism:

* the counit sends `X` to the identity matrix, so it sends `f` to `1 C 1ᵀ - C = 0`;
* the comultiplication sends `X` to `Y Z`, where `Y` and `Z` are the two tensor inclusions of
  `X`, and

  ```text
  (Y Z) C (Y Z)ᵀ - C = Y (Z C Zᵀ - C) Yᵀ + (Y C Yᵀ - C),
  ```

  whose two summands are the right and left tensor inclusions of `f` framed by matrices, so
  every entry lies in the right or left tensor ideal;
* the antipode sends `X` to its inverse matrix, and

  ```text
  X⁻¹ C (X⁻¹)ᵀ - C = -(X⁻¹ (X C Xᵀ - C) (X⁻¹)ᵀ),
  ```

  so every entry of the antipode image is a combination of the generators.

That each identity holds for an arbitrary constant `C` is what makes the classical examples
specializations rather than separate constructions: no step inverts `C`, transposes it, or uses
a relation between `C` and `Cᵀ`.

## Main declarations

* `TauCeti.ConstantForm.relationMatrix`: the matrix of defining relations `X C Xᵀ - C`.
* `TauCeti.ConstantForm.definingHopfIdeal`: the Hopf ideal its entries generate.
* `TauCeti.ConstantForm.coordinateHopfAlgebra` and `TauCeti.ConstantForm.coordinateMap`: the
  quotient coordinate Hopf algebra and the quotient morphism onto it.
* `TauCeti.ConstantForm.groupScheme` and `TauCeti.ConstantForm.inclusion`: the subgroup scheme
  preserving `C` and its closed immersion into the general linear group scheme — the generic
  `GeneralLinear.hopfIdealInclusion` at the defining Hopf ideal — with `groupScheme_def` and
  `inclusion_def` exposing the quotient-spectrum presentations.
* `TauCeti.ConstantForm.mem_definingPointsSubgroup_iff`: an ambient point is cut out exactly
  when its matrix `M` satisfies `M C Mᵀ = C`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3, where the orthogonal and symplectic groups are
  introduced as the subgroups of `GLₙ` cut out by the entries of a form relation.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), Chapter 1, for such groups
  as representable functors on commutative rings.
* The Stacks Project, [Tag 022W](https://stacks.math.columbia.edu/tag/022W), for the ambient
  general linear group scheme.

The matrix form of the closure computations is standard, and the framing identities above are
not adapted from either reference. The proofs themselves are those of the merged worked
examples `TauCeti.Symplectic` (for `C = Jₘ`) and `TauCeti.Orthogonal` (for `C = 1`),
generalized here to an arbitrary `C`: the declaration order and proof plan are theirs, and
those two files now consume this one rather than repeating it. `TauCeti.Symplectic` recorded
the generalization in its own module docstring — that the computations "apply verbatim to
`X C Xᵀ - C` for any constant matrix `C`" — before it was carried out.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ConstantForm

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The defining relation matrix -/

variable (C : Matrix (Fin n) (Fin n) R)

/-- **The matrix of defining relations** of the subgroup scheme preserving `C`:
`X C Xᵀ - C` over the coordinate Hopf algebra of `GL n`. -/
noncomputable def relationMatrix :
    Matrix (Fin n) (Fin n) (GeneralLinear.coordinateHopfAlgebra R n) :=
  GeneralLinear.genericMatrix R n *
      C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n)) *
      (GeneralLinear.genericMatrix R n)ᵀ -
    C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n))

/-- The relation matrix is the constant form transported by the generic matrix, minus the
form: `X C Xᵀ - C`. -/
theorem relationMatrix_def :
    relationMatrix R n C =
      GeneralLinear.genericMatrix R n *
          C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n)) *
          (GeneralLinear.genericMatrix R n)ᵀ -
        C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n)) := by
  rw [relationMatrix]

/-- The set of defining relations: the entries of the relation matrix. -/
def relationSet : Set (GeneralLinear.coordinateHopfAlgebra R n) :=
  Set.range fun ij : Fin n × Fin n => relationMatrix R n C ij.1 ij.2

/-- Every entry of the relation matrix is a defining relation. -/
theorem relationMatrix_mem_relationSet (i j : Fin n) :
    relationMatrix R n C i j ∈ relationSet R n C :=
  ⟨(i, j), rfl⟩

/-- An element is a defining relation exactly when it is an entry of the relation matrix. -/
@[simp] theorem mem_relationSet_iff {x : GeneralLinear.coordinateHopfAlgebra R n} :
    x ∈ relationSet R n C ↔ ∃ i j, relationMatrix R n C i j = x :=
  Set.mem_range.trans Prod.exists

/-- Mapping the relation matrix through an algebra morphism gives the relation of the images:
the generic matrix maps entrywise, and the constant form maps to the constant form. -/
@[simp] theorem relationMatrix_map {T : Type*} [CommRing T] [Algebra R T]
    (phi : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] T) :
    (relationMatrix R n C).map phi =
      (GeneralLinear.genericMatrix R n).map phi * C.map (algebraMap R T) *
          ((GeneralLinear.genericMatrix R n).map phi)ᵀ -
        C.map (algebraMap R T) := by
  have hC : (C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n))).map phi =
      C.map (algebraMap R T) := by
    rw [Matrix.map_map]
    exact congrArg _ (funext fun r => phi.commutes r)
  rw [relationMatrix, Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, hC, Matrix.transpose_map]
  exact fun a b => map_sub phi a b

/-- An entry of a framed relation matrix `P (X C Xᵀ - C) Q` lies in any ideal containing the
entries of the middle factor. This is the only membership computation the closure proofs
need. -/
private theorem entry_mul_mul_mem {S : Type*} [CommRing S] (K : Ideal S) {μ : ℕ}
    {M : Matrix (Fin μ) (Fin μ) S} (hM : ∀ k l, M k l ∈ K)
    (P Q : Matrix (Fin μ) (Fin μ) S) (i j : Fin μ) : (P * M * Q) i j ∈ K := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Ideal.sum_mem _ fun t _ => ?_
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hM t k))

/-! ### The three Hopf-ideal closure conditions -/

/-- The counit vanishes on every defining relation. -/
private theorem counit_relationMatrix (i j : Fin n) :
    Coalgebra.counit (R := R) (relationMatrix R n C i j) = 0 := by
  have h := congrFun (congrFun (relationMatrix_map R n C
    (Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R n))) i) j
  rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply] at h
  rw [h, GeneralLinear.map_counit_genericMatrix, Algebra.algebraMap_self, RingHom.coe_id,
    Matrix.map_id, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, sub_self,
    Matrix.zero_apply]

/-- The comultiplication of the relation matrix decomposes as a right-tensor-framed copy of the
relations plus the left tensor inclusion of the relations. -/
private theorem relationMatrix_map_comul :
    (relationMatrix R n C).map
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) =
      (GeneralLinear.genericMatrix R n).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
          (relationMatrix R n C).map (Algebra.TensorProduct.includeRight (R := R)) *
          ((GeneralLinear.genericMatrix R n).map
            (Algebra.TensorProduct.includeLeft (R := R) (S := R)))ᵀ +
        (relationMatrix R n C).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) := by
  rw [relationMatrix_map R n C, relationMatrix_map R n C, relationMatrix_map R n C,
    GeneralLinear.map_comul_genericMatrix, Matrix.transpose_mul]
  conv_rhs => rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_cancel]
  simp only [Matrix.mul_assoc]

/-- The comultiplication of every defining relation lies in the sum of the left and right tensor
ideals of the span of the relations. -/
private theorem comul_relationMatrix_mem (i j : Fin n) :
    Coalgebra.comul (R := R) (relationMatrix R n C i j) ∈
      HopfIdeal.leftTensorIdeal (R := R)
          (H := GeneralLinear.coordinateHopfAlgebra R n)
          (Ideal.span (relationSet R n C)) ⊔
        HopfIdeal.rightTensorIdeal (R := R)
          (H := GeneralLinear.coordinateHopfAlgebra R n)
          (Ideal.span (relationSet R n C)) := by
  have h := congrFun (congrFun (relationMatrix_map_comul R n C) i) j
  rw [Matrix.map_apply, Bialgebra.comulAlgHom_apply] at h
  rw [h, Matrix.add_apply]
  refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left ?_)
  · refine entry_mul_mul_mem _ (fun k l => ?_) _ _ i j
    rw [Matrix.map_apply]
    exact HopfIdeal.includeRight_mem_rightTensorIdeal (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n)
      (Ideal.subset_span (relationMatrix_mem_relationSet R n C k l))
  · rw [Matrix.map_apply]
    exact HopfIdeal.includeLeft_mem_leftTensorIdeal (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n)
      (Ideal.subset_span (relationMatrix_mem_relationSet R n C i j))

/-- The antipode image of the relation matrix is the negative of the relation matrix framed by
the bundled inverse: `X⁻¹ C (X⁻¹)ᵀ - C = -(X⁻¹ (X C Xᵀ - C) (X⁻¹)ᵀ)`. -/
private theorem relationMatrix_map_antipode :
    (relationMatrix R n C).map
        (HopfAlgebra.antipodeAlgHom (R := R)
          (A := GeneralLinear.coordinateHopfAlgebra R n)) =
      -((GeneralLinear.genericMatrix R n)⁻¹ * relationMatrix R n C *
        ((GeneralLinear.genericMatrix R n)⁻¹)ᵀ) := by
  have ht : (GeneralLinear.genericMatrix R n)ᵀ * ((GeneralLinear.genericMatrix R n)⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ (GeneralLinear.isUnit_det_genericMatrix R n),
      Matrix.transpose_one]
  have hkey : (GeneralLinear.genericMatrix R n)⁻¹ * relationMatrix R n C *
      ((GeneralLinear.genericMatrix R n)⁻¹)ᵀ =
      C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n)) -
        (GeneralLinear.genericMatrix R n)⁻¹ *
          C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n)) *
          ((GeneralLinear.genericMatrix R n)⁻¹)ᵀ := by
    rw [relationMatrix, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    calc (GeneralLinear.genericMatrix R n)⁻¹ *
          (GeneralLinear.genericMatrix R n *
            C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n)) *
            (GeneralLinear.genericMatrix R n)ᵀ) * ((GeneralLinear.genericMatrix R n)⁻¹)ᵀ
        = (GeneralLinear.genericMatrix R n)⁻¹ * GeneralLinear.genericMatrix R n *
            C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n)) *
            ((GeneralLinear.genericMatrix R n)ᵀ * ((GeneralLinear.genericMatrix R n)⁻¹)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = C.map (algebraMap R (GeneralLinear.coordinateHopfAlgebra R n)) := by
          rw [Matrix.nonsing_inv_mul _ (GeneralLinear.isUnit_det_genericMatrix R n), ht,
            Matrix.one_mul, Matrix.mul_one]
  rw [relationMatrix_map R n C, GeneralLinear.map_antipode_genericMatrix, hkey, neg_sub]

/-- The antipode carries every defining relation into the span of the relations. -/
private theorem antipode_relationMatrix_mem (i j : Fin n) :
    HopfAlgebra.antipode R (relationMatrix R n C i j) ∈ Ideal.span (relationSet R n C) := by
  have h := congrFun (congrFun (relationMatrix_map_antipode R n C) i) j
  rw [Matrix.map_apply, HopfAlgebra.antipodeAlgHom_apply] at h
  rw [h, Matrix.neg_apply]
  exact neg_mem (entry_mul_mul_mem _
    (fun k l => Ideal.subset_span (relationMatrix_mem_relationSet R n C k l)) _ _ i j)

/-! ### The defining Hopf ideal and quotient -/

/-- **The Hopf ideal preserving `C`**: the ideal of the coordinate Hopf algebra of `GL n`
generated by the entries of `X C Xᵀ - C`, with the three closure conditions extended from the
generators across the span. -/
noncomputable def definingHopfIdeal :
    HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n) :=
  HopfIdeal.ofSpan (relationSet R n C)
    (fun x hx => by
      obtain ⟨ij, rfl⟩ := hx
      exact comul_relationMatrix_mem R n C ij.1 ij.2)
    (fun x hx => by
      obtain ⟨ij, rfl⟩ := hx
      exact counit_relationMatrix R n C ij.1 ij.2)
    (fun x hx => by
      obtain ⟨ij, rfl⟩ := hx
      exact antipode_relationMatrix_mem R n C ij.1 ij.2)

/-- The underlying ideal of the defining Hopf ideal is the span of the defining relations. -/
@[simp]
theorem definingHopfIdeal_toIdeal :
    (definingHopfIdeal R n C).toIdeal = Ideal.span (relationSet R n C) := by
  rw [definingHopfIdeal, HopfIdeal.ofSpan_toIdeal]

/-- The coordinate Hopf algebra of the subgroup scheme of `GL n` preserving `C`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C)

/-- The quotient coordinate morphism from `O(GL n)` to the coordinate Hopf algebra of the
subgroup scheme preserving `C`. -/
noncomputable def coordinateMap :
    GeneralLinear.coordinateHopfAlgebra R n ⟶ coordinateHopfAlgebra R n C :=
  CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C)

/-- The coordinate map is the canonical quotient morphism by the defining Hopf ideal. -/
theorem coordinateMap_def :
    coordinateMap R n C =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n C) := by
  unfold coordinateMap
  rfl

/-- The coordinate morphism sends an ambient coordinate to its quotient class. -/
-- Not `@[simp]`: its left-hand side subsumes that of the `@[simp]` elimination lemma
-- `coordinateMap_relationMatrix`, and the raw quotient-class form is not the normal form —
-- the named morphism is. All uses are explicit `rw`.
theorem coordinateMap_apply (h : GeneralLinear.coordinateHopfAlgebra R n) :
    (coordinateMap R n C).hom h =
      Ideal.Quotient.mkₐ R (definingHopfIdeal R n C).toIdeal h := by
  unfold coordinateMap
  exact CommHopfAlgCat.mkQuotient_apply
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n C) h

/-- Every defining relation vanishes in the quotient coordinate Hopf algebra. -/
@[simp]
theorem coordinateMap_relationMatrix (i j : Fin n) :
    (coordinateMap R n C).hom (relationMatrix R n C i j) = 0 := by
  rw [coordinateMap_def]
  exact (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr
    (definingHopfIdeal_toIdeal R n C ▸
      Ideal.subset_span (relationMatrix_mem_relationSet R n C i j))

/-! ### The group scheme and its closed immersion -/

/-- The subgroup scheme of `GL n` preserving `C`. -/
noncomputable abbrev groupScheme :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C)

/-- The subgroup scheme preserving `C` is the quotient spectrum of its coordinate Hopf
algebra. -/
theorem groupScheme_def :
    groupScheme R n C =
      CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n C) :=
  rfl

/-- The closed-subgroup inclusion into the named general linear group scheme: the generic
Hopf-ideal closed immersion `GeneralLinear.hopfIdealInclusion` at the defining Hopf ideal. -/
noncomputable def inclusion : groupScheme R n C ⟶ GeneralLinear.groupScheme R n :=
  GeneralLinear.hopfIdealInclusion R n (definingHopfIdeal R n C)

/-- The inclusion is the generic Hopf-ideal closed immersion at the defining Hopf ideal. -/
theorem inclusion_def :
    inclusion R n C = GeneralLinear.hopfIdealInclusion R n (definingHopfIdeal R n C) := by
  unfold inclusion
  rfl

/-- The inclusion into the named general linear group scheme is a closed immersion. -/
instance isClosedImmersion_inclusion :
    AlgebraicGeometry.IsClosedImmersion (inclusion R n C).hom.hom.left := by
  rw [inclusion_def]
  infer_instance

/-- The quotient coordinate Hopf algebra, bundled with its finite-type property. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  FiniteTypeCommHopfAlgCat.quotient
    -- Not `GeneralLinear.finiteTypeCoordinateHopfAlgebra`: its body is not exposed, so its
    -- underlying object matches the coordinate Hopf algebra only propositionally here, and the
    -- defining Hopf ideal would not typecheck against it. The bundle is rebuilt with the
    -- object definitionally in place.
    (⟨GeneralLinear.coordinateHopfAlgebra R n,
      inferInstanceAs (Algebra.FiniteType R (GeneralLinear.coordinateHopfAlgebra R n))⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R n C)

/-- The finite-type package has the quotient coordinate Hopf algebra as its underlying
object. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R n C).obj = coordinateHopfAlgebra R n C := by
  rw [finiteTypeCoordinateHopfAlgebra]


/-! ### Algebra-valued points -/

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Mapping a point along the quotient coordinate morphism gives its ambient general-linear
point. `CommHopfAlgCat.quotientPointsHom` is by definition the points map induced by the
quotient morphism, so this is `coordinateMap_def` read on points; it is stated here to glue
the two applied forms at a value algebra. -/
-- Not `@[simp]`: `CommHopfAlgCat.mapPointsFunctor_app_apply` already rewrites the left-hand
-- side to its composition form before this lemma could apply.
theorem mapPointsFunctor_coordinateMap_app
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n C)
      (CommAlgCat.of R A)) :
    (CommHopfAlgCat.mapPointsFunctor (coordinateMap R n C)).app (CommAlgCat.of R A) f =
      CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n C)
        (CommAlgCat.of R A) f := by
  apply WithConv.ext
  rfl

/-- Evaluating the relation matrix at a point gives the form relation of its matrix. -/
private theorem ofConv_relationMatrix
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    (relationMatrix R n C).map g.ofConv =
      (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A) *
          C.map (algebraMap R A) *
          (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A)ᵀ -
        C.map (algebraMap R A) := by
  have hg : (GeneralLinear.genericMatrix R n).map g.ofConv =
      (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A) := by
    ext i j
    rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply]
    exact (GeneralLinear.pointToGeneralLinear_apply n g i j).symm
  rw [relationMatrix_map R n C g.ofConv, hg]

/-- **The ambient membership criterion**: an ambient point belongs to the subgroup cut out by
the defining Hopf ideal exactly when its matrix `M` satisfies `M C Mᵀ = C`.

This is the criterion the classical specializations consume: `TauCeti.Orthogonal` restates it
as membership in `Matrix.orthogonalGroup` (the `simp` normal form there), while
`TauCeti.Symplectic` uses it internally to build its points identification. It is deliberately
not a `simp` lemma — the orthogonal restatement is the normal form a user wants on that side,
and the symplectic side rewrites with it explicitly. -/
theorem mem_definingPointsSubgroup_iff
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n C)
        (CommAlgCat.of R A) ↔
      (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) * C.map (algebraMap R A) *
          (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) A)ᵀ =
        C.map (algebraMap R A) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, GeneralLinear.pointsMulEquiv_apply]
  constructor
  · intro h
    have hzero : (relationMatrix R n C).map g.ofConv = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply]
      exact h _ (HopfIdeal.mem_toIdeal.mp
        (definingHopfIdeal_toIdeal R n C ▸
          Ideal.subset_span (relationMatrix_mem_relationSet R n C i j)))
    rw [ofConv_relationMatrix R n C g] at hzero
    exact sub_eq_zero.mp hzero
  · intro h y hy
    have hzero : (relationMatrix R n C).map g.ofConv = 0 := by
      rw [ofConv_relationMatrix R n C g]
      exact sub_eq_zero.mpr h
    have hle : Ideal.span (relationSet R n C) ≤
        RingHom.ker (g.ofConv :
          GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] A) := by
      rw [Ideal.span_le]
      rintro _ ⟨ij, rfl⟩
      have := congrFun (congrFun hzero ij.1) ij.2
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    exact hle (definingHopfIdeal_toIdeal R n C ▸ HopfIdeal.mem_toIdeal.mpr hy)

end Points

end TauCeti.ConstantForm
