/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
public import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Diagonal representations of a diagonalizable group

A weight function `wt : Fin n → G` on a basis of a free module `M` makes `M` a comodule over the
group algebra `R[G]`, that is, a representation of the diagonalizable group `D(G)` which is
diagonal in that basis. This file records the resulting morphism of affine group schemes

```text
D(G) ⟶ GLₙ
```

and the criterion for it to be a closed immersion: the weights must generate the character group
`G`. In one direction this is immediate, since the coordinate morphism `O(GLₙ) ⟶ R[G]` hits
exactly the group algebra of the subgroup the weights generate; a diagonal representation whose
weights generate is therefore a faithful one.

For `G = ℤ^κ` this is the split torus `𝔾ₘ^κ` presented as a closed subgroup of `GLₙ` by the
weights of a representation, which is how the split maximal torus of a Chevalley group is written
down.

## Main declarations

* `TauCeti.DiagonalizableGroup.diagonalCoordinateMap`: the coordinate morphism
  `O(GLₙ) ⟶ R[G]` of a diagonal representation.
* `TauCeti.DiagonalizableGroup.diagonalGroupSchemeHom`: the group-scheme morphism `D(G) ⟶ GLₙ`.

## Main results

* `TauCeti.DiagonalizableGroup.pointToGeneralLinear_comp_diagonalCoordinateMap`: on points, the
  morphism is the diagonal matrix of the values of the weights at the point.
* `TauCeti.DiagonalizableGroup.surjective_diagonalCoordinateMap`: if the weights generate `G`,
  the coordinate morphism is surjective.
* `TauCeti.DiagonalizableGroup.isClosedImmersion_diagonalGroupSchemeHom`: if the weights generate
  `G`, the morphism `D(G) ⟶ GLₙ` is a closed immersion.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§2.2 and 3.2.
* J. S. Milne, *Algebraic Groups* (2017), §§4.a and 12.c.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti

universe u v w

namespace DiagonalizableGroup

/-! ## The coordinate morphism of a diagonal representation -/

section Coordinate

variable {R : Type u} {G : Type v} {M : Type w} {n : ℕ}
variable [CommRing R] [CommGroup G] [AddCommMonoid M] [Module R M]

/-- The coordinate Hopf-algebra morphism `O(GLₙ) ⟶ R[G]` of the representation of `D(G)` which is
diagonal in the basis `b` with weights `wt`. -/
noncomputable def diagonalCoordinateMap (b : Module.Basis (Fin n) R M) (wt : Fin n → G) :
    GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] MonoidAlgebra R G :=
  letI : Comodule R (MonoidAlgebra R G) M := Comodule.ofWeights b wt
  Comodule.coordinateBialgHom b

/-- The coordinate morphism of a diagonal representation sends the generic matrix to the diagonal
matrix of the characters. -/
theorem diagonalCoordinateMap_X (b : Module.Basis (Fin n) R M) (wt : Fin n → G) (i j : Fin n) :
    diagonalCoordinateMap b wt
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      Matrix.diagonal (fun x => MonoidAlgebra.single (wt x) (1 : R)) i j := by
  classical
  let : Comodule R (MonoidAlgebra R G) M := Comodule.ofWeights b wt
  have hdiag : Comodule.coefficientMatrix (C := MonoidAlgebra R G) b =
      Matrix.diagonal fun x => MonoidAlgebra.single (wt x) (1 : R) :=
    Comodule.coefficientMatrix_ofWeights b wt
  exact (Comodule.coordinateBialgHom_X (H := MonoidAlgebra R G) b i j).trans
    (congrFun (congrFun hdiag i) j)

/-- The antipode generators of `O(GLₙ)` are sent to the inverse characters. -/
theorem diagonalCoordinateMap_antipode_X (b : Module.Basis (Fin n) R M) (wt : Fin n → G)
    (i j : Fin n) :
    diagonalCoordinateMap b wt
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          ((GeneralLinear.localizedGenericMatrix R n)⁻¹ i j)) =
      Matrix.diagonal (fun x => MonoidAlgebra.single (wt x)⁻¹ (1 : R)) i j := by
  classical
  let : Comodule R (MonoidAlgebra R G) M := Comodule.ofWeights b wt
  have hdiag : Comodule.coefficientMatrix (C := MonoidAlgebra R G) b =
      Matrix.diagonal fun x => MonoidAlgebra.single (wt x) (1 : R) :=
    Comodule.coefficientMatrix_ofWeights b wt
  have hstep := Comodule.coordinateBialgHom_antipode_X (H := MonoidAlgebra R G) b i j
  rw [hdiag] at hstep
  refine hstep.trans ?_
  rcases eq_or_ne i j with rfl | hij
  · simp [MonoidAlgebra.antipode_single]
  · simp [Matrix.diagonal_apply_ne _ hij]

section Points

variable {A : Type*} [CommRing A] [Algebra R A]

/-- **On points, a diagonal representation is the diagonal matrix of the values of its weights.**
A point of `D(G)` is a character `χ` of `G`, and it acts on the `x`-th basis vector by `χ (wt x)`.
-/
theorem pointToGeneralLinear_comp_diagonalCoordinateMap (b : Module.Basis (Fin n) R M)
    (wt : Fin n → G) (q : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    (GeneralLinear.pointToGeneralLinear n
        (toConv (q.ofConv.comp (diagonalCoordinateMap b wt).toAlgHom)) :
          Matrix (Fin n) (Fin n) A) =
      Matrix.diagonal fun x => (charOfPoint q.ofConv (wt x) : A) := by
  classical
  ext i j
  rw [GeneralLinear.pointToGeneralLinear_apply, ofConv_toConv, AlgHom.comp_apply]
  change q.ofConv (diagonalCoordinateMap b wt _) = _
  rw [diagonalCoordinateMap_X]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Matrix.diagonal_apply_ne _ hij]

end Points

/-! ## Faithfulness -/

variable (R) in
/-- The set of characters whose group-algebra generator lies in a subalgebra is a submonoid. -/
private def singleSubmonoid (S : Subalgebra R (MonoidAlgebra R G)) : Submonoid G where
  carrier := {g | MonoidAlgebra.single g (1 : R) ∈ S}
  one_mem' := by
    simpa only [Set.mem_ofPred_eq, ← MonoidAlgebra.one_def] using S.one_mem
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simpa only [MonoidAlgebra.single_mul_single, one_mul] using S.mul_mem hg hh

private theorem mem_singleSubmonoid {S : Subalgebra R (MonoidAlgebra R G)} {g : G} :
    g ∈ singleSubmonoid R S ↔ MonoidAlgebra.single g (1 : R) ∈ S :=
  Iff.rfl

/-- Every generator of the group algebra whose character is generated by the weights lies in the
range of the coordinate morphism. -/
theorem single_mem_range_diagonalCoordinateMap (b : Module.Basis (Fin n) R M) (wt : Fin n → G)
    {g : G} (hg : g ∈ Subgroup.closure (Set.range wt)) :
    MonoidAlgebra.single g (1 : R) ∈ (diagonalCoordinateMap b wt).toAlgHom.range := by
  classical
  have hgen : ∀ i : Fin n,
      MonoidAlgebra.single (wt i) (1 : R) ∈ (diagonalCoordinateMap b wt).toAlgHom.range := by
    intro i
    have h := diagonalCoordinateMap_X b wt i i
    rw [Matrix.diagonal_apply_eq] at h
    exact ⟨_, h⟩
  have hinv : ∀ i : Fin n,
      MonoidAlgebra.single (wt i)⁻¹ (1 : R) ∈ (diagonalCoordinateMap b wt).toAlgHom.range := by
    intro i
    have h := diagonalCoordinateMap_antipode_X b wt i i
    rw [Matrix.diagonal_apply_eq] at h
    exact ⟨_, h⟩
  rw [← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hg
  refine mem_singleSubmonoid.1 (Submonoid.closure_le.2 ?_ hg)
  rintro x (⟨i, rfl⟩ | hx)
  · exact mem_singleSubmonoid.2 (hgen i)
  · obtain ⟨i, hi⟩ := Set.mem_inv.1 hx
    refine mem_singleSubmonoid.2 ?_
    rw [show x = (wt i)⁻¹ from by rw [hi, inv_inv]]
    exact hinv i

/-- **A diagonal representation whose weights generate the character group is faithful**: its
coordinate morphism `O(GLₙ) ⟶ R[G]` is surjective. -/
theorem surjective_diagonalCoordinateMap (b : Module.Basis (Fin n) R M) (wt : Fin n → G)
    (hwt : Subgroup.closure (Set.range wt) = ⊤) :
    Function.Surjective (diagonalCoordinateMap b wt) := by
  classical
  have hsurj : Function.Surjective (diagonalCoordinateMap b wt).toAlgHom := by
    rw [← AlgHom.range_eq_top]
    refine top_unique fun x _ => ?_
    rw [← MonoidAlgebra.sum_coeff_single x, Finsupp.sum]
    refine Subalgebra.sum_mem _ fun g _ => ?_
    have hg : MonoidAlgebra.single g (1 : R) ∈ (diagonalCoordinateMap b wt).toAlgHom.range :=
      single_mem_range_diagonalCoordinateMap b wt (hwt ▸ Subgroup.mem_top g)
    simpa only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one] using
      Subalgebra.smul_mem _ hg (MonoidAlgebra.coeff x g)
  exact hsurj

end Coordinate

/-! ## The morphism of group schemes -/

section Scheme

variable {R : Type u} {M : Type u} {n : ℕ}
variable [CommRing R] [AddCommMonoid M] [Module R M]
variable (G : FGCommGrpCat.{u})

/-- The morphism of affine group schemes `D(G) ⟶ GLₙ` attached to the representation of `D(G)`
which is diagonal in the basis `b` with weights `wt`. -/
noncomputable def diagonalGroupSchemeHom (b : Module.Basis (Fin n) R M) (wt : Fin n → G) :
    groupScheme R G ⟶ GeneralLinear.groupScheme R n :=
  letI : Comodule R (MonoidAlgebra R G) M := Comodule.ofWeights b wt
  eqToHom (groupScheme_def R G) ≫ Comodule.coordinateGroupSchemeHom b

/-- The diagonal group-scheme morphism is relative spectrum applied contravariantly to its
coordinate morphism, transported across the named presentation of `D(G)`. -/
theorem diagonalGroupSchemeHom_def (b : Module.Basis (Fin n) R M) (wt : Fin n → G) :
    diagonalGroupSchemeHom G b wt =
      eqToHom (groupScheme_def R G) ≫
        (hopfSpec (CommRingCat.of R)).map
          (CommHopfAlgCat.ofHom (diagonalCoordinateMap b wt)).op ≫
        eqToHom (GeneralLinear.groupScheme_def R n).symm := by
  let : Comodule R (MonoidAlgebra R G) M := Comodule.ofWeights b wt
  rw [diagonalGroupSchemeHom, Comodule.coordinateGroupSchemeHom_def]
  rfl

/-- **A diagonal representation whose weights generate the character group presents `D(G)` as a
closed subgroup of `GLₙ`.** -/
theorem isClosedImmersion_diagonalGroupSchemeHom (b : Module.Basis (Fin n) R M)
    (wt : Fin n → G) (hwt : Subgroup.closure (Set.range wt) = ⊤) :
    IsClosedImmersion (diagonalGroupSchemeHom G b wt).hom.hom.left := by
  let : Comodule R (MonoidAlgebra R G) M := Comodule.ofWeights b wt
  have hc : IsClosedImmersion
      (Comodule.coordinateGroupSchemeHom (H := MonoidAlgebra R G) b).hom.hom.left :=
    (Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff b).2
      (surjective_diagonalCoordinateMap b wt hwt)
  have he : IsIso (eqToHom (groupScheme_def R G)).hom.hom.left :=
    ((Over.forget (Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
        (eqToIso (groupScheme_def R G)))).isIso_hom
  have hcomp : IsClosedImmersion
      ((eqToHom (groupScheme_def R G)).hom.hom.left ≫
        (Comodule.coordinateGroupSchemeHom (H := MonoidAlgebra R G) b).hom.hom.left) :=
    (@MorphismProperty.cancel_left_of_respectsIso
      Scheme _ @IsClosedImmersion inferInstance _ _ _ _ _ he).2 hc
  rw [diagonalGroupSchemeHom]
  simpa only [Grp.comp', Mon.comp_hom', Over.comp_left] using hcomp

end Scheme

end DiagonalizableGroup

end TauCeti
