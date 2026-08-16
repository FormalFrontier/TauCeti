/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion
import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence

/-!
# Embedding a finite-type affine group in a general linear group

Let `H` be a commutative Hopf algebra of finite type over a field `k`. The fundamental theorem
of coalgebras places a finite set of algebra generators of `H` in a finite-dimensional
subcomodule `M` of the regular comodule. The matrix coefficients of `M` then generate `H` as a
`k`-algebra. After choosing a finite basis of `M`, every matrix coefficient is a linear
combination of the entries of its coefficient matrix. Hence the associated coordinate morphism

```text
O(GLₙ) ⟶ H
```

is surjective. Contravariantly, its spectrum is a closed immersion of the affine group scheme
represented by `H` into `GLₙ`.

The coordinate-algebra statement permits independent universes for `k` and `H`. The final
group-scheme statement uses the same universe for them, as required by Mathlib's current
`hopfSpec` construction.

## Main declarations

* `TauCeti.Comodule.matrixCoefficientSubalgebra_le_coordinateBialgHom_range`: the matrix
  coefficient subalgebra is contained in the range of the coordinate morphism.
* `TauCeti.Comodule.exists_coordinateBialgHom_surjective`: a finite-type commutative Hopf
  algebra over a field admits a finite-dimensional regular subcomodule whose coordinate
  morphism from `O(GLₙ)` is surjective.
* `TauCeti.Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom`: the group scheme
  represented by a finite-type commutative Hopf algebra embeds as a closed subgroup of some
  `GLₙ`.
* `TauCeti.AffineGroupSchemeCat.exists_isClosedImmersion_generalLinear`: every finite-type
  affine group scheme over a field embeds as a closed subgroup of some `GLₙ`.

## References

This is the coordinate-algebra form of the affine-group embedding theorem; see J. S. Milne,
*Algebraic Groups* (2017), Proposition 4.7 and Theorem 4.9. It advances Layer 1, "Embedding
theorem (hard)", of the ReductiveGroups roadmap.
-/

public section

open Module

namespace TauCeti.Comodule

universe u v w

noncomputable section

variable {k : Type u} {H : Type v} {M : Type w}
variable {n : ℕ}

section Range

variable [CommRing k] [CommRing H] [HopfAlgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

private theorem matrixCoefficient_mem_range_coordinateBialgHom
    (b : Basis (Fin n) k M) (φ : M →ₗ[k] k) (m : M) :
    matrixCoefficient (R := k) (C := H) φ m ∈
      (coordinateBialgHom (H := H) b).toAlgHom.range := by
  have hcoeff (j : Fin n) :
      matrixCoefficient (R := k) (C := H) φ (b j) =
        ∑ i, φ (b i) • coefficientMatrix (C := H) b i j := by
    rw [matrixCoefficient_def, coact_basis_eq_sum_coefficientMatrix, map_sum]
    simp
  rw [← b.sum_repr m]
  have hsum := map_sum (matrixCoefficientLinear (R := k) (C := H) φ)
    (fun j => (b.repr m) j • b j) Finset.univ
  simp only [matrixCoefficientLinear_apply] at hsum
  rw [hsum]
  refine (coordinateBialgHom (H := H) b).toAlgHom.range.sum_mem
    (t := Finset.univ) ?_
  intro j _
  rw [matrixCoefficient_smul, hcoeff]
  refine (coordinateBialgHom (H := H) b).toAlgHom.range.smul_mem ?_ ((b.repr m) j)
  refine (coordinateBialgHom (H := H) b).toAlgHom.range.sum_mem
    (t := Finset.univ) ?_
  intro i _
  refine (coordinateBialgHom (H := H) b).toAlgHom.range.smul_mem ?_ (φ (b i))
  exact ⟨_, coordinateBialgHom_X b i j⟩

/-- The matrix coefficient subalgebra of a finite free comodule is contained in the range of
its coordinate bialgebra morphism. -/
theorem matrixCoefficientSubalgebra_le_coordinateBialgHom_range
    (b : Basis (Fin n) k M) :
    matrixCoefficientSubalgebra (R := k) (C := H) (M := M) ≤
      (coordinateBialgHom (H := H) b).toAlgHom.range :=
  matrixCoefficientSubalgebra_le (R := k) (C := H) (M := M) fun φ m =>
    matrixCoefficient_mem_range_coordinateBialgHom b φ m

end Range

variable [Field k] [CommRing H] [HopfAlgebra k H]

/-- **A finite-type commutative Hopf algebra over a field is a quotient of the coordinate
ring of some general linear group.** More precisely, it has a finite-dimensional subcomodule
of its regular comodule and a basis for which the associated coordinate bialgebra morphism
`O(GLₙ) → H` is surjective.

Contravariantly, the affine group scheme represented by `H` embeds as a closed subgroup of
`GLₙ`. -/
theorem exists_coordinateBialgHom_surjective [Algebra.FiniteType k H] :
    ∃ (M : Subcomodule k H H) (n : ℕ) (b : Basis (Fin n) k M),
      Function.Surjective (coordinateBialgHom (H := H) b) := by
  let _ : Ring H := Algebra.semiringToRing k
  obtain ⟨M, hMfinite, hMcoeff⟩ :=
    exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top (k := k) (C := H)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Module.Free k M := Module.Free.of_divisionRing k M
  let : Module.Finite k M := hMfinite
  let b := Module.finBasis k M
  refine ⟨M, Module.finrank k M, b, ?_⟩
  have hsurjective :
      Function.Surjective (coordinateBialgHom (H := H) b).toAlgHom := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← hMcoeff]
    exact matrixCoefficientSubalgebra_le_coordinateBialgHom_range b
  exact hsurjective

end

end TauCeti.Comodule

namespace TauCeti.Comodule

section GroupScheme

open CategoryTheory AlgebraicGeometry

variable {k H M : Type u} {n : ℕ}
variable [CommRing k] [CommRing H] [HopfAlgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- The morphism from the affine group scheme represented by `H` to `GLₙ` associated to a
comodule with a basis indexed by `Fin n`.

This is relative spectrum applied contravariantly to the comodule's coordinate Hopf-algebra
morphism `O(GLₙ) ⟶ H`. -/
noncomputable def coordinateGroupSchemeHom (b : Basis (Fin n) k M) :
    (hopfSpec (CommRingCat.of k)).obj (Opposite.op (CommHopfAlgCat.of k H)) ⟶
      GeneralLinear.groupScheme k n :=
  (hopfSpec (CommRingCat.of k)).map
      (CommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b)).op ≫
    eqToHom (GeneralLinear.groupScheme_def k n).symm

/-- The group-scheme morphism associated to a comodule is the relative spectrum of its
coordinate Hopf-algebra morphism, followed by the defining identification of `GLₙ`. -/
theorem coordinateGroupSchemeHom_def (b : Basis (Fin n) k M) :
    coordinateGroupSchemeHom (H := H) b =
      (hopfSpec (CommRingCat.of k)).map
          (CommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b)).op ≫
        eqToHom (GeneralLinear.groupScheme_def k n).symm := (rfl)

/-- The group-scheme morphism associated to a finite free comodule is a closed immersion if
and only if its coordinate Hopf-algebra morphism is surjective. -/
@[simp]
theorem isClosedImmersion_coordinateGroupSchemeHom_iff (b : Basis (Fin n) k M) :
    IsClosedImmersion (coordinateGroupSchemeHom (H := H) b).hom.hom.left ↔
      Function.Surjective (coordinateBialgHom (H := H) b) := by
  rw [coordinateGroupSchemeHom_def]
  exact CommHopfAlgCat.isClosedImmersion_hopfSpec_map_comp_eqToHom_iff
    (GeneralLinear.groupScheme_def k n) _

end GroupScheme

section FiniteType

open AlgebraicGeometry

variable {k H : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H]

/-- The affine group scheme represented by a finite-type commutative Hopf algebra over a field
embeds as a closed subgroup of some general linear group. More precisely, a finite-dimensional
subcomodule of the regular comodule and a basis determine a closed immersion into `GLₙ`. -/
theorem exists_isClosedImmersion_coordinateGroupSchemeHom [Algebra.FiniteType k H] :
    ∃ (M : Subcomodule k H H) (n : ℕ) (b : Basis (Fin n) k M),
      IsClosedImmersion (coordinateGroupSchemeHom (H := H) b).hom.hom.left := by
  obtain ⟨M, n, b, hb⟩ := exists_coordinateBialgHom_surjective (k := k) (H := H)
  exact ⟨M, n, b, (isClosedImmersion_coordinateGroupSchemeHom_iff b).2 hb⟩

end FiniteType

end TauCeti.Comodule

namespace TauCeti.AffineGroupSchemeCat

open CategoryTheory AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

/-- **Every finite-type affine group scheme over a field embeds as a closed subgroup of some
general linear group.** -/
theorem exists_isClosedImmersion_generalLinear
    (G : AffineGroupSchemeCat (CommRingCat.of k)) [LocallyOfFiniteType G.obj.X.hom] :
    ∃ (n : ℕ) (f : G.obj ⟶ GeneralLinear.groupScheme k n),
      IsClosedImmersion f.hom.hom.left := by
  let E := commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)
  let A := (E.inverse.obj G).unop
  let e : G.obj ≅ (hopfSpec (CommRingCat.of k)).obj (Opposite.op A) :=
    ((affineGroupSchemeProperty (CommRingCat.of k)).ι.mapIso (E.counitIso.app G)).symm ≪≫
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of k)).app (E.inverse.obj G)
  have hAfinite : Algebra.FiniteType k A := by
    let : MorphismProperty.RespectsIso
        (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hA : LocallyOfFiniteType
        ((hopfSpec (CommRingCat.of k)).obj (Opposite.op A)).X.hom :=
      (MorphismProperty.over_iso_iff
        (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
          ((Grp.forget _).mapIso e)).mp
        (inferInstance : LocallyOfFiniteType G.obj.X.hom)
    rw [hopfSpec_obj_X_hom] at hA
    apply RingHom.finiteType_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hA
  let : Algebra.FiniteType k A := hAfinite
  obtain ⟨M, n, b, hb⟩ :=
    Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom (k := k) (H := A)
  refine ⟨n, e.hom ≫ Comodule.coordinateGroupSchemeHom (H := A) b, ?_⟩
  let _ : IsIso e.hom.hom.hom.left :=
    ((Over.forget (Spec (CommRingCat.of k))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of k)))).mapIso e)).isIso_hom
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  exact hb

end TauCeti.AffineGroupSchemeCat
