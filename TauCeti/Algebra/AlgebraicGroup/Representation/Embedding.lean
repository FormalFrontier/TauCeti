/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType

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

## Main declaration

* `TauCeti.Comodule.matrixCoefficientSubalgebra_le_coordinateBialgHom_range`: the matrix
  coefficient subalgebra is contained in the range of the coordinate morphism.
* `TauCeti.Comodule.exists_coordinateBialgHom_surjective`: a finite-type commutative Hopf
  algebra over a field admits a finite-dimensional regular subcomodule whose coordinate
  morphism from `O(GLₙ)` is surjective.

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
