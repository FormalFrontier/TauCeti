/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# The grading of a symmetric algebra

Let `M` be a free module over a commutative semiring. The powers of the image of `M` in its
symmetric algebra are not merely a spanning family: they form an internal direct sum. Thus every
element of the symmetric algebra has a unique finite decomposition into homogeneous terms.

The proof transports the standard total-degree decomposition of a multivariate polynomial ring
across the algebra equivalence associated to a basis of `M`. Besides the intrinsic result for a
free module, the comparison with multivariate homogeneous polynomials is exposed for a specified
basis.

## Main results

* `map_homogeneousSubmodule_equivMvPolynomial`: a basis-induced equivalence carries the degree
  `n` part of a symmetric algebra to the degree `n` part of a multivariate polynomial ring.
* `isInternal_homogeneousSubmodule_of_basis`: a specified basis makes the homogeneous pieces an
  internal direct sum.
* `isInternal_homogeneousSubmodule`: the intrinsic formulation for a free module.
* `homogeneousDecomposition`: the resulting direct-sum decomposition.
-/

public section

namespace TauCeti.SymmetricAlgebra

open Module

universe u v w

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The algebra equivalence induced by a basis preserves homogeneous degree. -/
@[simp]
theorem map_homogeneousSubmodule_equivMvPolynomial {ι : Type w} (b : Basis ι R M) (n : ℕ) :
    (homogeneousSubmodule R M n).map
        (SymmetricAlgebra.equivMvPolynomial b).toLinearMap =
      MvPolynomial.homogeneousSubmodule ι R n := by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, ← AlgEquiv.toLinearEquiv_toLinearMap,
    ← AlgEquiv.toAlgHom_toLinearMap,
    Submodule.map_pow (LinearMap.range (SymmetricAlgebra.ι R M))
      (SymmetricAlgebra.equivMvPolynomial b).toAlgHom n]
  congr 1
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, LinearMap.range_eq_map, ← b.span_eq,
    Submodule.map_span, Submodule.map_span, ← Set.image_comp, ← Set.range_comp]
  simp only [Function.comp_def, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
    SymmetricAlgebra.equivMvPolynomial_ι_apply]

/-- Membership in a homogeneous piece can be tested after applying the polynomial equivalence
induced by a basis.

This is not a `simp` lemma: `MvPolynomial.mem_homogeneousSubmodule` already rewrites the
left-hand side to `MvPolynomial.IsHomogeneous`, so the orientation below is not simp-normal. The
simp-normal form of the characterisation is
`SymmetricAlgebra.isHomogeneous_equivMvPolynomial_iff`. -/
theorem _root_.SymmetricAlgebra.equivMvPolynomial_mem_homogeneousSubmodule_iff {ι : Type w}
    (b : Basis ι R M) (n : ℕ) (p : SymmetricAlgebra R M) :
    SymmetricAlgebra.equivMvPolynomial b p ∈ MvPolynomial.homogeneousSubmodule ι R n ↔
      p ∈ homogeneousSubmodule R M n := by
  rw [← map_homogeneousSubmodule_equivMvPolynomial R M b n,
    Submodule.mem_map_equiv (e := (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv)]
  simp

/-- An element of a symmetric algebra is homogeneous of degree `n` exactly when its image under
the polynomial equivalence induced by a basis is. -/
@[simp]
theorem _root_.SymmetricAlgebra.isHomogeneous_equivMvPolynomial_iff {ι : Type w}
    (b : Basis ι R M) (n : ℕ) (p : SymmetricAlgebra R M) :
    (SymmetricAlgebra.equivMvPolynomial b p).IsHomogeneous n ↔ p ∈ homogeneousSubmodule R M n :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).symm.trans
    (SymmetricAlgebra.equivMvPolynomial_mem_homogeneousSubmodule_iff R M b n p)

/-- A basis makes the homogeneous pieces an internal direct sum decomposition of its symmetric
algebra. -/
theorem isInternal_homogeneousSubmodule_of_basis {ι : Type w} (b : Basis ι R M) :
    DirectSum.IsInternal (homogeneousSubmodule R M) := by
  have hmap : ∀ n : ℕ, (homogeneousSubmodule R M n).map
      ((SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv :
        SymmetricAlgebra R M →ₗ[R] MvPolynomial ι R) =
      MvPolynomial.homogeneousSubmodule ι R n := fun n ↦ by
    rw [AlgEquiv.toLinearEquiv_toLinearMap]
    exact map_homogeneousSubmodule_equivMvPolynomial R M b n
  -- The basis equivalence restricts to an equivalence of each degree-`n` piece.
  let φ (n : ℕ) : homogeneousSubmodule R M n ≃ₗ[R] MvPolynomial.homogeneousSubmodule ι R n :=
    ((SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv.submoduleMap _).trans
      (LinearEquiv.ofEq _ _ (hmap n))
  have hφ : ∀ (n : ℕ) (x : homogeneousSubmodule R M n),
      (φ n x : MvPolynomial ι R) = SymmetricAlgebra.equivMvPolynomial b x := fun _ _ ↦ rfl
  -- Hence recomposition on the symmetric algebra is conjugate to recomposition on polynomials.
  have hsq : ⇑(SymmetricAlgebra.equivMvPolynomial b) ∘
        ⇑(DirectSum.coeAddMonoidHom (homogeneousSubmodule R M)) =
      ⇑(DirectSum.coeAddMonoidHom (MvPolynomial.homogeneousSubmodule ι R)) ∘
        ⇑(DirectSum.lmap fun n ↦ (φ n).toLinearMap) := by
    refine funext fun x ↦ ?_
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n y => simpa using (hφ n y).symm
    | add y z hy hz => simpa using congrArg₂ (· + ·) hy hz
  have hlmap : Function.Bijective (DirectSum.lmap fun n ↦ (φ n).toLinearMap) :=
    ⟨(DirectSum.lmap_injective _).2 fun n ↦ (φ n).injective,
      (DirectSum.lmap_surjective _).2 fun n ↦ (φ n).surjective⟩
  refine ((SymmetricAlgebra.equivMvPolynomial b).bijective.of_comp_iff' _).mp ?_
  rw [hsq]
  exact ((MvPolynomial.decomposition :
    DirectSum.Decomposition (MvPolynomial.homogeneousSubmodule ι R)).isInternal).comp hlmap

/-- The homogeneous pieces form an internal direct sum decomposition of the symmetric algebra of
a free module. -/
theorem isInternal_homogeneousSubmodule [Module.Free R M] :
    DirectSum.IsInternal (homogeneousSubmodule R M) := by
  let ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  exact isInternal_homogeneousSubmodule_of_basis R M b

/-- A basis makes the homogeneous pieces of its symmetric algebra independent. -/
theorem iSupIndep_homogeneousSubmodule_of_basis {ι : Type w} (b : Basis ι R M) :
    iSupIndep (homogeneousSubmodule R M) :=
  (isInternal_homogeneousSubmodule_of_basis R M b).submodule_iSupIndep

/-- The homogeneous pieces of the symmetric algebra of a free module are independent. -/
theorem iSupIndep_homogeneousSubmodule [Module.Free R M] :
    iSupIndep (homogeneousSubmodule R M) :=
  (isInternal_homogeneousSubmodule R M).submodule_iSupIndep

/-- The canonical decomposition of the symmetric algebra of a free module into its homogeneous
pieces. -/
@[instance_reducible]
noncomputable def homogeneousDecomposition [Module.Free R M] :
    DirectSum.Decomposition (homogeneousSubmodule R M) :=
  (isInternal_homogeneousSubmodule R M).chooseDecomposition

end TauCeti.SymmetricAlgebra
