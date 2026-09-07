/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# The grading of a symmetric algebra

Let `M` be a module over a commutative semiring. The powers of the image of `M` in its symmetric
algebra are not merely a spanning family: they form an internal direct sum. Thus every element of
the symmetric algebra has a unique finite decomposition into homogeneous terms.

Consequently a map out of the symmetric algebra can be studied degree by degree: it is determined
by its restrictions to the homogeneous pieces, so two such maps agreeing on all of them agree, and
if it carries each piece into a corresponding summand of an internal decomposition of its target,
then it is injective as soon as all of those restrictions are.

Directness comes from the universal property: the external direct sum of the homogeneous pieces is
again a commutative algebra, so sending a generator to its degree-one copy produces an algebra map
splitting the recomposition map. No freeness of `M` is needed. This argument follows Mathlib's
`TensorAlgebra.gradedAlgebra`, in `Mathlib/LinearAlgebra/TensorAlgebra/Grading.lean`, which grades
the tensor algebra the same way. When `M` does carry a basis, the degree pieces are moreover
compared with the total-degree pieces of a multivariate polynomial ring.

## Main results

* `homogeneousDecomposition`: the homogeneous pieces decompose the symmetric algebra.
* `isInternal_homogeneousSubmodule`: the same statement as an internal direct sum.
* `map_homogeneousSubmodule_equivMvPolynomial`: a basis-induced equivalence carries the degree
  `n` part of a symmetric algebra to the degree `n` part of a multivariate polynomial ring.
* `SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff`: the degreewise form of that comparison.
-/

public section

namespace TauCeti.SymmetricAlgebra

open Module

open scoped DirectSum

universe u v w

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The generator map of a symmetric algebra, corestricted to the degree-one homogeneous piece and
then included into the external direct sum of all of them. -/
private noncomputable def gradedι : M →ₗ[R] ⨁ n, homogeneousSubmodule R M n :=
  DirectSum.lof R ℕ (fun n ↦ homogeneousSubmodule R M n) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ fun m ↦ by
      simpa only [pow_one] using LinearMap.mem_range_self _ m

/-- The defining formula for `gradedι`. -/
private theorem gradedι_apply (m : M) :
    gradedι R M m = DirectSum.of (fun n ↦ homogeneousSubmodule R M n) 1
      ⟨SymmetricAlgebra.ι R M m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

/-- The canonical decomposition of a symmetric algebra into its homogeneous pieces. No freeness of
`M` is needed: the external direct sum of the pieces is itself a commutative `R`-algebra, so the
universal property turns the degree-one copy of the generator map into an algebra map splitting the
recomposition map. -/
@[instance_reducible]
noncomputable def homogeneousDecomposition :
    DirectSum.Decomposition (homogeneousSubmodule R M) :=
  letI : GradedAlgebra (homogeneousSubmodule R M) :=
    GradedAlgebra.ofAlgHom _ (SymmetricAlgebra.lift (gradedι R M))
      (by
        ext m
        simp only [LinearMap.coe_comp, LinearMap.coe_coe, AlgHom.coe_comp, Function.comp_apply,
          SymmetricAlgebra.lift_ι_apply, gradedι_apply, DirectSum.coeAlgHom_of, AlgHom.coe_id,
          id_eq])
      -- A homogeneous element is a sum of products of `n` generators, so induction on the power
      -- reduces to the degree-one case.
      fun n x ↦ by
        obtain ⟨x, hx⟩ := x
        dsimp only [DirectSum.lof_eq_of]
        induction hx using Submodule.pow_induction_on_left' with
        | algebraMap r => rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
        | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, ← map_add]; rfl
        | mem_mul m hm i x hx ih =>
            obtain ⟨_, rfl⟩ := hm
            rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply, gradedι_apply, DirectSum.of_mul_of]
            exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)
  inferInstance

/-- The homogeneous pieces form an internal direct sum decomposition of the symmetric algebra. -/
theorem isInternal_homogeneousSubmodule :
    DirectSum.IsInternal (homogeneousSubmodule R M) :=
  letI := homogeneousDecomposition R M
  DirectSum.Decomposition.isInternal _

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

/-- An element of a symmetric algebra is homogeneous of degree `n` exactly when its image under
the polynomial equivalence induced by a basis is. -/
@[simp]
theorem _root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff {ι : Type w}
    (b : Basis ι R M) (n : ℕ) (p : SymmetricAlgebra R M) :
    (SymmetricAlgebra.equivMvPolynomial b p).IsHomogeneous n ↔ p ∈ homogeneousSubmodule R M n := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, ← map_homogeneousSubmodule_equivMvPolynomial R M b n,
    Submodule.mem_map_equiv (e := (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv)]
  simp

end TauCeti.SymmetricAlgebra
