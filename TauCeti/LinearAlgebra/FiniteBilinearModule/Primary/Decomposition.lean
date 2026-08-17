/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PrimaryDecomposition
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component

/-!
# Primary decomposition of finite bilinear and quadratic modules

This file upgrades the primary decomposition of the underlying finite abelian group to the
form-theoretic decompositions used for discriminant forms. For a finite bilinear module, its
primary components form an orthogonal product whose pairing is the sum of the restricted
pairings. For a finite quadratic module, the analogous quadratic map is the sum of the restricted
quadratic maps.

The canonical additive equivalence is an isometry in both settings. This follows from the
orthogonality and finite-sum identities proved in
`TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component`.

## Main results

* `TauCeti.FiniteBilinearModule.primaryDecomposition`: the canonical primary decomposition as a
  bilinear isometry.
* `TauCeti.FiniteQuadraticModule.primaryDecomposition`: the canonical primary decomposition as a
  quadratic isometry.
* `TauCeti.FiniteBilinearModule.isNondegenerate_primaryComponents` and
  `TauCeti.FiniteQuadraticModule.isNondegenerate_primaryComponents`: nondegeneracy is equivalent
  to nondegeneracy of the orthogonal product.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

This is the canonical-primary-decomposition part of Layer 3 of
`TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

/-- The orthogonal product of the prime-primary restrictions of a finite bilinear module. -/
@[expose] noncomputable def primaryComponents : FiniteBilinearModule where
  carrier := ∀ p : (Nat.card A).primeFactors,
    AddCommGroup.primaryComponent A p.1
  pairing :=
    { toFun := fun x ↦
        { toFun := fun y ↦ ∑ p, A.pairing (x p) (y p)
          map_zero' := by simp
          map_add' := fun y z ↦ by
            simp only [Pi.add_apply, AddSubgroup.coe_add, pairing_add_right,
              Finset.sum_add_distrib] }
      map_zero' := by
        ext y
        -- Expose the pointwise formula while constructing the bundled pairing itself.
        change ∑ p, A.pairing 0 (y p) = 0
        apply Finset.sum_eq_zero
        intro p _
        exact A.pairing_zero_left (y p)
      map_add' := fun x y ↦ by
        ext z
        -- Expose the pointwise formula while constructing the bundled pairing itself.
        change ∑ p, A.pairing (x p + y p) (z p) =
          (∑ p, A.pairing (x p) (z p)) + ∑ p, A.pairing (y p) (z p)
        simp only [pairing_add_left, Finset.sum_add_distrib] }
  pairing_comm x y := by
    -- Expose the pointwise formula while proving the final structure field.
    change (∑ p, A.pairing (x p) (y p)) = ∑ p, A.pairing (y p) (x p)
    apply Finset.sum_congr rfl
    intro p _
    exact A.pairing_comm (x p) (y p)

/-- The pairing on the orthogonal product is the sum of the component pairings. -/
@[simp]
theorem primaryComponents_pairing (x y : A.primaryComponents) :
    A.primaryComponents.pairing x y = ∑ p, A.pairing (x p) (y p) := by
  rfl

/-- The canonical primary decomposition is a bilinear isometry. -/
noncomputable def primaryDecomposition : Isometry A.primaryComponents A where
  toAddEquiv := AddCommGroup.primaryDecomposition A
  map_pairing' x y := by
    -- Unfolding the carrier variables and goal together aligns the bundled carrier's synthesized
    -- additive instance with the dependent-product instance used by the group decomposition.
    unfold primaryComponents at x y ⊢
    rw [AddCommGroup.primaryDecomposition_apply, AddCommGroup.primaryDecomposition_apply]
    change A.pairing (∑ p, (x p : A)) (∑ p, (y p : A)) =
      ∑ p, A.pairing (x p) (y p)
    exact A.pairing_sum_eq_sum_pairing_of_mem_primaryComponent
      Finset.univ Subtype.val (fun p ↦ x p) (fun p ↦ y p)
      (fun p _ ↦ Nat.prime_of_mem_primeFactors p.2)
      (fun p _ q _ hpq ↦ by simpa using hpq)
      (fun p _ ↦ (x p).2) (fun p _ ↦ (y p).2)

/-- The bilinear primary-decomposition isometry maps a tuple to its component sum. -/
@[simp]
theorem primaryDecomposition_apply (x : A.primaryComponents) :
    A.primaryDecomposition x = ∑ p, (x p : A) :=
  AddCommGroup.primaryDecomposition_apply A x

/-- The orthogonal product of primary components is nondegenerate exactly when the original
finite bilinear module is nondegenerate. -/
@[simp]
theorem isNondegenerate_primaryComponents :
    A.primaryComponents.IsNondegenerate ↔ A.IsNondegenerate :=
  A.primaryDecomposition.isNondegenerate_iff

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- The orthogonal product of the prime-primary restrictions of a finite quadratic module. -/
@[expose] noncomputable def primaryComponents : FiniteQuadraticModule where
  toFiniteBilinearModule := A.toFiniteBilinearModule.primaryComponents
  quadratic := ∑ p : (Nat.card A).primeFactors,
    (A.restrict (AddCommGroup.primaryComponent A p.1)).quadratic.comp (LinearMap.proj p)
  polar_eq_pairing' x y := by
    simp only [QuadraticMap.polar, sum_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    exact A.polar_eq_pairing (x p) (y p)

/-- The quadratic map on the orthogonal product is the sum of the component quadratic maps. -/
@[simp]
theorem primaryComponents_quadratic (x : A.primaryComponents) :
    A.primaryComponents.quadratic x = ∑ p, A.quadratic (x p) := by
  -- Unfold the carrier together with the structure so the dependent-product module instances
  -- used by `QuadraticMap.sum_apply` agree definitionally.
  unfold FiniteQuadraticModule.primaryComponents at x ⊢
  unfold FiniteBilinearModule.primaryComponents at x ⊢
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rfl

/-- The canonical primary decomposition is a quadratic isometry. -/
noncomputable def primaryDecomposition : Isometry A.primaryComponents A where
  toLinearEquiv := (AddCommGroup.primaryDecomposition A).toIntLinearEquiv
  map_app' x := by
    -- Unfolding the carrier variable and goal together aligns the bundled carrier's synthesized
    -- module instance with the dependent-product instance used by the group decomposition.
    unfold FiniteQuadraticModule.primaryComponents at x ⊢
    unfold FiniteBilinearModule.primaryComponents at x ⊢
    rw [sum_apply]
    change A.quadratic (AddCommGroup.primaryDecomposition A x) =
      ∑ p, A.quadratic (x p)
    rw [AddCommGroup.primaryDecomposition_apply]
    exact A.quadratic_sum_of_mem_primaryComponent Finset.univ Subtype.val (fun p ↦ x p)
      (fun p _ ↦ Nat.prime_of_mem_primeFactors p.2)
      (fun p _ q _ hpq ↦ by simpa using hpq)
      (fun p _ ↦ (x p).2)

/-- The quadratic primary-decomposition isometry maps a tuple to its component sum. -/
@[simp]
theorem primaryDecomposition_apply (x : A.primaryComponents) :
    A.primaryDecomposition x = ∑ p, (x p : A) :=
  AddCommGroup.primaryDecomposition_apply A x

/-- The orthogonal product of primary components is nondegenerate exactly when the original
finite quadratic module is nondegenerate. -/
@[simp]
theorem isNondegenerate_primaryComponents :
    A.primaryComponents.IsNondegenerate ↔ A.IsNondegenerate :=
  A.primaryDecomposition.isNondegenerate_iff

end FiniteQuadraticModule

end TauCeti
