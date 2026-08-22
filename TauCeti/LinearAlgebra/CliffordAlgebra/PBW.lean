/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.FiltrationGradedEquiv

/-!
# PBW equivalence for a Clifford filtration

This file identifies the associated graded algebra of the Clifford degree filtration with the
exterior algebra when `2` is invertible. It combines the equivalences on the successive quotients
with their compatibility with homogeneous multiplication.

This completes the associated-graded-algebra part of Layer 0 in the
[spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md#layer-0-the-clifford-algebra-its-universal-property-and-the-two-gradings).

## Main definition

* `CliffordAlgebra.associatedGradedEquivExterior`: the algebra equivalence from
  the associated graded of the Clifford filtration to the exterior algebra.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Proposition I.1.2.
-/

public section

open scoped DirectSum

universe u v

namespace CliffordAlgebra

open TauCeti.Algebra.wordFiltration

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

private noncomputable def scalarEquivFiltrationZero :
    R ≃ₗ[R] filtration Q 0 :=
  (LinearEquiv.ofInjective (Algebra.linearMap R (CliffordAlgebra Q))
    (algebraMap_injective Q)).trans
    (LinearEquiv.ofEq _ _
      (Submodule.one_eq_range.symm.trans
        (TauCeti.Algebra.wordFiltration_zero (ι Q)).symm))

private noncomputable def gradedPieceZeroEquivExteriorPower :
    GradedPiece (ι Q) 0 ≃ₗ[R] ⋀[R]^0 M :=
  (Submodule.quotEquivOfEqBot _ (previousRestricted_zero (ι Q))).trans
    ((scalarEquivFiltrationZero Q).symm.trans (exteriorPower.zeroEquiv R M).symm)

/-- The canonical equivalence from each graded filtration piece to the corresponding exterior
power. -/
noncomputable def gradedPieceEquivExteriorPower :
    (n : ℕ) → GradedPiece (ι Q) n ≃ₗ[R] ⋀[R]^n M
  | 0 => gradedPieceZeroEquivExteriorPower Q
  | n + 1 => filtrationGradedEquiv Q n

private theorem scalarEquivFiltrationZero_apply (r : R) :
    scalarEquivFiltrationZero Q r =
      ⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩ := by
  rfl

private theorem gradedPieceZeroEquivExteriorPower_apply_mk (r : R) :
    gradedPieceZeroEquivExteriorPower Q
      (Submodule.Quotient.mk
        (⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩ :
          filtration Q 0)) =
      (exteriorPower.zeroEquiv R M).symm r := by
  simp only [gradedPieceZeroEquivExteriorPower, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEqBot_apply_mk]
  rw [← scalarEquivFiltrationZero_apply Q r, LinearEquiv.symm_apply_apply]

private theorem gradedPieceEquivExteriorPower_apply_mk_zero (r : R) :
    gradedPieceEquivExteriorPower Q 0
      (Submodule.Quotient.mk
        (⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩ :
          filtration Q 0)) =
      (exteriorPower.zeroEquiv R M).symm r := by
  exact gradedPieceZeroEquivExteriorPower_apply_mk Q r

/-- The degree-zero piece equivalence sends a scalar class to the corresponding exterior
scalar. -/
@[simp]
theorem gradedPieceEquivExteriorPower_apply_algebraMap₀ (r : R) :
    gradedPieceEquivExteriorPower Q 0 (gradedAlgebraMap₀ (ι Q) r) =
      (exteriorPower.zeroEquiv R M).symm r := by
  rw [gradedAlgebraMap₀_apply]
  exact gradedPieceEquivExteriorPower_apply_mk_zero Q r

/-- The inverse degree-zero piece equivalence sends an exterior scalar to its scalar class. -/
@[simp]
theorem gradedPieceEquivExteriorPower_symm_apply_zeroEquiv_symm (r : R) :
    (gradedPieceEquivExteriorPower Q 0).symm
        ((exteriorPower.zeroEquiv R M).symm r) =
      gradedAlgebraMap₀ (ι Q) r := by
  apply (gradedPieceEquivExteriorPower Q 0).injective
  rw [LinearEquiv.apply_symm_apply,
    gradedPieceEquivExteriorPower_apply_algebraMap₀]

private noncomputable def filtrationLeadingTermAll (n : ℕ) :
    ⋀[R]^n M →ₗ[R] GradedPiece (ι Q) n :=
  (gradedPieceEquivExteriorPower Q n).symm.toLinearMap

private def exteriorPowerGradedMul (i j : ℕ) (x : ⋀[R]^i M) (y : ⋀[R]^j M) :
    ⋀[R]^(i + j) M :=
  @GradedMonoid.GMul.mul ℕ (fun n : ℕ => ⋀[R]^n M) _ inferInstance i j x y

private theorem filtrationLeadingTermAll_apply_ιMulti (n : ℕ) (v : Fin n → M) :
    filtrationLeadingTermAll Q n (exteriorPower.ιMulti R n v) =
      Submodule.Quotient.mk
        ⟨(List.ofFn ((ι Q) ∘ v)).prod, by
          rw [← List.map_ofFn]
          exact prod_map_ι_mem_filtration Q (l := List.ofFn v) (by simp)⟩ := by
  cases n with
  | zero =>
      apply (gradedPieceEquivExteriorPower Q 0).injective
      have hleft :
          gradedPieceEquivExteriorPower Q 0
              (filtrationLeadingTermAll Q 0 (exteriorPower.ιMulti R 0 v)) =
            exteriorPower.ιMulti R 0 v :=
        LinearEquiv.apply_symm_apply _ _
      rw [hleft]
      have hrep :
          (Submodule.Quotient.mk
            ⟨(List.ofFn ((ι Q) ∘ v)).prod, by
              rw [← List.map_ofFn]
              exact prod_map_ι_mem_filtration Q (l := List.ofFn v) (by simp)⟩ :
            GradedPiece (ι Q) 0) =
          Submodule.Quotient.mk
            (⟨algebraMap R (CliffordAlgebra Q) 1,
              algebraMap_mem_filtration Q 1 0⟩ : filtration Q 0) := by
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        simp
      rw [hrep, gradedPieceEquivExteriorPower_apply_mk_zero]
      apply (exteriorPower.zeroEquiv R M).injective
      rw [LinearEquiv.apply_symm_apply, exteriorPower.zeroEquiv_ιMulti]
  | succ n =>
      simpa only [filtrationLeadingTermAll, gradedPieceEquivExteriorPower,
        filtrationLeadingTerm_eq_filtrationGradedEquiv_symm Q n] using
        filtrationLeadingTerm_apply_ιMulti Q n v

private noncomputable def filtrationLeadingTermMul (i j : ℕ) :
    ⋀[R]^i M →ₗ[R] ⋀[R]^j M →ₗ[R] GradedPiece (ι Q) (i + j) :=
  ((gradedMul (ι Q) i j).compl₂ (filtrationLeadingTermAll Q j)).comp
    (filtrationLeadingTermAll Q i)

private noncomputable def exteriorPowerMulLeadingTerm (i j : ℕ) :
    ⋀[R]^i M →ₗ[R] ⋀[R]^j M →ₗ[R] GradedPiece (ι Q) (i + j) :=
  (DirectSum.gMulLHom R (fun n : ℕ => ⋀[R]^n M)).compr₂
    (filtrationLeadingTermAll Q (i + j))

private theorem filtrationLeadingTermAll_mul (i j : ℕ)
    (x : ⋀[R]^i M) (y : ⋀[R]^j M) :
    gradedMul (ι Q) i j (filtrationLeadingTermAll Q i x)
        (filtrationLeadingTermAll Q j y) =
      filtrationLeadingTermAll Q (i + j)
        (exteriorPowerGradedMul i j x y) := by
  have hmaps : filtrationLeadingTermMul Q i j = exteriorPowerMulLeadingTerm Q i j := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro b
    -- Extensionality leaves the two composed bilinear maps; expose their graded products.
    change gradedMul (ι Q) i j
        (filtrationLeadingTermAll Q i (exteriorPower.ιMulti R i a))
        (filtrationLeadingTermAll Q j (exteriorPower.ιMulti R j b)) =
      filtrationLeadingTermAll Q (i + j)
        (exteriorPowerGradedMul i j
          (exteriorPower.ιMulti R i a) (exteriorPower.ιMulti R j b))
    have hmul :
        exteriorPowerGradedMul i j
            (exteriorPower.ιMulti R i a) (exteriorPower.ιMulti R j b) =
          exteriorPower.ιMulti R (i + j) (Fin.append a b) := by
      apply Subtype.ext
      exact ExteriorAlgebra.ιMulti_mul_ιMulti a b
    rw [filtrationLeadingTermAll_apply_ιMulti,
      filtrationLeadingTermAll_apply_ιMulti, hmul,
      filtrationLeadingTermAll_apply_ιMulti, gradedMul_apply_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    -- Quotient and subtype extensionality leave the ambient Clifford products.
    change (List.ofFn ((ι Q) ∘ a)).prod * (List.ofFn ((ι Q) ∘ b)).prod =
      (List.ofFn ((ι Q) ∘ Fin.append a b)).prod
    rw [← List.map_ofFn, ← List.map_ofFn, ← List.map_ofFn,
      List.ofFn_fin_append, List.map_append, List.prod_append]
  exact LinearMap.congr_fun (LinearMap.congr_fun hmaps x) y

private theorem gradedPieceEquivExteriorPower_mul (i j : ℕ)
    (x : GradedPiece (ι Q) i) (y : GradedPiece (ι Q) j) :
    gradedPieceEquivExteriorPower Q (i + j) (gradedMul (ι Q) i j x y) =
      exteriorPowerGradedMul i j
        (gradedPieceEquivExteriorPower Q i x)
        (gradedPieceEquivExteriorPower Q j y) := by
  apply (gradedPieceEquivExteriorPower Q (i + j)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  have h := filtrationLeadingTermAll_mul Q i j
      (gradedPieceEquivExteriorPower Q i x)
      (gradedPieceEquivExteriorPower Q j y)
  have hx : filtrationLeadingTermAll Q i
      (gradedPieceEquivExteriorPower Q i x) = x :=
    LinearEquiv.symm_apply_apply _ x
  have hy : filtrationLeadingTermAll Q j
      (gradedPieceEquivExteriorPower Q j y) = y :=
    LinearEquiv.symm_apply_apply _ y
  rw [hx, hy] at h
  exact h

private noncomputable def gradedPieceToExteriorDirectSum (n : ℕ) :
    GradedPiece (ι Q) n →ₗ[R] ⨁ n : ℕ, ⋀[R]^n M :=
  DirectSum.lof R ℕ (fun n : ℕ => ⋀[R]^n M) n ∘ₗ
    (gradedPieceEquivExteriorPower Q n).toLinearMap

private theorem gradedPieceToExteriorDirectSum_one :
    gradedPieceToExteriorDirectSum Q 0
      (GradedMonoid.GOne.one : GradedPiece (ι Q) 0) = 1 := by
  rw [gradedGOne_one]
  have honePiece :
      gradedPieceEquivExteriorPower Q 0 (gradedOne (ι Q)) =
        (exteriorPower.zeroEquiv R M).symm 1 := by
    rw [gradedOne_def]
    exact gradedPieceEquivExteriorPower_apply_mk_zero Q 1
  rw [DirectSum.one_def]
  -- Unfold the piece map to compare the two degree-zero summands.
  change DirectSum.of (fun n : ℕ => ⋀[R]^n M) 0
      (gradedPieceEquivExteriorPower Q 0 (gradedOne (ι Q))) =
    DirectSum.of (fun n : ℕ => ⋀[R]^n M) 0 _
  rw [honePiece]
  apply congrArg (DirectSum.of (fun n : ℕ => ⋀[R]^n M) 0)
  apply Subtype.ext
  rw [exteriorPower.zeroEquiv_symm_apply]
  simp

private theorem gradedPieceToExteriorDirectSum_mul {i j : ℕ}
    (x : GradedPiece (ι Q) i) (y : GradedPiece (ι Q) j) :
    gradedPieceToExteriorDirectSum Q (i + j) (GradedMonoid.GMul.mul x y) =
      gradedPieceToExteriorDirectSum Q i x *
      gradedPieceToExteriorDirectSum Q j y := by
  rw [gradedGMul_mul]
  -- Unfold the piece maps to compare their homogeneous direct-sum generators.
  change DirectSum.of (fun n : ℕ => ⋀[R]^n M) (i + j)
      (gradedPieceEquivExteriorPower Q (i + j) (gradedMul (ι Q) i j x y)) =
    DirectSum.of (fun n : ℕ => ⋀[R]^n M) i
        (gradedPieceEquivExteriorPower Q i x) *
      DirectSum.of (fun n : ℕ => ⋀[R]^n M) j
        (gradedPieceEquivExteriorPower Q j y)
  rw [DirectSum.of_mul_of, gradedPieceEquivExteriorPower_mul]
  rfl

private noncomputable def associatedGradedToExteriorDirectSum :
    AssociatedGraded (ι Q) →ₐ[R] ⨁ n : ℕ, ⋀[R]^n M :=
  DirectSum.toAlgebra R (GradedPiece (ι Q))
    (gradedPieceToExteriorDirectSum Q)
    (gradedPieceToExteriorDirectSum_one Q)
    (gradedPieceToExteriorDirectSum_mul Q)

private theorem associatedGradedToExteriorDirectSum_bijective :
    Function.Bijective (associatedGradedToExteriorDirectSum Q) := by
  let e := DirectSum.congrLinearEquiv (gradedPieceEquivExteriorPower Q)
  have he :
      (associatedGradedToExteriorDirectSum Q).toLinearMap = e.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    -- `toAlgebra` is implemented by `toAddMonoid`; compare that map on each generator.
    change DirectSum.toAddMonoid
        (fun n => (gradedPieceToExteriorDirectSum Q n).toAddMonoidHom)
          (DirectSum.of (GradedPiece (ι Q)) n x) = e (DirectSum.of _ n x)
    rw [DirectSum.toAddMonoid_of]
    -- Expand the piece map before using the congruence equivalence's generator equation.
    change DirectSum.of (fun n : ℕ => ⋀[R]^n M) n
        (gradedPieceEquivExteriorPower Q n x) = e.toLinearMap (DirectSum.of _ n x)
    rw [DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_of]
    rfl
  have he_apply (x : AssociatedGraded (ι Q)) :
      associatedGradedToExteriorDirectSum Q x = e x :=
    LinearMap.congr_fun he x
  constructor
  · intro x y hxy
    apply e.injective
    rw [← he_apply x, ← he_apply y]
    exact hxy
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, he_apply x⟩

/-- The associated graded of the Clifford filtration is the exterior algebra. -/
noncomputable def associatedGradedEquivExterior :
    AssociatedGraded (ι Q) ≃ₐ[R] ExteriorAlgebra R M :=
  (AlgEquiv.ofBijective (associatedGradedToExteriorDirectSum Q)
    (associatedGradedToExteriorDirectSum_bijective Q)).trans
      (DirectSum.decomposeAlgEquiv (fun n : ℕ => ⋀[R]^n M)).symm

/-- The associated-graded equivalence on an arbitrary homogeneous piece. -/
@[simp]
theorem associatedGradedEquivExterior_apply_of (n : ℕ)
    (x : GradedPiece (ι Q) n) :
    associatedGradedEquivExterior Q
        (DirectSum.of (GradedPiece (ι Q)) n x) =
      (gradedPieceEquivExteriorPower Q n x : ExteriorAlgebra R M) := by
  -- Expose the two reused maps in the opaque composite on a homogeneous generator.
  change (DirectSum.decomposeAlgEquiv (fun n : ℕ => ⋀[R]^n M)).symm
      (DirectSum.toAddMonoid
        (fun n => (gradedPieceToExteriorDirectSum Q n).toAddMonoidHom)
          (DirectSum.of (GradedPiece (ι Q)) n x)) = _
  rw [DirectSum.toAddMonoid_of]
  -- The algebra equivalence reuses the decomposition linear equivalence at this boundary.
  change (DirectSum.decompose (fun n : ℕ => ⋀[R]^n M)).symm
      (DirectSum.of (fun n : ℕ => ⋀[R]^n M) n
        (gradedPieceEquivExteriorPower Q n x)) = _
  rw [DirectSum.decompose_symm_of]

/-- The inverse associated-graded equivalence on an arbitrary exterior power. -/
@[simp]
theorem associatedGradedEquivExterior_symm_apply_coe (n : ℕ)
    (x : ⋀[R]^n M) :
    (associatedGradedEquivExterior Q).symm (x : ExteriorAlgebra R M) =
      DirectSum.of (GradedPiece (ι Q)) n
        ((gradedPieceEquivExteriorPower Q n).symm x) := by
  apply (associatedGradedEquivExterior Q).injective
  rw [AlgEquiv.apply_symm_apply,
    associatedGradedEquivExterior_apply_of,
    LinearEquiv.apply_symm_apply]

/-- On a positive-degree homogeneous piece, the total equivalence is `filtrationGradedEquiv`. -/
@[simp 1100]
theorem associatedGradedEquivExterior_apply_of_succ (n : ℕ)
    (x : GradedPiece (ι Q) (n + 1)) :
    associatedGradedEquivExterior Q
        (DirectSum.of (GradedPiece (ι Q)) (n + 1) x) =
      (filtrationGradedEquiv Q n x : ExteriorAlgebra R M) := by
  exact associatedGradedEquivExterior_apply_of Q (n + 1) x

/-- The inverse on a positive-degree exterior power is the inverse graded equivalence. -/
@[simp 1100]
theorem associatedGradedEquivExterior_symm_apply_coe_succ (n : ℕ)
    (x : ⋀[R]^(n + 1) M) :
    (associatedGradedEquivExterior Q).symm (x : ExteriorAlgebra R M) =
      DirectSum.of (GradedPiece (ι Q)) (n + 1)
        ((filtrationGradedEquiv Q n).symm x) := by
  exact associatedGradedEquivExterior_symm_apply_coe Q (n + 1) x

end CliffordAlgebra
