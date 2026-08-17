/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import TauCeti.LinearAlgebra.CliffordAlgebra.AssociatedGraded
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

* `CliffordAlgebra.filtrationAssociatedGradedEquivExterior`: the algebra equivalence from
  the associated graded of the Clifford filtration to the exterior algebra.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Proposition I.1.2.
-/

public section

open CliffordAlgebra
open scoped DirectSum

universe u v

namespace CliffordAlgebra

open TauCeti

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

private noncomputable def scalarEquivFiltrationZero :
    R ≃ₗ[R] filtration Q 0 :=
  (LinearEquiv.ofInjective (Algebra.linearMap R (CliffordAlgebra Q))
    (algebraMap_injective Q)).trans
    (LinearEquiv.ofEq _ _ (Submodule.one_eq_range.symm.trans (filtration_zero Q).symm))

private noncomputable def filtrationGradedPieceZeroEquivExteriorPower :
    FiltrationGradedPiece Q 0 ≃ₗ[R] ⋀[R]^0 M :=
  (Submodule.quotEquivOfEqBot _ (filtrationPreviousRestricted_zero Q)).trans
    ((scalarEquivFiltrationZero Q).symm.trans (exteriorPower.zeroEquiv R M).symm)

/-- The canonical equivalence from each graded filtration piece to the corresponding exterior
power. -/
noncomputable def filtrationGradedPieceEquivExteriorPower :
    (n : ℕ) → FiltrationGradedPiece Q n ≃ₗ[R] ⋀[R]^n M
  | 0 => filtrationGradedPieceZeroEquivExteriorPower Q
  | n + 1 => filtrationGradedEquiv Q n

private theorem scalarEquivFiltrationZero_apply (r : R) :
    scalarEquivFiltrationZero Q r =
      ⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩ := by
  rfl

private theorem filtrationGradedPieceZeroEquivExteriorPower_apply_mk (r : R) :
    filtrationGradedPieceZeroEquivExteriorPower Q
      (Submodule.Quotient.mk
        (⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩ :
          filtration Q 0)) =
      (exteriorPower.zeroEquiv R M).symm r := by
  simp only [filtrationGradedPieceZeroEquivExteriorPower, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEqBot_apply_mk]
  rw [← scalarEquivFiltrationZero_apply Q r, LinearEquiv.symm_apply_apply]

private theorem filtrationGradedPieceEquivExteriorPower_apply_mk_zero (r : R) :
    filtrationGradedPieceEquivExteriorPower Q 0
      (Submodule.Quotient.mk
        (⟨algebraMap R (CliffordAlgebra Q) r, algebraMap_mem_filtration Q r 0⟩ :
          filtration Q 0)) =
      (exteriorPower.zeroEquiv R M).symm r := by
  exact filtrationGradedPieceZeroEquivExteriorPower_apply_mk Q r

/-- The degree-zero piece equivalence sends a scalar class to the corresponding exterior
scalar. -/
@[simp]
theorem filtrationGradedPieceEquivExteriorPower_apply_algebraMap₀ (r : R) :
    filtrationGradedPieceEquivExteriorPower Q 0 (filtrationGradedAlgebraMap₀ Q r) =
      (exteriorPower.zeroEquiv R M).symm r := by
  rw [filtrationGradedAlgebraMap₀_apply]
  exact filtrationGradedPieceEquivExteriorPower_apply_mk_zero Q r

/-- The inverse degree-zero piece equivalence sends an exterior scalar to its scalar class. -/
@[simp]
theorem filtrationGradedPieceEquivExteriorPower_symm_apply_zeroEquiv_symm (r : R) :
    (filtrationGradedPieceEquivExteriorPower Q 0).symm
        ((exteriorPower.zeroEquiv R M).symm r) =
      filtrationGradedAlgebraMap₀ Q r := by
  apply (filtrationGradedPieceEquivExteriorPower Q 0).injective
  rw [LinearEquiv.apply_symm_apply,
    filtrationGradedPieceEquivExteriorPower_apply_algebraMap₀]

private noncomputable def filtrationLeadingTermAll (n : ℕ) :
    ⋀[R]^n M →ₗ[R] FiltrationGradedPiece Q n :=
  (filtrationGradedPieceEquivExteriorPower Q n).symm.toLinearMap

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
      apply (filtrationGradedPieceEquivExteriorPower Q 0).injective
      have hleft :
          filtrationGradedPieceEquivExteriorPower Q 0
              (filtrationLeadingTermAll Q 0 (exteriorPower.ιMulti R 0 v)) =
            exteriorPower.ιMulti R 0 v :=
        LinearEquiv.apply_symm_apply _ _
      rw [hleft]
      have hrep :
          (Submodule.Quotient.mk
            ⟨(List.ofFn ((ι Q) ∘ v)).prod, by
              rw [← List.map_ofFn]
              exact prod_map_ι_mem_filtration Q (l := List.ofFn v) (by simp)⟩ :
            FiltrationGradedPiece Q 0) =
          Submodule.Quotient.mk
            (⟨algebraMap R (CliffordAlgebra Q) 1,
              algebraMap_mem_filtration Q 1 0⟩ : filtration Q 0) := by
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        simp
      rw [hrep, filtrationGradedPieceEquivExteriorPower_apply_mk_zero]
      apply (exteriorPower.zeroEquiv R M).injective
      rw [LinearEquiv.apply_symm_apply, exteriorPower.zeroEquiv_ιMulti]
  | succ n =>
      simpa only [filtrationLeadingTermAll, filtrationGradedPieceEquivExteriorPower,
        filtrationLeadingTerm_eq_filtrationGradedEquiv_symm Q n] using
        filtrationLeadingTerm_apply_ιMulti Q n v

private noncomputable def filtrationLeadingTermMul (i j : ℕ) :
    ⋀[R]^i M →ₗ[R] ⋀[R]^j M →ₗ[R] FiltrationGradedPiece Q (i + j) :=
  ((filtrationGradedMul Q i j).compl₂ (filtrationLeadingTermAll Q j)).comp
    (filtrationLeadingTermAll Q i)

private noncomputable def exteriorPowerMulLeadingTerm (i j : ℕ) :
    ⋀[R]^i M →ₗ[R] ⋀[R]^j M →ₗ[R] FiltrationGradedPiece Q (i + j) :=
  (DirectSum.gMulLHom R (fun n : ℕ => ⋀[R]^n M)).compr₂
    (filtrationLeadingTermAll Q (i + j))

private theorem filtrationLeadingTermAll_mul (i j : ℕ)
    (x : ⋀[R]^i M) (y : ⋀[R]^j M) :
    filtrationGradedMul Q i j (filtrationLeadingTermAll Q i x)
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
    change filtrationGradedMul Q i j
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
      filtrationLeadingTermAll_apply_ιMulti, filtrationGradedMul_apply_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    -- Quotient and subtype extensionality leave the ambient Clifford products.
    change (List.ofFn ((ι Q) ∘ a)).prod * (List.ofFn ((ι Q) ∘ b)).prod =
      (List.ofFn ((ι Q) ∘ Fin.append a b)).prod
    rw [← List.map_ofFn, ← List.map_ofFn, ← List.map_ofFn,
      List.ofFn_fin_append, List.map_append, List.prod_append]
  exact LinearMap.congr_fun (LinearMap.congr_fun hmaps x) y

private theorem filtrationGradedPieceEquivExteriorPower_mul (i j : ℕ)
    (x : FiltrationGradedPiece Q i) (y : FiltrationGradedPiece Q j) :
    filtrationGradedPieceEquivExteriorPower Q (i + j) (filtrationGradedMul Q i j x y) =
      exteriorPowerGradedMul i j
        (filtrationGradedPieceEquivExteriorPower Q i x)
        (filtrationGradedPieceEquivExteriorPower Q j y) := by
  apply (filtrationGradedPieceEquivExteriorPower Q (i + j)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  have h := filtrationLeadingTermAll_mul Q i j
      (filtrationGradedPieceEquivExteriorPower Q i x)
      (filtrationGradedPieceEquivExteriorPower Q j y)
  have hx : filtrationLeadingTermAll Q i
      (filtrationGradedPieceEquivExteriorPower Q i x) = x :=
    LinearEquiv.symm_apply_apply _ x
  have hy : filtrationLeadingTermAll Q j
      (filtrationGradedPieceEquivExteriorPower Q j y) = y :=
    LinearEquiv.symm_apply_apply _ y
  rw [hx, hy] at h
  exact h

private noncomputable def filtrationGradedPieceToExteriorDirectSum (n : ℕ) :
    FiltrationGradedPiece Q n →ₗ[R] ⨁ n : ℕ, ⋀[R]^n M :=
  DirectSum.lof R ℕ (fun n : ℕ => ⋀[R]^n M) n ∘ₗ
    (filtrationGradedPieceEquivExteriorPower Q n).toLinearMap

private theorem filtrationGradedPieceToExteriorDirectSum_one :
    filtrationGradedPieceToExteriorDirectSum Q 0
      (GradedMonoid.GOne.one : FiltrationGradedPiece Q 0) = 1 := by
  -- `DirectSum.toAlgebra` states its unit through `GOne`; expose the named graded unit.
  change filtrationGradedPieceToExteriorDirectSum Q 0 (filtrationGradedOne Q) = 1
  have honePiece :
      filtrationGradedPieceEquivExteriorPower Q 0 (filtrationGradedOne Q) =
        (exteriorPower.zeroEquiv R M).symm 1 := by
    rw [filtrationGradedOne_def]
    exact filtrationGradedPieceEquivExteriorPower_apply_mk_zero Q 1
  rw [DirectSum.one_def]
  -- Unfold the piece map to compare the two degree-zero summands.
  change DirectSum.of (fun n : ℕ => ⋀[R]^n M) 0
      (filtrationGradedPieceEquivExteriorPower Q 0 (filtrationGradedOne Q)) =
    DirectSum.of (fun n : ℕ => ⋀[R]^n M) 0 _
  rw [honePiece]
  apply congrArg (DirectSum.of (fun n : ℕ => ⋀[R]^n M) 0)
  apply Subtype.ext
  rw [exteriorPower.zeroEquiv_symm_apply]
  simp

private theorem filtrationGradedPieceToExteriorDirectSum_mul {i j : ℕ}
    (x : FiltrationGradedPiece Q i) (y : FiltrationGradedPiece Q j) :
    filtrationGradedPieceToExteriorDirectSum Q (i + j) (GradedMonoid.GMul.mul x y) =
      filtrationGradedPieceToExteriorDirectSum Q i x *
        filtrationGradedPieceToExteriorDirectSum Q j y := by
  -- `DirectSum.toAlgebra` states multiplication through `GMul`; expose its named product and maps.
  change filtrationGradedPieceToExteriorDirectSum Q (i + j) (filtrationGradedMul Q i j x y) = _
  change DirectSum.of (fun n : ℕ => ⋀[R]^n M) (i + j)
      (filtrationGradedPieceEquivExteriorPower Q (i + j) (filtrationGradedMul Q i j x y)) =
    DirectSum.of (fun n : ℕ => ⋀[R]^n M) i
        (filtrationGradedPieceEquivExteriorPower Q i x) *
      DirectSum.of (fun n : ℕ => ⋀[R]^n M) j
        (filtrationGradedPieceEquivExteriorPower Q j y)
  rw [DirectSum.of_mul_of, filtrationGradedPieceEquivExteriorPower_mul]
  rfl

private noncomputable def filtrationAssociatedGradedToExteriorDirectSum :
    filtrationAssociatedGraded Q →ₐ[R] ⨁ n : ℕ, ⋀[R]^n M :=
  DirectSum.toAlgebra R (FiltrationGradedPiece Q)
    (filtrationGradedPieceToExteriorDirectSum Q)
    (filtrationGradedPieceToExteriorDirectSum_one Q)
    (filtrationGradedPieceToExteriorDirectSum_mul Q)

private theorem filtrationAssociatedGradedToExteriorDirectSum_bijective :
    Function.Bijective (filtrationAssociatedGradedToExteriorDirectSum Q) := by
  let e := DirectSum.congrLinearEquiv (filtrationGradedPieceEquivExteriorPower Q)
  have he :
      (filtrationAssociatedGradedToExteriorDirectSum Q).toLinearMap = e.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    -- `toAlgebra` is implemented by `toAddMonoid`; compare that map on each generator.
    change DirectSum.toAddMonoid
        (fun n => (filtrationGradedPieceToExteriorDirectSum Q n).toAddMonoidHom)
          (DirectSum.of (FiltrationGradedPiece Q) n x) = e (DirectSum.of _ n x)
    rw [DirectSum.toAddMonoid_of]
    -- Expand the piece map before using the congruence equivalence's generator equation.
    change DirectSum.of (fun n : ℕ => ⋀[R]^n M) n
        (filtrationGradedPieceEquivExteriorPower Q n x) = e.toLinearMap (DirectSum.of _ n x)
    rw [DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_of]
    rfl
  have he_apply (x : filtrationAssociatedGraded Q) :
      filtrationAssociatedGradedToExteriorDirectSum Q x = e x :=
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
noncomputable def filtrationAssociatedGradedEquivExterior :
    filtrationAssociatedGraded Q ≃ₐ[R] ExteriorAlgebra R M :=
  (AlgEquiv.ofBijective (filtrationAssociatedGradedToExteriorDirectSum Q)
    (filtrationAssociatedGradedToExteriorDirectSum_bijective Q)).trans
      (DirectSum.decomposeAlgEquiv (fun n : ℕ => ⋀[R]^n M)).symm

/-- The associated-graded equivalence on an arbitrary homogeneous piece. -/
@[simp]
theorem filtrationAssociatedGradedEquivExterior_apply_of (n : ℕ)
    (x : FiltrationGradedPiece Q n) :
    filtrationAssociatedGradedEquivExterior Q
        (DirectSum.of (FiltrationGradedPiece Q) n x) =
      (filtrationGradedPieceEquivExteriorPower Q n x : ExteriorAlgebra R M) := by
  -- Expose the two reused maps in the opaque composite on a homogeneous generator.
  change (DirectSum.decomposeAlgEquiv (fun n : ℕ => ⋀[R]^n M)).symm
      (DirectSum.toAddMonoid
        (fun n => (filtrationGradedPieceToExteriorDirectSum Q n).toAddMonoidHom)
          (DirectSum.of (FiltrationGradedPiece Q) n x)) = _
  rw [DirectSum.toAddMonoid_of]
  -- The algebra equivalence reuses the decomposition linear equivalence at this boundary.
  change (DirectSum.decompose (fun n : ℕ => ⋀[R]^n M)).symm
      (DirectSum.of (fun n : ℕ => ⋀[R]^n M) n
        (filtrationGradedPieceEquivExteriorPower Q n x)) = _
  rw [DirectSum.decompose_symm_of]

/-- The inverse associated-graded equivalence on an arbitrary exterior power. -/
@[simp]
theorem filtrationAssociatedGradedEquivExterior_symm_apply_coe (n : ℕ)
    (x : ⋀[R]^n M) :
    (filtrationAssociatedGradedEquivExterior Q).symm (x : ExteriorAlgebra R M) =
      DirectSum.of (FiltrationGradedPiece Q) n
        ((filtrationGradedPieceEquivExteriorPower Q n).symm x) := by
  apply (filtrationAssociatedGradedEquivExterior Q).injective
  rw [AlgEquiv.apply_symm_apply,
    filtrationAssociatedGradedEquivExterior_apply_of,
    LinearEquiv.apply_symm_apply]

/-- On a positive-degree homogeneous piece, the total equivalence is `filtrationGradedEquiv`. -/
@[simp 1100]
theorem filtrationAssociatedGradedEquivExterior_apply_of_succ (n : ℕ)
    (x : FiltrationGradedPiece Q (n + 1)) :
    filtrationAssociatedGradedEquivExterior Q
        (DirectSum.of (FiltrationGradedPiece Q) (n + 1) x) =
      (filtrationGradedEquiv Q n x : ExteriorAlgebra R M) := by
  exact filtrationAssociatedGradedEquivExterior_apply_of Q (n + 1) x

/-- The inverse on a positive-degree exterior power is the inverse graded equivalence. -/
@[simp 1100]
theorem filtrationAssociatedGradedEquivExterior_symm_apply_coe_succ (n : ℕ)
    (x : ⋀[R]^(n + 1) M) :
    (filtrationAssociatedGradedEquivExterior Q).symm (x : ExteriorAlgebra R M) =
      DirectSum.of (FiltrationGradedPiece Q) (n + 1)
        ((filtrationGradedEquiv Q n).symm x) := by
  exact filtrationAssociatedGradedEquivExterior_symm_apply_coe Q (n + 1) x

end CliffordAlgebra
