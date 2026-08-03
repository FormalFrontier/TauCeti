/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# Clifford bivectors and exterior squares

This module packages the generic half-normalized Clifford commutator into an alternating map and
the induced linear map from the second exterior power. Its action on a Clifford generator is given
by the polarization of the quadratic form.

The formula is valid over every commutative ring in which `2` is invertible. The factor `⅟2` is
forced: the commutator of the unnormalized expression acts by twice the desired infinitesimal
rotation.

This is a shared generic prerequisite for the roadmap's Layer 3 standard-form normalization and
the later Layer 9 arbitrary-form realization. It constructs neither `soEquivBivector` nor
`soEquivQuadratic`, and it does not construct a transported Lie bracket, a Spin action, or the
Layer 9 CAR worked instance.

## Main definitions

* `TauCeti.CliffordAlgebra.cliffordBivector`: the half-normalized commutator of two Clifford
  generators.
* `TauCeti.CliffordAlgebra.cliffordBivectorAlternating`: the corresponding alternating map.
* `TauCeti.CliffordAlgebra.cliffordBivectorExterior`: the induced linear map from the second
  exterior power.

## Main results

* `TauCeti.CliffordAlgebra.cliffordBivector_lie_ι`: its commutator action on a generator is the
  infinitesimal rotation determined by `QuadraticMap.polar`.
* `TauCeti.CliffordAlgebra.cliffordBivectorExterior_apply_ιMulti`: the exterior-square map on a
  decomposable bivector.
* `TauCeti.CliffordAlgebra.cliffordBivector_mem_evenOdd_zero` and
  `TauCeti.CliffordAlgebra.cliffordBivector_mem_filtration_two`: it is even and has filtration
  degree at most two.
* `TauCeti.CliffordAlgebra.cliffordBivector_lie_cliffordBivector`: the ambient commutator of
  decomposable bivectors.
* `TauCeti.CliffordAlgebra.cliffordBivectorLieSubalgebra`: their image as a Lie subalgebra of the
  Clifford algebra with its ambient commutator.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 3, "the Lie algebra `𝔰𝔬(V) ≅ ⋀²V` inside the Clifford algebra".
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The half-normalized Clifford commutator of two generators. Its action on a third generator is
the infinitesimal rotation in `cliffordBivector_lie_ι`; that action, rather than this expression,
fixes the normalization. -/
noncomputable def cliffordBivector (a b : M) : CliffordAlgebra Q :=
  (⅟ (2 : R)) • (ι Q a * ι Q b - ι Q b * ι Q a)

/-- The defining half-normalized commutator formula for a Clifford bivector. -/
theorem cliffordBivector_def (a b : M) :
    cliffordBivector Q a b = (⅟ (2 : R)) • (ι Q a * ι Q b - ι Q b * ι Q a) := by
  rw [cliffordBivector]

/-- The alternating map whose value on two vectors is their half-normalized Clifford bivector. -/
noncomputable def cliffordBivectorAlternating : M [⋀^Fin 2]→ₗ[R] CliffordAlgebra Q :=
  { toFun := fun v => cliffordBivector Q (v 0) (v 1)
    map_update_add' := by
      intro _ v i x y
      fin_cases i <;>
        simp [cliffordBivector_def, add_mul, mul_add, smul_sub] <;>
        module
    map_update_smul' := by
      intro _ v i c x
      fin_cases i <;>
        simp [cliffordBivector_def, smul_sub, smul_smul, mul_comm]
    map_eq_zero_of_eq' := by
      intro v i j h hij
      fin_cases i <;> fin_cases j <;> simp_all [cliffordBivector_def] }

private theorem cliffordBivectorAlternating_apply_internal (a b : M) :
    cliffordBivectorAlternating Q ![a, b] = cliffordBivector Q a b := rfl

/-- The alternating map agrees with the half-normalized Clifford bivector on a pair of vectors. -/
@[simp]
theorem cliffordBivectorAlternating_apply (a b : M) :
    cliffordBivectorAlternating Q ![a, b] = cliffordBivector Q a b :=
  cliffordBivectorAlternating_apply_internal Q a b

/-- The linear map from the second exterior power induced by the Clifford bivector. -/
noncomputable def cliffordBivectorExterior : ⋀[R]^2 M →ₗ[R] CliffordAlgebra Q :=
  exteriorPower.alternatingMapLinearEquiv (cliffordBivectorAlternating Q)

/-- The exterior-square Clifford bivector map on a decomposable bivector. -/
@[simp]
theorem cliffordBivectorExterior_apply_ιMulti (a b : M) :
    cliffordBivectorExterior Q (exteriorPower.ιMulti R 2 ![a, b]) = cliffordBivector Q a b := by
  simp [cliffordBivectorExterior]

/-- Interchanging the two vectors negates their Clifford bivector. -/
theorem cliffordBivector_swap (a b : M) :
    cliffordBivector Q b a = -cliffordBivector Q a b := by
  rw [← cliffordBivectorAlternating_apply, ← cliffordBivectorAlternating_apply]
  convert (cliffordBivectorAlternating Q).map_swap (v := ![a, b])
    (by decide : (0 : Fin 2) ≠ 1) using 1
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The Clifford bivector of a repeated vector is zero. -/
@[simp]
theorem cliffordBivector_self (a : M) : cliffordBivector Q a a = 0 := by
  simpa only [cliffordBivectorAlternating_apply] using
    (cliffordBivectorAlternating Q).map_eq_zero_of_eq ![a, a] (by simp)
      (by decide : (0 : Fin 2) ≠ 1)

/-- Clifford bivectors are even. -/
theorem cliffordBivector_mem_evenOdd_zero (a b : M) :
    cliffordBivector Q a b ∈ evenOdd Q 0 := by
  rw [cliffordBivector_def]
  exact Submodule.smul_mem _ _ <|
    Submodule.sub_mem _ (ι_mul_ι_mem_evenOdd_zero Q a b) (ι_mul_ι_mem_evenOdd_zero Q b a)

/-- Clifford bivectors have filtration degree at most two. -/
theorem cliffordBivector_mem_filtration_two (a b : M) :
    cliffordBivector Q a b ∈ filtration Q 2 := by
  rw [cliffordBivector_def]
  exact Submodule.smul_mem _ _ <|
    Submodule.sub_mem _ (ι_mul_ι_mem_filtration_two Q a b) (ι_mul_ι_mem_filtration_two Q b a)

private theorem cliffordBivectorExterior_range_le (P : Submodule R (CliffordAlgebra Q))
    (hP : ∀ a b : M, cliffordBivector Q a b ∈ P) :
    LinearMap.range (cliffordBivectorExterior Q) ≤ P := by
  rw [LinearMap.range_eq_map, Submodule.map_le_iff_le_comap,
    ← exteriorPower.ιMulti_span R 2 M]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  -- Rewriting does not unfold membership in the comap, so expose the map application explicitly.
  change cliffordBivectorExterior Q (exteriorPower.ιMulti R 2 ![v 0, v 1]) ∈ P
  rw [cliffordBivectorExterior_apply_ιMulti]
  exact hP _ _

/-- The exterior-square Clifford bivector map takes values in the even component. -/
theorem cliffordBivectorExterior_range_le_evenOdd_zero :
    LinearMap.range (cliffordBivectorExterior Q) ≤ evenOdd Q 0 :=
  cliffordBivectorExterior_range_le Q _ (cliffordBivector_mem_evenOdd_zero Q)

/-- The exterior-square Clifford bivector map takes values in filtration degree at most two. -/
theorem cliffordBivectorExterior_range_le_filtration_two :
    LinearMap.range (cliffordBivectorExterior Q) ≤ filtration Q 2 :=
  cliffordBivectorExterior_range_le Q _ (cliffordBivector_mem_filtration_two Q)

/-- The action-normalization identity for the half-normalized Clifford bivector. -/
theorem cliffordBivector_lie_ι (a b x : M) :
    ⁅cliffordBivector Q a b, ι Q x⁆ =
      ι Q (QuadraticMap.polar Q b x • a - QuadraticMap.polar Q a x • b) := by
  rw [cliffordBivector_def, Ring.lie_def]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [map_sub, map_smul, map_smul]
  have hbx := ι_mul_ι_add_swap (Q := Q) b x
  have hax := ι_mul_ι_add_swap (Q := Q) a x
  have hA (r : R) : ι Q a * algebraMap R (CliffordAlgebra Q) r = r • ι Q a := by
    calc
      ι Q a * algebraMap R (CliffordAlgebra Q) r = algebraMap R (CliffordAlgebra Q) r * ι Q a :=
        (Algebra.commutes r (ι Q a)).symm
      _ = r • ι Q a := (Algebra.smul_def r (ι Q a)).symm
  have hB (r : R) : ι Q b * algebraMap R (CliffordAlgebra Q) r = r • ι Q b := by
    calc
      ι Q b * algebraMap R (CliffordAlgebra Q) r = algebraMap R (CliffordAlgebra Q) r * ι Q b :=
        (Algebra.commutes r (ι Q b)).symm
      _ = r • ι Q b := (Algebra.smul_def r (ι Q b)).symm
  have h :
      (ι Q a * ι Q b - ι Q b * ι Q a) * ι Q x -
          ι Q x * (ι Q a * ι Q b - ι Q b * ι Q a) =
        (2 : R) • (QuadraticMap.polar Q b x • ι Q a -
          QuadraticMap.polar Q a x • ι Q b) := by
    calc
      (ι Q a * ι Q b - ι Q b * ι Q a) * ι Q x -
          ι Q x * (ι Q a * ι Q b - ι Q b * ι Q a) =
        ι Q a * (ι Q b * ι Q x + ι Q x * ι Q b) -
          ι Q b * (ι Q a * ι Q x + ι Q x * ι Q a) -
          (ι Q a * ι Q x + ι Q x * ι Q a) * ι Q b +
          (ι Q b * ι Q x + ι Q x * ι Q b) * ι Q a := by
            noncomm_ring
      _ = ι Q a * algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q b x) -
          ι Q b * algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a x) -
          algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a x) * ι Q b +
          algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q b x) * ι Q a := by
            rw [hbx, hax]
      _ = (2 : R) • (QuadraticMap.polar Q b x • ι Q a -
          QuadraticMap.polar Q a x • ι Q b) := by
            rw [hA, hB, ← Algebra.smul_def, ← Algebra.smul_def]
            rw [two_smul R]
            abel
  rw [h]
  exact invOf_smul_smul (2 : R) _

/-- The ambient commutator of two decomposable Clifford bivectors. The half-normalization in
`cliffordBivector` makes this the usual bivector commutator formula without an additional scalar
factor. -/
theorem cliffordBivector_lie_cliffordBivector (a b c d : M) :
    ⁅cliffordBivector Q a b, cliffordBivector Q c d⁆ =
      QuadraticMap.polar Q b c • cliffordBivector Q a d -
        QuadraticMap.polar Q a c • cliffordBivector Q b d +
      QuadraticMap.polar Q b d • cliffordBivector Q c a -
        QuadraticMap.polar Q a d • cliffordBivector Q c b := by
  have h_lie_mul (x y z : CliffordAlgebra Q) :
      ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
    rw [Ring.lie_def, Ring.lie_def, Ring.lie_def]
    noncomm_ring
  rw [cliffordBivector_def Q c d, lie_smul, lie_sub]
  rw [h_lie_mul, h_lie_mul]
  rw [cliffordBivector_lie_ι, cliffordBivector_lie_ι]
  simp only [map_sub, map_smul]
  rw [cliffordBivector_def, cliffordBivector_def, cliffordBivector_def,
    cliffordBivector_def]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul]
  module

/-- The range of the exterior-square Clifford bivector map is closed under the ambient Clifford
commutator. -/
theorem lie_mem_cliffordBivectorExterior_range {x y : CliffordAlgebra Q}
    (hx : x ∈ LinearMap.range (cliffordBivectorExterior Q))
    (hy : y ∈ LinearMap.range (cliffordBivectorExterior Q)) :
    ⁅x, y⁆ ∈ LinearMap.range (cliffordBivectorExterior Q) := by
  have h_bivector_mem (a b : M) :
      cliffordBivector Q a b ∈ LinearMap.range (cliffordBivectorExterior Q) := by
    rw [← cliffordBivectorExterior_apply_ιMulti]
    exact LinearMap.mem_range_self _ _
  have h_decomp (a b : M) :
      ∀ y ∈ LinearMap.range (cliffordBivectorExterior Q),
        ⁅cliffordBivector Q a b, y⁆ ∈ LinearMap.range (cliffordBivectorExterior Q) := by
    intro y hy
    let P := (LinearMap.range (cliffordBivectorExterior Q)).comap
      (LieModule.toEnd R (CliffordAlgebra Q) (CliffordAlgebra Q) (cliffordBivector Q a b))
    have hP : LinearMap.range (cliffordBivectorExterior Q) ≤ P :=
      cliffordBivectorExterior_range_le Q P (fun c d => by
        rw [Submodule.mem_comap, LieModule.toEnd_apply_apply,
          cliffordBivector_lie_cliffordBivector]
        apply Submodule.sub_mem
        · apply Submodule.add_mem
          · exact Submodule.sub_mem _
              (Submodule.smul_mem _ _ (h_bivector_mem _ _))
              (Submodule.smul_mem _ _ (h_bivector_mem _ _))
          · exact Submodule.smul_mem _ _ (h_bivector_mem _ _)
        · exact Submodule.smul_mem _ _ (h_bivector_mem _ _))
    exact hP hy
  let P := (LinearMap.range (cliffordBivectorExterior Q)).comap
    ((LieModule.toEnd R (CliffordAlgebra Q) (CliffordAlgebra Q)).flip y)
  have hP : LinearMap.range (cliffordBivectorExterior Q) ≤ P :=
    cliffordBivectorExterior_range_le Q P (fun a b => by
      rw [Submodule.mem_comap]
      exact h_decomp a b y hy)
  exact hP hx

/-- Clifford bivectors as an ambient Lie subalgebra of the Clifford algebra. This does not put a
Lie bracket on the exterior square itself. -/
noncomputable def cliffordBivectorLieSubalgebra : LieSubalgebra R (CliffordAlgebra Q) :=
  { LinearMap.range (cliffordBivectorExterior Q) with
    lie_mem' := lie_mem_cliffordBivectorExterior_range Q }

/-- Membership in the Clifford bivector Lie subalgebra means being the image of an exterior
bivector. -/
@[simp]
theorem mem_cliffordBivectorLieSubalgebra_iff {x : CliffordAlgebra Q} :
    x ∈ cliffordBivectorLieSubalgebra Q ↔
      ∃ y : ⋀[R]^2 M, cliffordBivectorExterior Q y = x := by
  simpa only [cliffordBivectorLieSubalgebra, LieSubalgebra.mem_mk_iff'] using
    (LinearMap.mem_range (f := cliffordBivectorExterior Q))

/-- The exterior-square Clifford bivector map takes values in the Clifford bivector Lie
subalgebra. -/
@[simp]
theorem cliffordBivectorExterior_mem_cliffordBivectorLieSubalgebra (x : ⋀[R]^2 M) :
    cliffordBivectorExterior Q x ∈ cliffordBivectorLieSubalgebra Q := by
  simpa only [cliffordBivectorLieSubalgebra, LieSubalgebra.mem_mk_iff'] using
    (LinearMap.mem_range_self (cliffordBivectorExterior Q) x)

end CommRing

end CliffordAlgebra

end TauCeti
