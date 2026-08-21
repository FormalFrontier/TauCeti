/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.NoncommRing
import Mathlib.Data.Fin.Tuple.Reflection
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
the later Layer 9 arbitrary-form realization. It constructs neither `bivectorEquivSo` nor
`soEquivQuadratic`, and it does not construct a transported Lie bracket, a Spin action, or the
Layer 9 CAR worked instance.

## Main definitions

* `CliffordAlgebra.bivector`: the half-normalized commutator of two Clifford
  generators.
* `CliffordAlgebra.bivectorAlternating`: the corresponding alternating map.
* `CliffordAlgebra.bivectorExterior`: the induced linear map from the second
  exterior power.

## Main results

* `CliffordAlgebra.bivector_lie_ι`: its commutator action on a generator is the
  infinitesimal rotation determined by `QuadraticMap.polar`.
* `CliffordAlgebra.bivectorExterior_apply_ιMulti`: the exterior-square map on a
  decomposable bivector.
* `CliffordAlgebra.equivExterior_bivector`,
  `CliffordAlgebra.equivExterior_bivectorExterior`, and
  `CliffordAlgebra.bivectorExterior_injective`: the exterior model sends
  bivectors to exterior products, so the exterior-square map is injective.
* `CliffordAlgebra.bivector_mem_evenOdd_zero` and
  `CliffordAlgebra.bivector_mem_filtration_two`: it is even and has filtration
  degree at most two.
* `CliffordAlgebra.bivectorExterior_range_le_of_bivector_mem`: the
  exterior-square map lands in any submodule containing the Clifford bivectors.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 3, "the Lie algebra `𝔰𝔬(V) ≅ ⋀²V` inside the Clifford algebra".
-/

public section


universe u v

namespace CliffordAlgebra

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The half-normalized Clifford commutator of two generators. Its action on a third generator is
the infinitesimal rotation in `bivector_lie_ι`; that action, rather than this expression,
fixes the normalization. -/
noncomputable def bivector (a b : M) : CliffordAlgebra Q :=
  (⅟ (2 : R)) • (ι Q a * ι Q b - ι Q b * ι Q a)

/-- The defining half-normalized commutator formula for a Clifford bivector. -/
theorem bivector_def (a b : M) :
    bivector Q a b = (⅟ (2 : R)) • (ι Q a * ι Q b - ι Q b * ι Q a) := by
  rw [bivector]

/-- The alternating map whose value on two vectors is their half-normalized Clifford bivector. -/
noncomputable def bivectorAlternating : M [⋀^Fin 2]→ₗ[R] CliffordAlgebra Q :=
  { toFun := fun v => bivector Q (v 0) (v 1)
    map_update_add' := by
      intro _ v i x y
      fin_cases i <;>
        simp [bivector_def, add_mul, mul_add, smul_sub] <;>
        module
    map_update_smul' := by
      intro _ v i c x
      fin_cases i <;>
        simp [bivector_def, smul_sub, smul_smul, mul_comm]
    map_eq_zero_of_eq' := by
      intro v i j h hij
      fin_cases i <;> fin_cases j <;> simp_all [bivector_def] }

-- Proving the exported `bivectorAlternating_apply` by `rfl` directly would require
-- `bivectorAlternating` to be `@[expose]`d, which it deliberately is not. The `rfl` is
-- therefore done here, inside the module, and re-exported below.
private theorem bivectorAlternating_apply_internal (a b : M) :
    bivectorAlternating Q ![a, b] = bivector Q a b := rfl

/-- The alternating map agrees with the half-normalized Clifford bivector on a pair of vectors. -/
@[simp]
theorem bivectorAlternating_apply (a b : M) :
    bivectorAlternating Q ![a, b] = bivector Q a b :=
  bivectorAlternating_apply_internal Q a b

/-- The linear map from the second exterior power induced by the Clifford bivector. -/
noncomputable def bivectorExterior : ⋀[R]^2 M →ₗ[R] CliffordAlgebra Q :=
  exteriorPower.alternatingMapLinearEquiv (bivectorAlternating Q)

/-- The exterior-square Clifford bivector map on a decomposable bivector. -/
@[simp]
theorem bivectorExterior_apply_ιMulti (a b : M) :
    bivectorExterior Q (exteriorPower.ιMulti R 2 ![a, b]) = bivector Q a b := by
  simp [bivectorExterior]

private theorem equivExterior_ι_mul_ι_sub_swap (a b : M) :
    equivExterior Q (ι Q a * ι Q b - ι Q b * ι Q a) =
      ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b -
        ExteriorAlgebra.ι R b * ExteriorAlgebra.ι R a := by
  simp only [equivExterior, map_sub, changeFormEquiv_apply, changeForm_ι_mul_ι]
  rw [QuadraticMap.associated_isSymm R (-Q) a b]
  module

/-- The exterior model sends a half-normalized Clifford bivector to its exterior product. -/
theorem equivExterior_bivector (a b : M) :
    equivExterior Q (bivector Q a b) = ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b := by
  rw [bivector_def, map_smul, equivExterior_ι_mul_ι_sub_swap]
  rw [eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap a b),
    sub_neg_eq_add, ← two_smul R, invOf_smul_smul]

private theorem equivExterior_comp_bivectorExterior :
    (equivExterior Q).toLinearMap.comp (bivectorExterior Q) = (⋀[R]^2 M).subtype := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  have hx : x = ![x 0, x 1] := (FinVec.etaExpand_eq x).symm
  rw [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.compAlternatingMap_apply, LinearEquiv.coe_coe]
  rw [hx, bivectorExterior_apply_ιMulti, equivExterior_bivector]
  simp

/-- The exterior model is a left inverse of the exterior-square Clifford bivector map.

As with `equivExterior_basis`, this is not a simp lemma because simp unfolds `equivExterior`
before rewriting its applications. -/
theorem equivExterior_bivectorExterior (x : ⋀[R]^2 M) :
    equivExterior Q (bivectorExterior Q x) = (x : ExteriorAlgebra R M) :=
  LinearMap.congr_fun (equivExterior_comp_bivectorExterior Q) x

/-- The exterior-square Clifford bivector map is injective. -/
theorem bivectorExterior_injective : Function.Injective (bivectorExterior Q) := by
  apply Function.Injective.of_comp (f := equivExterior Q)
  -- `of_comp` exposes function composition, while the named equation uses `LinearMap.comp`.
  change Function.Injective ((equivExterior Q).toLinearMap.comp (bivectorExterior Q))
  simpa only [equivExterior_comp_bivectorExterior] using
    Submodule.subtype_injective (⋀[R]^2 M)

/-- Interchanging the two vectors negates their Clifford bivector. -/
theorem bivector_swap (a b : M) :
    bivector Q b a = -bivector Q a b := by
  rw [← bivectorAlternating_apply, ← bivectorAlternating_apply]
  convert (bivectorAlternating Q).map_swap (v := ![a, b])
    (by decide : (0 : Fin 2) ≠ 1) using 1
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The Clifford bivector of a repeated vector is zero. -/
@[simp]
theorem bivector_self (a : M) : bivector Q a a = 0 := by
  simpa only [bivectorAlternating_apply] using
    (bivectorAlternating Q).map_eq_zero_of_eq ![a, a] (by simp)
      (by decide : (0 : Fin 2) ≠ 1)

/-- Clifford bivectors are even. -/
theorem bivector_mem_evenOdd_zero (a b : M) :
    bivector Q a b ∈ evenOdd Q 0 := by
  rw [bivector_def]
  exact Submodule.smul_mem _ _ <|
    Submodule.sub_mem _ (ι_mul_ι_mem_evenOdd_zero Q a b) (ι_mul_ι_mem_evenOdd_zero Q b a)

/-- Clifford bivectors have filtration degree at most two. -/
theorem bivector_mem_filtration_two (a b : M) :
    bivector Q a b ∈ filtration Q 2 := by
  rw [bivector_def]
  exact Submodule.smul_mem _ _ <|
    Submodule.sub_mem _ (ι_mul_ι_mem_filtration_two Q a b) (ι_mul_ι_mem_filtration_two Q b a)

/-- The image of the exterior-square Clifford bivector map lands in any submodule containing every
Clifford bivector: the decomposable bivectors generate `⋀[R]^2 M`. -/
theorem bivectorExterior_range_le_of_bivector_mem
    (P : Submodule R (CliffordAlgebra Q))
    (hP : ∀ a b : M, bivector Q a b ∈ P) :
    LinearMap.range (bivectorExterior Q) ≤ P := by
  rw [LinearMap.range_eq_map, Submodule.map_le_iff_le_comap,
    ← exteriorPower.ιMulti_span R 2 M]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv]
  -- Rewriting does not unfold membership in the comap, so expose the map application explicitly.
  change bivectorExterior Q (exteriorPower.ιMulti R 2 ![v 0, v 1]) ∈ P
  rw [bivectorExterior_apply_ιMulti]
  exact hP _ _

/-- The action-normalization identity for the half-normalized Clifford bivector. -/
theorem bivector_lie_ι (a b x : M) :
    ⁅bivector Q a b, ι Q x⁆ =
      ι Q (QuadraticMap.polar Q b x • a - QuadraticMap.polar Q a x • b) := by
  rw [bivector_def, Ring.lie_def]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [map_sub, map_smul, map_smul]
  have hbx := ι_mul_ι_add_swap (Q := Q) b x
  have hax := ι_mul_ι_add_swap (Q := Q) a x
  -- A generator commutes past a scalar, turning the product into a scalar action.
  have hcomm (m : M) (r : R) : ι Q m * algebraMap R (CliffordAlgebra Q) r = r • ι Q m := by
    rw [← Algebra.commutes r (ι Q m), Algebra.smul_def]
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
            rw [hcomm a, hcomm b, ← Algebra.smul_def, ← Algebra.smul_def]
            rw [two_smul R]
            abel
  rw [h]
  exact invOf_smul_smul (2 : R) _

end CommRing

end CliffordAlgebra
