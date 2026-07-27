/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Haar
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Averaging over compact groups

This file bundles integration against normalized Haar measure as a continuous linear map on
continuous vector-valued functions. It records the norm bound, constants, and invariance under left
and right translation needed for averaging representations.

The implementation reuses Mathlib's Bochner integral, its commutation with continuous linear maps,
and the generic left-, right-, and inversion-invariance lemmas for integrals on groups.

The construction is the averaging operator from Layer 0 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {V : Type*} [NormedAddCommGroup V]

private theorem integrable_continuousMap (f : C(G, V)) :
    Integrable f (haarProb G) := by
  simpa only [integrableOn_univ] using
    f.continuous.continuousOn.integrableOn_compact (μ := haarProb G) isCompact_univ

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [SMulCommClass ℝ 𝕜 V]

/-- Averaging a continuous vector-valued function against normalized Haar measure, as a
continuous linear map. -/
noncomputable def haarAverage [CompleteSpace V] : C(G, V) →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ g, f g ∂haarProb G
      map_add' := fun f h ↦ integral_add
        (integrable_continuousMap G f) (integrable_continuousMap G h)
      map_smul' := fun c f ↦ integral_smul c f }
    1 fun f ↦ by
      rw [one_mul]
      simpa using norm_integral_le_of_norm_le_const
        (μ := haarProb G) (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- The Haar average is the Bochner integral against normalized Haar measure.

Not a `simp` lemma: `haarAverage` is the normal form here, so that the constant, translation
and inversion lemmas below can be `simp` lemmas. Unfold explicitly with `rw`/`simp` when the
underlying integral is wanted. -/
theorem haarAverage_apply [CompleteSpace V] (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = ∫ g, f g ∂haarProb G :=
  (rfl)

/-- Haar averaging is norm-nonincreasing for the uniform norm on continuous maps. -/
theorem norm_haarAverage_apply_le [CompleteSpace V] (f : C(G, V)) :
    ‖haarAverage G (𝕜 := 𝕜) f‖ ≤ ‖f‖ := by
  rw [haarAverage_apply]
  simpa using norm_integral_le_of_norm_le_const
    (μ := haarProb G) (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- The operator norm of Haar averaging is at most one. -/
theorem norm_haarAverage_le_one [CompleteSpace V] :
    ‖haarAverage G (𝕜 := 𝕜) (V := V)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa using norm_haarAverage_apply_le G (𝕜 := 𝕜) f

/-- The Haar average of a constant function is that constant. -/
@[simp]
theorem haarAverage_const [CompleteSpace V] (v : V) :
    haarAverage G (𝕜 := 𝕜) (ContinuousMap.const G v) = v := by
  simp [haarAverage_apply]

/-- On a nonzero target, Haar averaging has operator norm one. -/
theorem norm_haarAverage [Nontrivial V] [CompleteSpace V] :
    ‖haarAverage G (𝕜 := 𝕜) (V := V)‖ = 1 := by
  apply le_antisymm (norm_haarAverage_le_one G) _
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hnorm : ‖ContinuousMap.const G v‖ = ‖v‖ := by
    apply le_antisymm
    · exact (ContinuousMap.const G v).norm_le (norm_nonneg v) |>.2 fun _ ↦ le_rfl
    · simpa using (ContinuousMap.const G v).norm_coe_le_norm (1 : G)
  have h := (haarAverage G (𝕜 := 𝕜) (V := V)).ratio_le_opNorm
    (ContinuousMap.const G v)
  simpa [haarAverage_const, hnorm, norm_ne_zero_iff.mpr hv] using h

/-- Continuous linear maps commute with Haar averaging. -/
theorem haarAverage_comp_comm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace 𝕜 W] [SMulCommClass ℝ 𝕜 W] [CompleteSpace V] [CompleteSpace W]
    (L : V →L[𝕜] W) (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜)
        ⟨fun g ↦ L (f g), L.continuous.comp f.continuous⟩ =
      L (haarAverage G (𝕜 := 𝕜) f) := by
  rw [haarAverage_apply, haarAverage_apply]
  exact L.integral_comp_comm (integrable_continuousMap G f)

/-- Haar averaging is unchanged by left translation of the argument. -/
@[simp]
theorem haarAverage_comp_mulLeft [CompleteSpace V] (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulLeft g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulLeft]
  exact integral_mul_left_eq_self f g

/-- Haar averaging is unchanged by right translation of the argument. -/
@[simp]
theorem haarAverage_comp_mulRight [CompleteSpace V] (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulRight g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulRight]
  exact integral_mul_right_eq_self f g

/-- Haar averaging is unchanged by inversion of the argument. -/
@[simp]
theorem haarAverage_comp_inv [CompleteSpace V] (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜)
        ⟨fun g ↦ f g⁻¹, f.continuous.comp continuous_inv⟩ =
      haarAverage G (𝕜 := 𝕜) f := by
  rw [haarAverage_apply, haarAverage_apply]
  exact integral_inv_eq_self f (haarProb G)

end CompactGroup

end TauCeti
