/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RepresentationTheory.Continuous.MatrixCoefficient
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Matrix coefficients in `L²` of a compact group

A matrix coefficient `g ↦ ⟪π g v, w⟫` of a continuous representation of a compact group is a
continuous function on a probability space, hence square integrable. This file records its image
in `L²(G)` for normalized Haar measure, and the identities that turn `L²`-statements about matrix
coefficients into integrals.

The `L²` picture is what the Schur orthogonality relations are stated in: they compute the inner
product of two matrix coefficients, and `inner_matrixCoeffLp` below rewrites that inner product as
the Haar integral the orthogonality argument evaluates.

## Main definitions

* `TauCeti.ContRepresentation.matrixCoeffLp`: the matrix coefficient `g ↦ ⟪π g v, w⟫` as an element
  of `Lp 𝕜 2 (haarProb G)`.
* `TauCeti.ContRepresentation.matrixCoeffLpₛₗ`: the matrix coefficients of a fixed representation
  bundled as a sesquilinear map `V →ₗ⋆[𝕜] V →ₗ[𝕜] Lp 𝕜 2 (haarProb G)`.

## Main statements

* `TauCeti.ContRepresentation.inner_matrixCoeffLp`: the `L²` inner product of two matrix
  coefficients is the Haar integral of their pointwise product, in Mathlib's convention
  `⟪F, H⟫ = ∫ H · conj F`.
* `TauCeti.ContRepresentation.norm_matrixCoeffLp_sq`: the squared `L²` norm is the Haar integral of
  the squared modulus.
* `TauCeti.ContRepresentation.norm_matrixCoeffLp_le`: for a unitary representation the `L²` norm is
  at most `‖v‖ * ‖w‖`, because normalized Haar measure has total mass one.
* `TauCeti.ContRepresentation.matrixCoeffLp_eq_zero_iff`: passing to `L²` loses no information,
  since Haar measure is positive on nonempty open sets.

This is the second half of the Layer 3 milestone of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), whose first half is the
uniform-norm algebra in `TauCeti/RepresentationTheory/Continuous/MatrixCoefficient.lean`. The
mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section CompactGroup

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- The matrix coefficient `g ↦ ⟪π g v, w⟫` as an element of `L²(G)` for normalized Haar measure.

A matrix coefficient is continuous and `G` is compact, so `ContinuousMap.toLp` applies; the
normalization of Haar measure to a probability measure is what makes the resulting `L²` norms
comparable to the uniform norm without a measure-dependent constant. -/
@[expose] noncomputable def matrixCoeffLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) : Lp 𝕜 2 (haarProb G) :=
  ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w)

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem matrixCoeffLp_def (v w : V) :
    matrixCoeffLp π hπ v w = ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w) :=
  rfl

/-- A matrix coefficient in `L²` is represented, almost everywhere, by the function it comes
from. -/
theorem coeFn_matrixCoeffLp (v w : V) :
    matrixCoeffLp π hπ v w =ᵐ[haarProb G] fun g ↦ ⟪π g v, w⟫_𝕜 := by
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (haarProb G)
    (matrixCoeff π hπ v w)] with g hg
  rw [matrixCoeffLp_def, hg, matrixCoeff_apply]

/-! ### Sesquilinearity in the defining vectors

Passing to `L²` is linear, so the sesquilinearity of `matrixCoeff` transfers verbatim. -/

@[simp]
theorem matrixCoeffLp_zero_left (w : V) : matrixCoeffLp π hπ 0 w = 0 := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_zero_right (v : V) : matrixCoeffLp π hπ v 0 = 0 := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_add_left (v₁ v₂ w : V) :
    matrixCoeffLp π hπ (v₁ + v₂) w = matrixCoeffLp π hπ v₁ w + matrixCoeffLp π hπ v₂ w := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_add_right (v w₁ w₂ : V) :
    matrixCoeffLp π hπ v (w₁ + w₂) = matrixCoeffLp π hπ v w₁ + matrixCoeffLp π hπ v w₂ := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_smul_left (c : 𝕜) (v w : V) :
    matrixCoeffLp π hπ (c • v) w = (starRingEnd 𝕜) c • matrixCoeffLp π hπ v w := by
  simp [matrixCoeffLp_def]

@[simp]
theorem matrixCoeffLp_smul_right (v : V) (c : 𝕜) (w : V) :
    matrixCoeffLp π hπ v (c • w) = c • matrixCoeffLp π hπ v w := by
  simp [matrixCoeffLp_def]

/-- The `L²` matrix coefficients of a fixed representation, bundled as a sesquilinear map:
conjugate linear in the first vector, linear in the second, exactly as Mathlib's `innerₛₗ`.

This is the map whose range spans the `π`-isotypic block of `L²(G)`, and bundling supplies the
remaining additive identities (`map_neg`, `map_sub`, `map_sum`) through the `LinearMap` API. -/
noncomputable def matrixCoeffLpₛₗ : V →ₗ⋆[𝕜] V →ₗ[𝕜] Lp 𝕜 2 (haarProb G) where
  toFun v :=
    { toFun := matrixCoeffLp π hπ v
      map_add' := matrixCoeffLp_add_right π hπ v
      map_smul' := matrixCoeffLp_smul_right π hπ v }
  map_add' v₁ v₂ := LinearMap.ext fun w ↦ matrixCoeffLp_add_left π hπ v₁ v₂ w
  map_smul' c v := LinearMap.ext fun w ↦ matrixCoeffLp_smul_left π hπ c v w

@[simp]
theorem matrixCoeffLpₛₗ_apply_apply (v w : V) :
    matrixCoeffLpₛₗ π hπ v w = matrixCoeffLp π hπ v w :=
  (rfl)

/-! ### Passing to `L²` loses no information

Haar measure is positive on nonempty open sets, so two continuous functions agreeing almost
everywhere agree. -/

theorem matrixCoeffLp_eq_zero_iff (v w : V) :
    matrixCoeffLp π hπ v w = 0 ↔ matrixCoeff π hπ v w = 0 := by
  constructor
  · intro h
    refine ContinuousMap.toLp_injective (𝕜 := 𝕜) (p := 2) (haarProb G) ?_
    rw [← matrixCoeffLp_def, h, map_zero]
  · intro h
    rw [matrixCoeffLp_def, h, map_zero]

/-- A matrix coefficient vanishes in `L²` exactly when it vanishes identically. -/
theorem matrixCoeffLp_eq_zero_iff_forall (v w : V) :
    matrixCoeffLp π hπ v w = 0 ↔ ∀ g : G, ⟪π g v, w⟫_𝕜 = 0 := by
  rw [matrixCoeffLp_eq_zero_iff]
  constructor
  · intro h g
    rw [← matrixCoeff_apply π hπ v w g, h, ContinuousMap.zero_apply]
  · intro h
    ext g
    simpa using h g

/-! ### The inner product as a Haar integral -/

/-- The `L²` inner product of two matrix coefficients is the Haar integral of their pointwise
product. Mathlib's inner product is conjugate linear in its first argument and unfolds as
`⟪F, H⟫ = ∫ H · conj F`, which is where the conjugation sits below; this placement is what the
Schur orthogonality relations are stated against. -/
theorem inner_matrixCoeffLp (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) (v w : V)
    (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜
      = ∫ g, ⟪ρ g v', w'⟫_𝕜 * (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 ∂(haarProb G) := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, ContinuousMap.inner_toLp]
  simp

/-- The squared `L²` norm of a matrix coefficient is the Haar integral of its squared modulus. -/
theorem norm_matrixCoeffLp_sq (v w : V) :
    ‖matrixCoeffLp π hπ v w‖ ^ 2 = ∫ g, ‖⟪π g v, w⟫_𝕜‖ ^ 2 ∂(haarProb G) := by
  have h := inner_matrixCoeffLp π hπ π hπ v w v w
  rw [inner_self_eq_norm_sq_to_K] at h
  have hpt : ∀ g : G,
      ⟪π g v, w⟫_𝕜 * (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 = ((‖⟪π g v, w⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
    intro g
    rw [RCLike.mul_conj]
    push_cast
    ring
  simp_rw [hpt, integral_ofReal] at h
  exact_mod_cast h

/-! ### Bounds from the normalization of Haar measure -/

/-- The `L²` norm of a matrix coefficient of a unitary representation is at most the product of the
norms of its defining vectors, with no constant: the pointwise bound `‖v‖ * ‖w‖` integrates to
itself because normalized Haar measure has total mass one. -/
theorem norm_matrixCoeffLp_le (hunitary : IsUnitary π) (v w : V) :
    ‖matrixCoeffLp π hπ v w‖ ≤ ‖v‖ * ‖w‖ := by
  have hsq : ‖matrixCoeffLp π hπ v w‖ ^ 2 ≤ (‖v‖ * ‖w‖) ^ 2 := by
    rw [norm_matrixCoeffLp_sq]
    calc ∫ g, ‖⟪π g v, w⟫_𝕜‖ ^ 2 ∂(haarProb G)
        ≤ ∫ _ : G, (‖v‖ * ‖w‖) ^ 2 ∂(haarProb G) :=
          integral_mono_of_nonneg (.of_forall fun _ ↦ sq_nonneg _) (integrable_const _)
            (.of_forall fun g ↦
              pow_le_pow_left₀ (norm_nonneg _) (hunitary.norm_inner_map_le g v w) 2)
      _ = (‖v‖ * ‖w‖) ^ 2 := by simp
  rw [← Real.sqrt_sq (norm_nonneg (matrixCoeffLp π hπ v w)),
    ← Real.sqrt_sq (mul_nonneg (norm_nonneg v) (norm_nonneg w))]
  exact Real.sqrt_le_sqrt hsq

/-! ### The trivial representation, and subrepresentations -/

/-- The matrix coefficients of the trivial representation are constants, and normalized Haar
measure gives a constant its own norm. This is the sanity check that `matrixCoeffLp` carries the
probability normalization rather than an unnormalized one. -/
theorem norm_matrixCoeffLp_trivial (v w : V) :
    ‖matrixCoeffLp (ContRepresentation.trivial 𝕜 G V) continuous_const v w‖ = ‖⟪v, w⟫_𝕜‖ := by
  have h : ‖matrixCoeffLp (ContRepresentation.trivial 𝕜 G V) continuous_const v w‖ ^ 2
      = ‖⟪v, w⟫_𝕜‖ ^ 2 := by
    rw [norm_matrixCoeffLp_sq]
    simp
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq (norm_nonneg _)]

/-- A matrix coefficient of an invariant submodule is the matrix coefficient of the ambient
representation at the underlying vectors, so passing to a subrepresentation creates no new
elements of `L²(G)`. -/
@[simp]
theorem matrixCoeffLp_subrepresentation {U : Submodule 𝕜 V} (hU : ∀ g, ∀ v ∈ U, π g v ∈ U)
    (v w : U) :
    matrixCoeffLp (subrepresentation π U hU) (continuous_subrepresentation hπ) v w
      = matrixCoeffLp π hπ (v : V) (w : V) := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, matrixCoeff_subrepresentation]

end CompactGroup

end ContRepresentation

end TauCeti
