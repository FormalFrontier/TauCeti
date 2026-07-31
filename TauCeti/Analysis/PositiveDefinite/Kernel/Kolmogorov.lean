/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic
public import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Kolmogorov decomposition of a positive-definite kernel

This file constructs the canonical Hilbert-space realization of a scalar-valued
positive-definite kernel.  A kernel `K : α → α → 𝕜` is first regarded as the operator-valued
kernel whose `(a, b)` entry is multiplication by `K a b` on the one-dimensional Hilbert space
`𝕜`.  Mathlib's `RKHS.OfKernel` construction then gives a Hilbert space and kernel vectors
`Φ a` satisfying

`⟪Φ a, Φ b⟫_𝕜 = K a b`.

The span of the kernel vectors is dense, so this is the minimal Kolmogorov decomposition rather
than an arbitrary realization.

This advances Part C of `TauCetiRoadmap/OneParameterSemigroups/README.md`, specifically the
positive-definite-function API item asking for the GNS/Kolmogorov decomposition.  The completion
and reproducing-kernel construction are Mathlib's `RKHS.OfKernel`; this file supplies only the
scalar-kernel bridge and its characteristic API.

## Main declarations

* `TauCeti.positiveDefiniteKernelOperator`: regard a scalar kernel as an operator-valued kernel.
* `TauCeti.IsPositiveDefiniteKernel.operator_posSemidef`: positivity of that operator kernel.
* `TauCeti.IsPositiveDefiniteKernel.KolmogorovSpace`: the canonical Hilbert space.
* `TauCeti.IsPositiveDefiniteKernel.kolmogorovFeature`: its canonical feature map.
* `TauCeti.IsPositiveDefiniteKernel.inner_kolmogorovFeature`: the Kolmogorov identity.
* `TauCeti.IsPositiveDefiniteKernel.kolmogorovFeature_dense`: minimality of the decomposition.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups*,
  Springer GTM 100 (1984), Chapter 3.
-/

public section

open ComplexConjugate ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder

namespace TauCeti

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v}

/-- A scalar kernel regarded as an operator-valued kernel on the one-dimensional Hilbert space
`𝕜`: the entry at `(a, b)` is left multiplication by `K a b`. -/
noncomputable def positiveDefiniteKernelOperator (K : α → α → 𝕜) :
    Matrix α α (𝕜 →L[𝕜] 𝕜) :=
  Matrix.of fun a b => ContinuousLinearMap.mul 𝕜 𝕜 (K a b)

@[simp]
theorem positiveDefiniteKernelOperator_apply (K : α → α → 𝕜) (a b : α) (z : 𝕜) :
    positiveDefiniteKernelOperator K a b z = K a b * z := by
  rfl

namespace IsPositiveDefiniteKernel

variable {K : α → α → 𝕜}

/-- The operator-valued kernel obtained from a scalar positive-definite kernel is positive
semidefinite.  This is the bridge needed by Mathlib's `RKHS.OfKernel` construction. -/
theorem operator_posSemidef (hK : IsPositiveDefiniteKernel K) :
    (positiveDefiniteKernelOperator K).PosSemidef := by
  apply (RKHS.posSemidef_tfae (K := positiveDefiniteKernelOperator K)).out 2 0 |>.mp
  refine ⟨?_, ?_⟩
  · apply Matrix.ext
    intro a b
    rw [Matrix.conjTranspose_apply]
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    rw [positiveDefiniteKernelOperator_apply, positiveDefiniteKernelOperator_apply]
    rw [RCLike.inner_apply', RCLike.inner_apply', map_mul,
      isPositiveDefiniteKernel_conj_symm hK]
    ring
  · intro f
    have hnonneg := ((isPositiveDefiniteKernel_def K).mp hK).2 f
    have hre := (RCLike.nonneg_iff.mp hnonneg).1
    simpa [positiveDefiniteKernelOperator_apply, RCLike.star_def, mul_assoc, mul_left_comm,
      mul_comm, isPositiveDefiniteKernel_conj_symm hK] using hre

/-- The canonical Hilbert space in the Kolmogorov decomposition of `K`.

This is an abbreviation because Mathlib's `RKHS.OfKernel` currently has to be an abbreviation in
order for its normed-group and inner-product instances to reduce. -/
noncomputable abbrev KolmogorovSpace (hK : IsPositiveDefiniteKernel K) :=
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef := ⟨hK.operator_posSemidef⟩
  RKHS.OfKernel (positiveDefiniteKernelOperator K)

/-- The canonical feature map into the Kolmogorov space.  It sends `a` to the reproducing-kernel
vector at `a`, evaluated on the scalar `1`. -/
noncomputable def kolmogorovFeature (hK : IsPositiveDefiniteKernel K) (a : α) :
    hK.KolmogorovSpace := by
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef := ⟨hK.operator_posSemidef⟩
  exact RKHS.kerFun hK.KolmogorovSpace a 1

/-- **Kolmogorov identity.** Inner products of the canonical feature vectors recover the
original kernel. -/
theorem inner_kolmogorovFeature (hK : IsPositiveDefiniteKernel K) (a b : α) :
    ⟪hK.kolmogorovFeature a, hK.kolmogorovFeature b⟫_𝕜 = K a b := by
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef := ⟨hK.operator_posSemidef⟩
  rw [kolmogorovFeature, kolmogorovFeature,
    ← RKHS.kernel_inner hK.KolmogorovSpace b a (1 : 𝕜) 1,
    RKHS.OfKernel.kernel_ofKernel]
  simp [isPositiveDefiniteKernel_conj_symm hK]

/-- The squared norm of a canonical feature vector is the real part of the corresponding
diagonal kernel value. -/
theorem norm_kolmogorovFeature_sq (hK : IsPositiveDefiniteKernel K) (a : α) :
    ‖hK.kolmogorovFeature a‖ ^ 2 = RCLike.re (K a a) := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), hK.inner_kolmogorovFeature]

/-- The squared distance between two canonical feature vectors, expressed entirely in terms of
the original kernel. -/
theorem norm_kolmogorovFeature_sub_sq (hK : IsPositiveDefiniteKernel K) (a b : α) :
    ‖hK.kolmogorovFeature a - hK.kolmogorovFeature b‖ ^ 2 =
      RCLike.re (K a a) - 2 * RCLike.re (K a b) + RCLike.re (K b b) := by
  rw [norm_sub_sq (𝕜 := 𝕜), hK.norm_kolmogorovFeature_sq, hK.norm_kolmogorovFeature_sq,
    hK.inner_kolmogorovFeature]

/-- The canonical feature vectors have dense linear span in the Kolmogorov space.  Thus the
construction is minimal: it contains no orthogonal summand invisible to the kernel. -/
theorem kolmogorovFeature_dense (hK : IsPositiveDefiniteKernel K) :
    (Submodule.span 𝕜 (Set.range hK.kolmogorovFeature)).topologicalClosure = ⊤ := by
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef := ⟨hK.operator_posSemidef⟩
  have hspan :
      Submodule.span 𝕜
          {y | ∃ (a : α) (z : 𝕜), RKHS.kerFun hK.KolmogorovSpace a z = y} =
        Submodule.span 𝕜 (Set.range hK.kolmogorovFeature) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro y ⟨a, z, rfl⟩
      have hfeature :
          RKHS.kerFun hK.KolmogorovSpace a z =
            z • RKHS.kerFun hK.KolmogorovSpace a 1 := by
        rw [← map_smul]
        simp
      rw [hfeature]
      exact (Submodule.span 𝕜 (Set.range hK.kolmogorovFeature)).smul_mem z
        (Submodule.subset_span ⟨a, by rw [kolmogorovFeature]⟩)
    · refine Submodule.span_le.2 ?_
      rintro y ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a, 1, by rw [kolmogorovFeature]⟩
  have hdense := RKHS.kerFun_dense (H := hK.KolmogorovSpace)
  rw [hspan] at hdense
  exact hdense

end IsPositiveDefiniteKernel

end TauCeti

end
