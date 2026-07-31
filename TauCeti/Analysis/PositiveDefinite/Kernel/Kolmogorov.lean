/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic
public import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Kolmogorov decomposition of a positive-definite kernel

This file constructs the canonical Hilbert-space realization of a scalar-valued
positive-definite kernel.  A kernel `K : α → α → 𝕜` is first regarded as the operator-valued
kernel whose `(a, b)` entry is multiplication by `K a b` on the one-dimensional Hilbert space
`𝕜`.  Mathlib's `RKHS.OfKernel` construction then gives a Hilbert space and kernel vectors
`Φ a` satisfying

`⟪Φ a, Φ b⟫_𝕜 = K a b`.

The span of the kernel vectors is dense, so this is the minimal Kolmogorov decomposition rather
than an arbitrary realization.  Its universal property gives a unique linear isometry into any
other realization, and a linear isometric equivalence when that realization is also minimal.

This advances Part C of `TauCetiRoadmap/OneParameterSemigroups/README.md`, specifically the
positive-definite-function API item asking for the GNS/Kolmogorov decomposition.  The completion
and reproducing-kernel construction are Mathlib's `RKHS.OfKernel`; this file supplies only the
scalar-kernel bridge and its characteristic API.

## Main declarations

* `TauCeti.positiveDefiniteKernelOperator`: regard a scalar kernel as an operator-valued kernel.
* `TauCeti.IsPositiveDefiniteKernel.posSemidef_positiveDefiniteKernelOperator`: positivity of that
  operator kernel.
* `TauCeti.IsPositiveDefiniteKernel.KolmogorovSpace`: the canonical Hilbert space.
* `TauCeti.IsPositiveDefiniteKernel.kolmogorovFeature`: its canonical feature map.
* `TauCeti.IsPositiveDefiniteKernel.inner_kolmogorovFeature`: the Kolmogorov identity.
* `TauCeti.IsPositiveDefiniteKernel.kolmogorovFeature_dense`: minimality of the decomposition.
* `TauCeti.IsPositiveDefiniteKernel.kolmogorovIsometry`: the universal comparison isometry.
* `TauCeti.IsPositiveDefiniteKernel.kolmogorovEquiv`: equivalence with any other minimal
  realization.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups*,
  Springer GTM 100 (1984), Chapter 3.
-/

public section

open ComplexConjugate ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder

namespace TauCeti

universe u v w

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
theorem posSemidef_positiveDefiniteKernelOperator (hK : IsPositiveDefiniteKernel K) :
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
    have hinner (a b : α) (x y : 𝕜) :
        ⟪positiveDefiniteKernelOperator K b a x, y⟫_𝕜 = star x * K a b * y := by
      rw [positiveDefiniteKernelOperator_apply, RCLike.inner_apply', map_mul,
        isPositiveDefiniteKernel_conj_symm hK, RCLike.star_def]
      ring
    have hquadratic :
        RCLike.re (f.sum fun a x => f.sum fun b y =>
          ⟪positiveDefiniteKernelOperator K b a x, y⟫_𝕜) =
          RCLike.re (f.sum fun a x => f.sum fun b y => star x * K a b * y) := by
      simp only [hinner]
    rw [hquadratic]
    simpa only [Matrix.of_apply] using hre

/-- The canonical Hilbert space in the Kolmogorov decomposition of `K`.

This is an abbreviation because Mathlib's `RKHS.OfKernel` currently has to be an abbreviation in
order for its normed-group and inner-product instances to reduce. -/
noncomputable abbrev KolmogorovSpace (hK : IsPositiveDefiniteKernel K) :=
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨hK.posSemidef_positiveDefiniteKernelOperator⟩
  RKHS.OfKernel (positiveDefiniteKernelOperator K)

/-- The canonical feature map into the Kolmogorov space.  It sends `a` to the reproducing-kernel
vector at `a`, evaluated on the scalar `1`. -/
noncomputable def kolmogorovFeature (hK : IsPositiveDefiniteKernel K) (a : α) :
    hK.KolmogorovSpace := by
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨hK.posSemidef_positiveDefiniteKernelOperator⟩
  exact RKHS.kerFun hK.KolmogorovSpace a 1

/-- **Kolmogorov identity.** Inner products of the canonical feature vectors recover the
original kernel. -/
@[simp]
theorem inner_kolmogorovFeature (hK : IsPositiveDefiniteKernel K) (a b : α) :
    ⟪hK.kolmogorovFeature a, hK.kolmogorovFeature b⟫_𝕜 = K a b := by
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨hK.posSemidef_positiveDefiniteKernelOperator⟩
  rw [kolmogorovFeature, kolmogorovFeature,
    ← RKHS.kernel_inner hK.KolmogorovSpace b a (1 : 𝕜) 1,
    RKHS.OfKernel.kernel_ofKernel]
  simp [isPositiveDefiniteKernel_conj_symm hK]

/-- The squared norm of a canonical feature vector is the real part of the corresponding
diagonal kernel value. -/
@[simp]
theorem norm_kolmogorovFeature_sq (hK : IsPositiveDefiniteKernel K) (a : α) :
    ‖hK.kolmogorovFeature a‖ ^ 2 = RCLike.re (K a a) := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), hK.inner_kolmogorovFeature]

/-- The squared distance between two canonical feature vectors, expressed entirely in terms of
the original kernel. -/
@[simp]
theorem norm_kolmogorovFeature_sub_sq (hK : IsPositiveDefiniteKernel K) (a b : α) :
    ‖hK.kolmogorovFeature a - hK.kolmogorovFeature b‖ ^ 2 =
      RCLike.re (K a a) - 2 * RCLike.re (K a b) + RCLike.re (K b b) := by
  rw [norm_sub_sq (𝕜 := 𝕜), hK.norm_kolmogorovFeature_sq, hK.norm_kolmogorovFeature_sq,
    hK.inner_kolmogorovFeature]

/-- The canonical feature vectors have dense linear span in the Kolmogorov space.  Thus the
construction is minimal: it contains no orthogonal summand invisible to the kernel. -/
theorem kolmogorovFeature_dense (hK : IsPositiveDefiniteKernel K) :
    (Submodule.span 𝕜 (Set.range hK.kolmogorovFeature)).topologicalClosure = ⊤ := by
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨hK.posSemidef_positiveDefiniteKernelOperator⟩
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

private theorem denseRange_featureCombination (hK : IsPositiveDefiniteKernel K) :
    DenseRange (Finsupp.linearCombination 𝕜 hK.kolmogorovFeature) := by
  have hdense : Dense ((Finsupp.linearCombination 𝕜 hK.kolmogorovFeature).range :
      Set hK.KolmogorovSpace) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.2
    rw [Finsupp.range_linearCombination]
    exact hK.kolmogorovFeature_dense
  exact hdense

private theorem norm_featureCombination_eq {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (hK : IsPositiveDefiniteKernel K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b) (f : α →₀ 𝕜) :
    ‖Finsupp.linearCombination 𝕜 φ f‖ =
      ‖Finsupp.linearCombination 𝕜 hK.kolmogorovFeature f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← inner_self_eq_norm_sq (𝕜 := 𝕜)]
  congr 1
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left, inner_smul_right, hφ, hK.inner_kolmogorovFeature]

/-- The unique linear isometry from the canonical Kolmogorov space into any Hilbert-space
realization of `K`.  It sends each canonical feature vector to the corresponding vector in the
given realization. -/
noncomputable def kolmogorovIsometry {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : IsPositiveDefiniteKernel K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b) : hK.KolmogorovSpace →ₗᵢ[𝕜] E := by
  let canonical := Finsupp.linearCombination 𝕜 hK.kolmogorovFeature
  let target := Finsupp.linearCombination 𝕜 φ
  have hdense : DenseRange canonical := denseRange_featureCombination hK
  have hnorm : ∀ f, ‖target f‖ = ‖canonical f‖ := norm_featureCombination_eq hK φ hφ
  have hbound : ∃ C, ∀ f, ‖target f‖ ≤ C * ‖canonical f‖ :=
    ⟨1, fun f => by simp [hnorm f]⟩
  exact LinearIsometry.mk (target.extendOfNorm canonical).toLinearMap fun x => by
    refine hdense.induction_on x (isClosed_eq (target.extendOfNorm canonical).continuous.norm
      continuous_norm) ?_
    intro f
    exact calc
      ‖target.extendOfNorm canonical (canonical f)‖ = ‖target f‖ :=
        congrArg norm (LinearMap.extendOfNorm_eq hdense hbound f)
      _ = ‖canonical f‖ := hnorm f

/-- The universal comparison isometry sends canonical feature vectors to the vectors of the
given realization. -/
@[simp]
theorem kolmogorovIsometry_apply {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : IsPositiveDefiniteKernel K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b) (a : α) :
    hK.kolmogorovIsometry φ hφ (hK.kolmogorovFeature a) = φ a := by
  rw [kolmogorovIsometry]
  have happ := LinearMap.extendOfNorm_eq
    (f := Finsupp.linearCombination 𝕜 φ)
    (e := Finsupp.linearCombination 𝕜 hK.kolmogorovFeature)
    (denseRange_featureCombination hK)
    ⟨1, fun f => by simp [norm_featureCombination_eq hK φ hφ f]⟩ (Finsupp.single a 1)
  simpa only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe,
    Finsupp.linearCombination_single, one_smul] using happ

/-- A linear isometry out of the canonical Kolmogorov space is uniquely determined by its values
on the canonical feature vectors. -/
theorem kolmogorovIsometry_unique {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : IsPositiveDefiniteKernel K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b) (T : hK.KolmogorovSpace →ₗᵢ[𝕜] E)
    (hT : ∀ a, T (hK.kolmogorovFeature a) = φ a) : T = hK.kolmogorovIsometry φ hφ := by
  apply LinearIsometry.ext
  intro x
  have hdense : Dense (Submodule.span 𝕜 (Set.range hK.kolmogorovFeature) :
      Set hK.KolmogorovSpace) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 hK.kolmogorovFeature_dense
  refine hdense.induction ?_ (isClosed_eq T.continuous
    (hK.kolmogorovIsometry φ hφ).continuous) x
  intro y hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, rfl⟩
    rw [hT, hK.kolmogorovIsometry_apply]
  · simp
  · intro p q _ _ hp hq
    simpa using congrArg₂ (· + ·) hp hq
  · intro c p _ hp
    simpa using congrArg (c • ·) hp

/-- If the vectors in a realization of `K` have dense linear span, the universal comparison
isometry is surjective. -/
theorem kolmogorovIsometry_surjective {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : IsPositiveDefiniteKernel K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b)
    (hφdense : (Submodule.span 𝕜 (Set.range φ)).topologicalClosure = ⊤) :
    Function.Surjective (hK.kolmogorovIsometry φ hφ) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hφdense]
  apply Submodule.topologicalClosure_minimal
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨hK.kolmogorovFeature a, hK.kolmogorovIsometry_apply φ hφ a⟩
  · exact (hK.kolmogorovIsometry φ hφ).isometry.isClosedEmbedding.isClosed_range

/-- The canonical Kolmogorov space is linearly isometric to every other minimal realization of
the same kernel. -/
noncomputable def kolmogorovEquiv {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : IsPositiveDefiniteKernel K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b)
    (hφdense : (Submodule.span 𝕜 (Set.range φ)).topologicalClosure = ⊤) :
    hK.KolmogorovSpace ≃ₗᵢ[𝕜] E :=
  LinearIsometryEquiv.ofSurjective (hK.kolmogorovIsometry φ hφ)
    (hK.kolmogorovIsometry_surjective φ hφ hφdense)

/-- The equivalence with another minimal realization sends canonical feature vectors to the
vectors of that realization. -/
@[simp]
theorem kolmogorovEquiv_apply {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : IsPositiveDefiniteKernel K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b)
    (hφdense : (Submodule.span 𝕜 (Set.range φ)).topologicalClosure = ⊤) (a : α) :
    hK.kolmogorovEquiv φ hφ hφdense (hK.kolmogorovFeature a) = φ a := by
  rw [kolmogorovEquiv, LinearIsometryEquiv.coe_ofSurjective]
  exact hK.kolmogorovIsometry_apply φ hφ a

end IsPositiveDefiniteKernel

end TauCeti

end
