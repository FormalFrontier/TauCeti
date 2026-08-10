/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.ApproximateIdentity
public import TauCeti.RepresentationTheory.Compact.EigenspaceRepresentation
public import TauCeti.RepresentationTheory.Compact.MatrixCoefficient

/-!
# The representative ring of a compact group is dense

This file proves the analytic core of the Peter-Weyl theorem: on a compact Hausdorff group the
representative ring `𝓡(G)`, the span of the matrix coefficients of the finite-dimensional
continuous representations, is **dense in `C(G, 𝕜)` for the uniform norm**
(`TauCeti.representativeStarSubalgebra_dense`).

Both halves of the argument are already available and are combined here.

* An approximate identity (`TauCeti.exists_isMollifier_norm_convolutionCLM_toLp_sub_le`)
  approximates a continuous function `f` uniformly by convolutions `k * f` against mollifying
  kernels supported near the identity.
* Spectral theory (`TauCeti.convolutionCLM_mem_closure_representativeSubmodule`) puts every
  convolution against a symmetric kernel in the uniform closure of `𝓡(G)`: the eigenspaces of a
  compact self-adjoint convolution operator span a dense subspace of `L²(G)`, and each eigenspace
  at a nonzero eigenvalue carries a finite-dimensional continuous representation whose matrix
  coefficients are what the convolution produces.

Nothing in either half assumes that `G` has any finite-dimensional representations, or that they
separate points; the representations are manufactured from the spectral theorem. Point separation
is the *consequence* proved below, not an input, so the argument is not circular. From it, the
finite-dimensional continuous representations of a compact group separate its points
(`TauCeti.exists_contRepresentation_apply_ne`), and in particular a nonidentity element is moved by
one of them (`TauCeti.exists_contRepresentation_apply_ne_one`).

Uniform density also gives `L²` density: continuous functions are dense in `L²(G)`, so the image of
`𝓡(G)` in `L²(G)` is dense (`TauCeti.representativeLpSubmodule_dense`) and its orthogonal
complement vanishes (`TauCeti.orthogonal_representativeLpSubmodule_eq_bot`). That is the statement
the Peter-Weyl Hilbert basis is assembled from, once the orthonormality of the normalized matrix
coefficients is combined with it.

## Main definitions

* `TauCeti.representativeLpSubmodule`: the image of the representative ring `𝓡(G)` in `L²(G)`.

## Main statements

* `TauCeti.representativeSubmodule_dense` and `TauCeti.representativeStarSubalgebra_dense`:
  **the representative ring is uniformly dense in `C(G, 𝕜)`.**
* `TauCeti.exists_mem_representativeSubmodule_norm_sub_lt`: the same, quantitatively.
* `TauCeti.exists_isRepresentative_apply_ne` and
  `TauCeti.representativeStarSubalgebra_separatesPoints`: the representative functions separate the
  points of `G`.
* `TauCeti.exists_contRepresentation_apply_ne`, `TauCeti.exists_contRepresentation_apply_ne_one`:
  the finite-dimensional continuous representations separate the points of `G`, and every
  nonidentity element acts nontrivially in one of them.
* `TauCeti.representativeLpSubmodule_dense` and
  `TauCeti.orthogonal_representativeLpSubmodule_eq_bot`: the representative ring is dense in
  `L²(G)`, equivalently its orthogonal complement is trivial.
* `TauCeti.eq_zero_of_inner_matrixCoeffLp_eq_zero`: **the matrix coefficients are complete in
  `L²(G)`**, an `L²` class orthogonal to all of them being zero.

## Implementation notes

Separation of points is deduced from density rather than proved directly: the functions agreeing
at two fixed points form a closed subspace of `C(G, 𝕜)`, so if every representative function agreed
at `x` and `y` then so would every continuous function, which Urysohn's lemma forbids on a compact
Hausdorff space. Descending from a representative *function* separating `x` and `y` to a
*representation* separating them is immediate, because a matrix coefficient of `π` takes the same
value at `x` and at `y` as soon as `π x = π y`.

## References

This is the Layer 5 density milestone of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
which asks for `representativeStarSubalgebra_dense` proved by the non-circular convolution route
and for `representativeStarSubalgebra_separatesPoints` and the `L²` density as its corollaries.

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), §5.2.
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 4.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III.
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace Topology

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-! ### Uniform density in `C(G, 𝕜)` -/

variable (𝕜 G) in
/-- **The representative ring of a compact group is uniformly dense in `C(G, 𝕜)`.** This is the
analytic core of the Peter-Weyl theorem.

A continuous `f` is uniformly within `ε` of a convolution `k * f` against a mollifying kernel
(`TauCeti.exists_isMollifier_norm_convolutionCLM_toLp_sub_le`), and a mollifying kernel is
symmetric, so that convolution lies in the uniform closure of `𝓡(G)`
(`TauCeti.convolutionCLM_mem_closure_representativeSubmodule`). Hence `f` lies in the closure of
the closure, which is the closure. -/
theorem representativeSubmodule_dense :
    Dense (representativeSubmodule 𝕜 G : Set C(G, 𝕜)) := by
  intro f
  rw [← closure_closure]
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨k, hk, hkf⟩ :=
    exists_isMollifier_norm_convolutionCLM_toLp_sub_le 𝕜 f (half_pos hε) Filter.univ_mem
  refine ⟨convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f),
    convolutionCLM_mem_closure_representativeSubmodule k hk.inv_apply_eq_conj _, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact hkf.trans_lt (half_lt_self hε)

variable (𝕜 G) in
/-- **The representative ring is uniformly dense**, in the `*`-subalgebra packaging. -/
theorem representativeStarSubalgebra_dense :
    Dense (representativeStarSubalgebra 𝕜 G : Set C(G, 𝕜)) := by
  have hcoe : (representativeStarSubalgebra 𝕜 G : Set C(G, 𝕜))
      = (representativeSubmodule 𝕜 G : Set C(G, 𝕜)) :=
    Set.ext fun _ => mem_representativeStarSubalgebra_iff
  rw [hcoe]
  exact representativeSubmodule_dense 𝕜 G

/-- **Uniform approximation by matrix coefficients, quantitatively.** Every continuous function on
a compact group is uniformly approximated, to any prescribed accuracy, by a finite linear
combination of matrix coefficients of finite-dimensional continuous representations. -/
theorem exists_mem_representativeSubmodule_norm_sub_lt (f : C(G, 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h ∈ representativeSubmodule 𝕜 G, ‖h - f‖ < ε := by
  obtain ⟨h, hh, hdist⟩ := Metric.mem_closure_iff.1 (representativeSubmodule_dense 𝕜 G f) ε hε
  exact ⟨h, hh, by rwa [dist_comm, dist_eq_norm] at hdist⟩

/-! ### Separation of points -/

/-- **The representative functions separate the points of a compact group.** If every matrix
coefficient of every finite-dimensional continuous representation took the same value at `x` and at
`y`, then so would every element of the span; the functions with that property form a closed
subspace of `C(G, 𝕜)`, so by density every continuous function would, contradicting Urysohn's
lemma.

This is a corollary of the density theorem and must not be used in proving it: that the
finite-dimensional representations of a compact group separate points is equivalent to Peter-Weyl,
not an ingredient of it. -/
theorem exists_isRepresentative_apply_ne {x y : G} (hxy : x ≠ y) :
    ∃ f : C(G, 𝕜), IsRepresentative f ∧ f x ≠ f y := by
  by_contra hcon
  push Not at hcon
  -- The difference of the two evaluations is a continuous linear functional on `C(G, 𝕜)`.
  set L : C(G, 𝕜) →ₗ[𝕜] 𝕜 :=
    { toFun := fun f => f x - f y
      map_add' := fun f g => by simp only [ContinuousMap.add_apply]; ring
      map_smul' := fun c f => by simp only [ContinuousMap.smul_apply, RingHom.id_apply]; ring }
  have hLcont : Continuous L := (continuous_eval_const x).sub (continuous_eval_const y)
  -- Its kernel is a closed subspace containing every representative function, hence everything.
  have hker : ∀ f : C(G, 𝕜), f x = f y := by
    have hle : representativeSubmodule 𝕜 G ≤ LinearMap.ker L :=
      representativeSubmodule_le fun f hf => sub_eq_zero.2 (hcon f hf)
    have hclosed : IsClosed ((LinearMap.ker L : Submodule 𝕜 C(G, 𝕜)) : Set C(G, 𝕜)) :=
      isClosed_eq hLcont continuous_const
    intro f
    exact sub_eq_zero.1 (closure_minimal hle hclosed (representativeSubmodule_dense 𝕜 G f))
  -- Urysohn's lemma produces a continuous function that does separate `x` from `y`.
  obtain ⟨u, hux, huy, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := x))
      (isClosed_singleton (x := y)) (by simpa using hxy)
  have hux' : u x = 0 := hux rfl
  have huy' : u y = 1 := huy rfl
  have hone : ((0 : ℝ) : 𝕜) = ((1 : ℝ) : 𝕜) := by
    have h := hker ⟨fun z => ((u z : ℝ) : 𝕜), RCLike.continuous_ofReal.comp u.continuous⟩
    simp only [ContinuousMap.coe_mk] at h
    rwa [hux', huy'] at h
  simp at hone

/-- **The representative `*`-subalgebra separates points.** The Stone-Weierstrass hypothesis, here
a consequence of the density theorem rather than a route to it. -/
theorem representativeStarSubalgebra_separatesPoints :
    (representativeStarSubalgebra 𝕜 G).SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hf, hne⟩ := exists_isRepresentative_apply_ne (𝕜 := 𝕜) hxy
  exact ⟨f, ⟨f, mem_representativeStarSubalgebra_iff.2
    (mem_representativeSubmodule_of_isRepresentative hf), rfl⟩, hne⟩

/-- **The finite-dimensional continuous representations of a compact group separate its points.**
If `π x = π y` for every one of them then every matrix coefficient agrees at `x` and `y`, which
`TauCeti.exists_isRepresentative_apply_ne` forbids. -/
theorem exists_contRepresentation_apply_ne {x y : G} (hxy : x ≠ y) :
    ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
      Continuous π ∧ π x ≠ π y := by
  obtain ⟨f, hf, hne⟩ := exists_isRepresentative_apply_ne (𝕜 := 𝕜) hxy
  obtain ⟨n, π, hπ, v, w, rfl⟩ := hf.exists_eq_matrixCoeff
  refine ⟨n, π, hπ, fun h => hne ?_⟩
  rw [ContRepresentation.matrixCoeff_apply, ContRepresentation.matrixCoeff_apply, h]

/-- **A nonidentity element of a compact group acts nontrivially in some finite-dimensional
continuous representation.** In particular a compact group all of whose finite-dimensional
continuous representations are trivial is itself trivial. -/
theorem exists_contRepresentation_apply_ne_one {g : G} (hg : g ≠ 1) :
    ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
      Continuous π ∧ π g ≠ 1 := by
  obtain ⟨n, π, hπ, hne⟩ := exists_contRepresentation_apply_ne (𝕜 := 𝕜) hg
  exact ⟨n, π, hπ, fun h => hne (by rw [h, map_one])⟩

/-! ### Density in `L²(G)` -/

variable (𝕜 G) in
/-- **The representative ring inside `L²(G)`**: the image of `𝓡(G)` under the inclusion of
continuous functions into `L²` for normalized Haar measure. It is the span of the `L²` classes of
the matrix coefficients of the finite-dimensional continuous representations. -/
noncomputable def representativeLpSubmodule : Submodule 𝕜 (Lp 𝕜 2 (haarProb G)) :=
  (representativeSubmodule 𝕜 G).map (ContinuousMap.toLp 2 (haarProb G) 𝕜).toLinearMap

omit [T2Space G] in
variable (𝕜 G) in
/-- The `L²` representative ring is the image of the uniform one. -/
theorem coe_representativeLpSubmodule :
    (representativeLpSubmodule 𝕜 G : Set (Lp 𝕜 2 (haarProb G)))
      = ContinuousMap.toLp 2 (haarProb G) 𝕜 '' (representativeSubmodule 𝕜 G) :=
  Submodule.map_coe _ _

omit [T2Space G] in
/-- Membership in the `L²` representative ring: being the `L²` class of a representative
function. -/
theorem mem_representativeLpSubmodule_iff {u : Lp 𝕜 2 (haarProb G)} :
    u ∈ representativeLpSubmodule 𝕜 G ↔
      ∃ a ∈ representativeSubmodule 𝕜 G, ContinuousMap.toLp 2 (haarProb G) 𝕜 a = u :=
  Submodule.mem_map

variable (𝕜 G) in
/-- **The representative ring is dense in `L²(G)`.** Continuous functions are dense in `L²` of a
compact group, and the representative ring is uniformly dense in them, so its `L²` classes are
dense. -/
theorem representativeLpSubmodule_dense :
    Dense (representativeLpSubmodule 𝕜 G : Set (Lp 𝕜 2 (haarProb G))) := by
  rw [coe_representativeLpSubmodule]
  set T := (ContinuousMap.toLp 2 (haarProb G) 𝕜 : C(G, 𝕜) →L[𝕜] Lp 𝕜 2 (haarProb G))
  have hrange : Dense (range T) :=
    ContinuousMap.toLp_denseRange (E := 𝕜) (p := 2) (haarProb G) 𝕜 (by simp)
  refine dense_closure.1 (hrange.mono ?_)
  rw [← image_univ, ← (representativeSubmodule_dense 𝕜 G).closure_eq]
  exact image_closure_subset_closure_image T.continuous

variable (𝕜 G) in
/-- **No nonzero `L²` class is orthogonal to every matrix coefficient.** This is the `L²`-density
statement in the form the Peter-Weyl Hilbert basis is assembled from: combined with the
orthonormality of the normalized matrix coefficients it says that they form a Hilbert basis of
`L²(G)`. -/
theorem orthogonal_representativeLpSubmodule_eq_bot :
    (representativeLpSubmodule 𝕜 G)ᗮ = ⊥ :=
  Submodule.topologicalClosure_eq_top_iff.1
    (Submodule.dense_iff_topologicalClosure_eq_top.1 (representativeLpSubmodule_dense 𝕜 G))

/-- **Completeness of the matrix coefficients in `L²(G)`.** An `L²` class orthogonal to every
matrix coefficient of every finite-dimensional continuous representation vanishes. Combined with
the Schur orthogonality relations, this is what makes the normalized matrix coefficients a Hilbert
basis of `L²(G)`.

Restricting the hypothesis to the standard models `EuclideanSpace 𝕜 (Fin n)` makes the statement
stronger and loses nothing: by `TauCeti.isRepresentative_matrixCoeff` a matrix coefficient of a
continuous representation on an arbitrary finite-dimensional inner product space is itself a matrix
coefficient on a standard model, so orthogonality to all of those follows. -/
theorem eq_zero_of_inner_matrixCoeffLp_eq_zero {f : Lp 𝕜 2 (haarProb G)}
    (h : ∀ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))) (hπ : Continuous π)
      (v w : EuclideanSpace 𝕜 (Fin n)),
        ⟪f, ContRepresentation.matrixCoeffLp π hπ v w⟫_𝕜 = 0) :
    f = 0 := by
  have hle : representativeSubmodule 𝕜 G ≤
      LinearMap.ker ((innerSL 𝕜 f).toLinearMap ∘ₗ
        (ContinuousMap.toLp 2 (haarProb G) 𝕜 : C(G, 𝕜) →L[𝕜] Lp 𝕜 2 (haarProb G)).toLinearMap) := by
    refine representativeSubmodule_le fun a ha => ?_
    obtain ⟨n, π, hπ, v, w, rfl⟩ := ha.exists_eq_matrixCoeff
    simpa only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      ← ContRepresentation.matrixCoeffLp_def] using h n π hπ v w
  have hmem : f ∈ (representativeLpSubmodule 𝕜 G)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨a, ha, rfl⟩ := mem_representativeLpSubmodule_iff.1 hu
    simpa only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply] using hle ha
  rw [orthogonal_representativeLpSubmodule_eq_bot] at hmem
  exact hmem

end CompactGroup

end TauCeti
