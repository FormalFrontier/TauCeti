/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Analysis.Calculus.Hadamard

/-!
# Tangent vectors as point derivations

A tangent vector acts on smooth scalar-valued functions by directional differentiation. This gives
a canonical linear map from the ordinary tangent space to the algebraic point derivations.

## Main results

* `tangentToPointDerivation`: the point derivation associated to a tangent vector.
* `tangentToPointDerivation_injective`: distinct tangent vectors induce distinct point derivations
  on finite-dimensional Hausdorff real manifolds.
* `tangentToPointDerivation_surjective`: at an interior point of a finite-dimensional Hausdorff
  real manifold, every point derivation comes from a tangent vector.
* `pointDerivationEquivTangentSpace`: the resulting canonical linear equivalence.
* `PointDerivation.congr_of_eventuallyEq`: on a finite-dimensional Hausdorff real manifold, a point
  derivation depends only on the germ of a smooth function at its basepoint.
* `tangentToPointDerivation_mfderiv`: this association commutes with differentials.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
-/

public section

open scoped ContDiff Derivation Manifold Topology

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A tangent vector acts on smooth functions by directional differentiation. -/
-- Exposure is required for the exported characteristic equation below to unfold this definition
-- under the module system.
@[expose]
def tangentToPointDerivation (x : M) : TangentSpace I x →ₗ[𝕜] PointDerivation I x where
  toFun v :=
    Derivation.mk'
      { toFun := fun f => mvfderiv I f x v
        map_add' := fun f g => by
          -- Unfold the pointed smooth-map addition wrapper: `ContMDiffMap.coe_add` does not match
          -- this type synonym directly.
          change mvfderiv I (⇑f + ⇑g) x v = _
          exact congr($(mvfderiv_add
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
            (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
        map_smul' := fun c f => by
          have hc : MDiffAt (fun _ : M => c) x := mdifferentiableAt_const
          -- Unfold the pointed smooth-map scalar wrapper: `ContMDiffMap.coe_smul` does not match
          -- this type synonym directly.
          change mvfderiv I ((fun _ : M => c) • ⇑f) x v = c • mvfderiv I f x v
          have h := congr($(mvfderiv_smul hc
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
          calc
            _ = (c • mvfderiv I f x +
                (mvfderiv I (fun _ : M => c) x).smulRight (f x)) v := h
            _ = _ := by simp [mvfderiv_const] }
      fun f g => by
        -- Unfold the pointed smooth-map multiplication wrapper and the evaluation scalar action
        -- (`PointedContMDiffMap.smul_def`): the corresponding `ContMDiffMap.coe_mul` theorem does
        -- not match this type synonym directly.
        change mvfderiv I (⇑f * ⇑g) x v =
          f x * mvfderiv I g x v + g x * mvfderiv I f x v
        exact congr($(mvfderiv_mul
          (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
          (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
  map_add' v w := by
    ext f
    -- Unfold the two bundled linear maps to expose linearity of `mvfderiv` in its tangent vector.
    change mvfderiv I f x (v + w) = _
    exact (mvfderiv I f x).map_add v w
  map_smul' c v := by
    ext f
    -- Unfold the two bundled linear maps to expose scalar linearity of `mvfderiv`.
    change mvfderiv I f x (c • v) = _
    exact (mvfderiv I f x).map_smul c v

/-- The point derivation associated to a tangent vector evaluates a smooth function by its
directional derivative. -/
@[simp]
theorem tangentToPointDerivation_apply (x : M) (v : TangentSpace I x)
    (f : C^∞⟮I, M; 𝕜⟯) : tangentToPointDerivation x v f = mvfderiv I f x v :=
  rfl

/-- **A globally smooth map with the germ of the extended chart.** There is a `C^∞` map `M → E`
that agrees with `extChartAt I x` on a neighbourhood of `x`. -/
private theorem exists_contMDiffMap_eventuallyEq_extChartAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] (x : M) :
    ∃ F : C^∞⟮I, M; modelWithCornersSelf ℝ E, E⟯,
      Filter.EventuallyEq (nhds x) (F : M → E) (extChartAt I x) := by
  -- Multiplying the chart by a bump function at `x` leaves its germ there and makes the product
  -- smooth everywhere.
  let b : SmoothBumpFunction I x := Classical.choice inferInstance
  refine ⟨⟨fun y ↦ b y • extChartAt I x y, b.contMDiff_smul contMDiffOn_extChartAt⟩, ?_⟩
  filter_upwards [b.eventuallyEq_one] with y hy
  simp [hy]

/-- On a finite-dimensional Hausdorff real manifold, smooth scalar-valued functions distinguish
tangent vectors. -/
theorem tangentToPointDerivation_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (x : M) :
    Function.Injective (tangentToPointDerivation (I := I) x) := by
  intro v w hvw
  -- The tangent-space type synonym carries no normed-space instance of its own, so expose the
  -- model space before applying the separating-dual theorem.
  change E at v w
  change v = w
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  let f : C^∞⟮I, M; ℝ⟯ := ⟨fun y ↦ φ (F y), φ.contMDiff.comp F.contMDiff⟩
  have hlocal : (f : M → ℝ) =ᶠ[𝓝 x] φ ∘ extChartAt I x := hF.fun_comp φ
  have hfv : mvfderiv I f x v = mvfderiv I f x w := by
    have h := congrArg (fun D ↦ D f) hvw
    -- Unbundle the comparison map after evaluating the two point derivations at `f`.
    change mvfderiv I f x v = mvfderiv I f x w at h
    exact h
  have hderiv (u : TangentSpace I x) : mvfderiv I f x u = φ u := by
    have hφ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ (extChartAt I x x) = φ :=
      φ.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [mvfderiv, hlocal.mfderiv_eq,
      mfderiv_comp x φ.mdifferentiableAt
        (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H x)),
      hφ, mfderiv_extChartAt_self]
    -- Unwrap the tangent-space synonym and apply the resulting identity linear map; there is no
    -- separate simplification lemma for this final coercion boundary.
    change φ u = φ u
    rfl
  -- The separating-dual goal is stated on the model space after the tangent-space synonym was
  -- exposed above, so return to the corresponding scalar equality before using `hderiv`.
  change φ v = φ w
  rw [← hderiv v, ← hderiv w]
  exact hfv

/-- **Hadamard's lemma in coordinates.** Subtracting its value at `x` writes a smooth real
function as a combination of the coordinate functions of any finitely-indexed basis, each taken
relative to its own value at `x`, with smooth coefficients. At the base point those coefficients
are the directional derivatives along the basis. -/
private theorem exists_contMDiffMap_hadamard_coords {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (f : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) (x : E) (b : Module.Basis ι ℝ E) :
    ∃ a : ι → C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      (∀ i, a i x = fderiv ℝ f x (b i)) ∧
        ∀ y, f y - f x = ∑ i, a i y * (b.coord i y - b.coord i x) := by
  refine ⟨fun i ↦ ⟨fun y ↦ hadamardFactor f x y (b i), ?_⟩, fun i ↦ ?_, ?_⟩
  · have hfac : ContDiff ℝ ∞ (hadamardFactor f x) :=
      f.contMDiff.contDiff.contDiff_hadamardFactor f x
    -- Applying a smooth continuous-linear-map-valued function to the constant vector `b i`
    -- is the available API for smoothness of each scalar Hadamard factor.
    exact (hfac.clm_apply (show ContDiff ℝ ∞ (fun _ : E ↦ b i) from contDiff_const)).contMDiff
  · simp
  · intro y
    calc
      f y - f x = hadamardFactor f x y (y - x) :=
        (f.contMDiff.contDiff.of_le (by norm_num)).sub_eq_hadamardFactor_apply f x y
      _ = ∑ i, hadamardFactor f x y (b i) * (b.coord i y - b.coord i x) := by
        rw [← b.sum_repr (y - x), map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        simp [mul_comm]

/-- **Hadamard's identity in the algebra of smooth functions.** A pointwise factorization of
`g - g x` through the functions `c i`, with coefficients `a i`, is an identity between the bundled
smooth maps themselves, the constants appearing as the images of `algebraMap`.

This is the pointwise-to-bundled transport: the hypothesis speaks of values, the conclusion of
elements of `C^∞⟮…⟯`, and the two are related by evaluation being a ring homomorphism. -/
private theorem sub_algebraMap_eq_sum_mul_sub_algebraMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} [Fintype ι] (x : E)
    (g : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯)
    (a c : ι → C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯)
    (h : ∀ y, g y - g x = ∑ i, a i y * (c i y - c i x)) :
    g - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (g x) =
      ∑ i, a i * (c i - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (c i x)) := by
  ext y
  calc
    (g - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (g x)) y = g y - g x := rfl
    _ = ∑ i, a i y * (c i y - c i x) := h y
    _ = _ := by
      -- Evaluation of bundled smooth maps is a ring homomorphism, but the pointwise coercion on
      -- the left does not expose that homomorphism to `rw` automatically.
      change _ = ContMDiffMap.evalRingHom y _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ rfl

/-- The constant smooth map `algebraMap ℝ C^∞⟮…⟯ s` takes the value `s` at every point.

The algebra structure on smooth maps is pointwise, so this holds by unfolding; stating it gives
that normalization a name, so the proofs below need not rely on it silently. -/
private theorem algebraMap_contMDiffMap_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : ℝ) (y : E) :
    (algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ s) y = s :=
  rfl

/-- **Subtracting its value at the base point does not change a derivation**, since the constant
subtracted off is annihilated by `D`. -/
private theorem derivation_sub_algebraMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x : E}
    (D : PointDerivation (modelWithCornersSelf ℝ E) x)
    (q : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) :
    D (q - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (q x)) = D q := by
  -- `D`'s domain is a type synonym for `C^∞⟮…⟯`, so a difference formed in the unpointed type
  -- does not match `map_sub`/`map_algebraMap` as stated. These restatements supply the form `rw`
  -- needs, each holding by definitional unfolding alone; isolating them here keeps that
  -- bookkeeping out of every consumer.
  have hsub (u w : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) : D (u - w) = D u - D w :=
    D.map_sub _ _
  have hconst (s : ℝ) :
      D (algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ s) = 0 :=
    D.map_algebraMap s
  rw [hsub, hconst, sub_zero]

/-- **The Leibniz rule collapses once the second factor vanishes at the base point.** Subtracting
`q x` from `q` makes that factor vanish at `x`, and the Leibniz scalar action is evaluation at `x`,
so the `D p` term drops out. What survives is `D q`, weighted by `p x` — the subtracted constant
itself contributing nothing, being annihilated by `D`. -/
private theorem derivation_mul_sub_algebraMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x : E}
    (D : PointDerivation (modelWithCornersSelf ℝ E) x)
    (p q : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) :
    D (p * (q - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (q x))) = p x * D q := by
  set r : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ :=
    q - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (q x) with hr
  have hleibniz := D.leibniz p r
  -- Unfold pointed-map evaluation in the Leibniz identity. The scalar action there is
  -- evaluation at `x`, which is definitionally the displayed multiplication.
  change D (p * r) = p x * D r + r x * D p at hleibniz
  have hrx : r x = 0 := by
    rw [hr]
    simp [algebraMap_contMDiffMap_apply]
  rw [hleibniz, hrx, hr, derivation_sub_algebraMap, zero_mul, add_zero]

private theorem tangentToPointDerivation_surjective_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (x : E) :
    Function.Surjective
      (tangentToPointDerivation (I := modelWithCornersSelf ℝ E) x) := by
  intro D
  -- Read `D` on a finite coordinate system and use those values as the coordinates of the
  -- candidate tangent vector.
  let b := Module.finBasis ℝ E
  let c (i : Fin (Module.finrank ℝ E)) : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ :=
    ⟨b.coord i, (b.coord i).toContinuousLinearMap.contDiff.contMDiff⟩
  -- `PointedContMDiffMap` is a type synonym for `C^∞⟮…⟯`, so `D` applies to an ordinary smooth
  -- map directly and no pointed-map wrapper is needed.
  let v : TangentSpace (modelWithCornersSelf ℝ E) x := ∑ i, D (c i) • b i
  refine ⟨v, ?_⟩
  ext f
  let f' : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ := ⟨f, f.contMDiff⟩
  -- The domain of `D` and `TangentSpace` are pointed-map and model-space type synonyms. Unfold
  -- their evaluation here so the rest of the argument can stay in the ordinary smooth-map API.
  change mvfderiv (modelWithCornersSelf ℝ E) f' x v = D f'
  rw [mvfderiv, mfderiv_eq_fderiv]
  -- Hadamard's lemma factors `f - f(x)` through the coordinate functions, with smooth factors,
  -- so this identity lives in the algebra on which the derivation acts.
  obtain ⟨a, hax, ha⟩ := exists_contMDiffMap_hadamard_coords f' x b
  have hfactor := sub_algebraMap_eq_sum_mul_sub_algebraMap x f' a c ha
  -- `D`'s domain is a type synonym for `C^∞⟮…⟯`, so the sum below lives *syntactically* in the
  -- unpointed type and `rw` cannot use `map_sum` as stated; this restatement supplies the
  -- matching form, and holds by definitional unfolding alone.
  have hsum (q : Fin (Module.finrank ℝ E) → C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) :
      D (∑ i, q i) = ∑ i, D (q i) :=
    map_sum D _ _
  calc
    fderiv ℝ f' x v = ∑ i, fderiv ℝ f' x (b i) * D (c i) := by
      -- Unfold the chosen vector `v` across the tangent-space synonym before using linearity.
      change fderiv ℝ f' x (∑ i, D (c i) • b i) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp [smul_eq_mul, mul_comm]
    _ = D (∑ i, a i * (c i - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (c i x))) := by
      rw [hsum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [derivation_mul_sub_algebraMap, hax]
    _ = D (f' - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (f' x)) :=
      congrArg D hfactor.symm
    _ = D f' := derivation_sub_algebraMap D f'

namespace PointDerivation

/-- A point derivation on a finite-dimensional Hausdorff real manifold depends only on the germ of
a smooth function at its basepoint. -/
theorem congr_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {x : M} (v : PointDerivation I x) (f g : C^∞⟮I, M; ℝ⟯)
    (hfg : (f : M → ℝ) =ᶠ[𝓝 x] g) :
    v f = v g := by
  have hs : {y | f y = g y} ∈ 𝓝 x := hfg
  obtain ⟨b, -, hb⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.mp hs
  let b' : C^∞⟮I, M; ℝ⟯ := ⟨b, b.contMDiff⟩
  have hprod : b' * (f - g) = 0 := by
    ext y
    -- Unbundle pointwise multiplication and subtraction of smooth maps.
    change b y * (f y - g y) = 0
    by_cases hy : b y = 0
    · simp [hy]
    · have hyb : y ∈ Function.support b := hy
      have hyeq : f y = g y := hb hyb
      simp [hyeq]
  have hx : f x = g x := hfg.eq_of_nhds
  have hleibniz := v.leibniz b' (f - g)
  -- Reinterpret the global smooth-map equality in the pointed type synonym used by `v`.
  have hprodAt : (b' * (f - g) : C^∞⟮I, M; ℝ⟯⟨x⟩) = 0 := hprod
  have hzero : v (b' * (f - g) : C^∞⟮I, M; ℝ⟯⟨x⟩) = 0 := by
    calc
      _ = v 0 := congrArg v hprodAt
      _ = 0 := v.map_zero
  have heq := hzero.symm.trans hleibniz
  -- Unfold the pointed scalar action as evaluation at `x` before simplifying the Leibniz rule.
  change 0 = b x * v (f - g) + (f x - g x) * v b' at heq
  simp [hx] at heq
  have hsub : v (f - g : C^∞⟮I, M; ℝ⟯⟨x⟩) = v f - v g := v.map_sub f g
  exact sub_eq_zero.mp (heq.trans hsub).symm

end PointDerivation

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- Sending tangent vectors to point derivations commutes with the differential of a smooth map. -/
theorem tangentToPointDerivation_mfderiv (f : C^∞⟮I, M; I', M'⟯) (x : M)
    (v : TangentSpace I x) :
    tangentToPointDerivation (f x) (mfderiv I I' f x v) =
      𝒅 f x (tangentToPointDerivation x v) := by
  ext g
  -- Unfold the derivation differential and both comparison-map applications before using the
  -- manifold chain rule; their bundled coercions have no separate rewriting lemma.
  change mvfderiv I' g (f x) (mfderiv I I' f x v) =
    tangentToPointDerivation x v (g.comp f)
  rw [tangentToPointDerivation_apply]
  exact (mfderiv_comp_apply x
    (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt v).symm

/-- **A smooth function factors through the chart near an interior point.** If `F` has the germ of
the extended chart at an interior point `x`, then every `f : C^∞⟮I, M; ℝ⟯` agrees near `x` with
`g' ∘ F` for some `C^∞` function `g'` on the model space. -/
private theorem exists_contMDiffMap_comp_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x : M} (hx : I.IsInteriorPoint x) (F : C^∞⟮I, M; modelWithCornersSelf ℝ E, E⟯)
    (hF : Filter.EventuallyEq (nhds x) (F : M → E) (extChartAt I x))
    (f : C^∞⟮I, M; ℝ⟯) :
    ∃ g' : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      Filter.EventuallyEq (nhds x) (f : M → ℝ) (g' ∘ F) := by
  -- Cut the chart expression of `f` off inside the interior of the chart target.
  have hFx : F x = extChartAt I x x := hF.eq_of_nhds
  have htarget : interior (extChartAt I x).target ∈ nhds (F x) := by
    rw [hFx]
    exact isOpen_interior.mem_nhds
      ((ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx)
  obtain ⟨β, hβ, -⟩ :=
    (SmoothBumpFunction.nhds_basis_support
      (I := modelWithCornersSelf ℝ E) htarget).mem_iff.mp htarget
  let g : E → ℝ := fun y ↦ β y * f ((extChartAt I x).symm y)
  have hg : ContDiff ℝ ∞ g := by
    apply ContMDiff.contDiff
    refine contMDiff_of_tsupport fun y hy ↦ ?_
    have hytarget : y ∈ interior (extChartAt I x).target :=
      hβ (tsupport_mul_subset_left hy)
    have hsymmWithin :=
      contMDiffWithinAt_extChartAt_symm_target (n := ∞) x (interior_subset hytarget)
    have hsymm := hsymmWithin.contMDiffAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hytarget) interior_subset)
    exact β.contMDiffAt.mul (f.contMDiff.contMDiffAt.comp y hsymm)
  refine ⟨⟨g, hg.contMDiff⟩, ?_⟩
  have hβF : Filter.EventuallyEq (nhds x) (β ∘ F) (fun _ ↦ 1) :=
    β.eventuallyEq_one.comp_tendsto F.contMDiff.continuous.continuousAt
  have hsource : ∀ᶠ y in nhds x, y ∈ (extChartAt I x).source :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  filter_upwards [hF, hβF, hsource] with y hFy hβy hy
  -- Unfold composition and the bundled chart-local function; no theorem rewrites through both
  -- bundled-map coercions at once.
  change f y = β (F y) * f ((extChartAt I x).symm (F y))
  -- Likewise expose the constant function in the eventual equality supplied by the bump.
  change β (F y) = 1 at hβy
  rw [hβy, one_mul, hFy, (extChartAt I x).left_inv hy]

/-- Every point derivation at an interior point of a finite-dimensional Hausdorff real manifold is
directional differentiation along a tangent vector. -/
theorem tangentToPointDerivation_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] (x : M) (hx : I.IsInteriorPoint x) :
    Function.Surjective (tangentToPointDerivation (I := I) x) := by
  intro D
  -- A bump-localized extended chart is globally smooth and agrees with the chart germ at `x`.
  -- Push `D` through it and apply the model-space theorem to obtain the candidate vector `v`.
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  obtain ⟨w, hw⟩ := tangentToPointDerivation_surjective_model (F x) (fdifferential F x D)
  let v : TangentSpace I x := w
  have hv : mfderiv I (modelWithCornersSelf ℝ E) F x v = w := by
    rw [hF.mfderiv_eq, mfderiv_extChartAt_self]
    -- `TangentSpace I x` is the model space as a type synonym, so the identity derivative applies
    -- to `v` definitionally as the model-space vector `w`.
    rfl
  refine ⟨v, ?_⟩
  ext f
  -- To compare the two derivations on an arbitrary global `f`, replace it near `x` by a smooth
  -- function of the chart.
  obtain ⟨g', hlocal⟩ := exists_contMDiffMap_comp_eventuallyEq hx F hF f
  -- Germ invariance replaces `f` by `g' ∘ F` on both sides. Naturality of the tangent comparison
  -- then reduces the result exactly to the model-space equality `hw`.
  rw [(tangentToPointDerivation x v).congr_of_eventuallyEq f (g'.comp F) hlocal,
    D.congr_of_eventuallyEq f (g'.comp F) hlocal]
  have hpush : fdifferential F x (tangentToPointDerivation x v) =
      tangentToPointDerivation (F x) w := by
    rw [← tangentToPointDerivation_mfderiv F x v, hv]
  exact congrArg (fun d : PointDerivation (modelWithCornersSelf ℝ E) (F x) ↦ d g')
    (hpush.trans hw)

/-- Point derivations and tangent vectors are canonically linearly equivalent at an interior point
of a finite-dimensional Hausdorff real manifold. -/
noncomputable def pointDerivationEquivTangentSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] (x : M) (hx : I.IsInteriorPoint x) :
    PointDerivation I x ≃ₗ[ℝ] TangentSpace I x :=
  (LinearEquiv.ofBijective (tangentToPointDerivation x)
    ⟨tangentToPointDerivation_injective x, tangentToPointDerivation_surjective x hx⟩).symm

/-- The inverse of the point-derivation equivalence is directional differentiation. -/
@[simp]
theorem pointDerivationEquivTangentSpace_symm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] (x : M) (hx : I.IsInteriorPoint x) (v : TangentSpace I x) :
    (pointDerivationEquivTangentSpace x hx).symm v = tangentToPointDerivation x v := by
  simpa only [pointDerivationEquivTangentSpace, LinearEquiv.symm_symm] using
    (LinearEquiv.ofBijective_apply (tangentToPointDerivation x) v)

/-- Converting a point derivation to a tangent vector and back recovers the derivation. -/
@[simp]
theorem tangentToPointDerivation_pointDerivationEquivTangentSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] (x : M) (hx : I.IsInteriorPoint x) (D : PointDerivation I x) :
    tangentToPointDerivation x (pointDerivationEquivTangentSpace x hx D) = D := by
  rw [← pointDerivationEquivTangentSpace_symm_apply x hx]
  exact (pointDerivationEquivTangentSpace x hx).symm_apply_apply D

/-- Converting a tangent vector to a point derivation and back recovers the vector. -/
@[simp]
theorem pointDerivationEquivTangentSpace_tangentToPointDerivation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] (x : M) (hx : I.IsInteriorPoint x) (v : TangentSpace I x) :
    pointDerivationEquivTangentSpace x hx (tangentToPointDerivation x v) = v := by
  rw [← pointDerivationEquivTangentSpace_symm_apply x hx]
  exact (pointDerivationEquivTangentSpace x hx).apply_symm_apply v

/-- The equivalence between point derivations and tangent vectors is natural under smooth maps. -/
@[simp]
theorem pointDerivationEquivTangentSpace_fdifferential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M'] [T2Space M']
    (f : C^∞⟮I, M; I', M'⟯) (x : M) (hx : I.IsInteriorPoint x)
    (hfx : I'.IsInteriorPoint (f x)) (D : PointDerivation I x) :
    pointDerivationEquivTangentSpace (f x) hfx (𝒅 f x D) =
      mfderiv I I' f x (pointDerivationEquivTangentSpace x hx D) := by
  apply tangentToPointDerivation_injective (I := I') (f x)
  rw [tangentToPointDerivation_pointDerivationEquivTangentSpace (f x) hfx,
    tangentToPointDerivation_mfderiv,
    tangentToPointDerivation_pointDerivationEquivTangentSpace x hx]
