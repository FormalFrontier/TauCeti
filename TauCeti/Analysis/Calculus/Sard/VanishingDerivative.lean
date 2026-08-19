/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.FlatStratum
public import TauCeti.Analysis.Calculus.Sard.IntermediateStratum
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.LocallyNull

/-!
# Sard's theorem on the locus where the derivative vanishes

This file proves that a sufficiently smooth map between finite-dimensional real normed spaces
sends the set of points at which its Fréchet derivative vanishes to a set of additive Haar measure
zero, with no restriction on the two dimensions. Since a linear map onto a one-dimensional space
is surjective exactly when it is nonzero, this is the full Morse--Sard theorem whenever the target
is one-dimensional: the critical values of a smooth real-valued function on a finite-dimensional
real normed space form a null set, and its regular values are dense.

The proof is Morse's stratification argument, run by induction on the dimension of the source and
assembling the two estimates already available. Write `Σ_i` for the set of points at which the
iterated derivatives of order `1 ≤ j ≤ i` all vanish, and stratify `Σ_1` as
`Σ_1 = Σ_K ∪ ⋃_{i < K} (Σ_i \ Σ_{i+1})` for a depth `K` large enough that
`finrank ℝ E < (K + 1) * finrank ℝ F`.

* On the innermost stratum `Σ_K`, `TauCeti.addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero`
  applies directly: enough derivatives vanish for the Hölder estimate to force nullity.
* Near a point of `Σ_i \ Σ_{i+1}`,
  `TauCeti.exists_parametrization_iteratedFDeriv_eq_zero` carries `Σ_i` by a `C^r` map `θ` out of
  a space of dimension `finrank ℝ E - 1`. Every point of `Σ_1` in the image is a point where
  `f ∘ θ` has vanishing derivative, by the chain rule, so the inductive hypothesis in dimension
  `finrank ℝ E - 1` applies to `f ∘ θ` and returns the local nullity of the image.

Both steps are local, and second countability of the source turns local nullity into global
nullity through `TauCeti.measure_image_null_of_locally_null`.

Each descent step costs derivatives, since the parametrization `θ` is only as smooth as the
implicit function theorem makes it; the regularity `finrank ℝ E * finrank ℝ E + 1` recorded below
is a convenient sufficient bound rather than the sharp one. Morse--Sard holds already for `C^k`
maps with `k ≥ max 1 (finrank ℝ E - finrank ℝ F + 1)`; recovering that sharp exponent needs a
more careful induction than the one run here, and smooth maps satisfy every bound in sight.

What is still missing for the general Morse--Sard theorem is the outermost stratum, the set of
critical points at which the derivative is nonzero but not surjective; Milnor handles it by a
Fubini argument on a local fibration of the source. Combined with
`TauCeti.Differentiable.addHaar_image_criticalPoints_eq_zero` (equal dimensions) and
`TauCeti.Differentiable.addHaar_image_not_surjective_fderiv_eq_zero_of_finrank_lt_finrank`
(smaller source), Morse--Sard is now available whenever `finrank ℝ E ≤ finrank ℝ F`, and, in any
source dimension, whenever `finrank ℝ F = 1`.

This is Lane F0 of the analytic Heegaard Floer roadmap, where finite-dimensional Sard is the
prerequisite for Sard--Smale and hence for every transversality argument downstream.

## Main results

* `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`: the image of a set of points at which the
  derivative vanishes is null, for a map that is `C^k` at those points with `k` large enough.
* `TauCeti.ContDiff.addHaar_image_setOf_fderiv_eq_zero`: its global form for a smooth map.
* `TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero_of_finrank_eq_one`: **Morse--Sard for a
  one-dimensional target**, with
  `TauCeti.ContDiff.dense_compl_image_criticalPoints_of_finrank_eq_one` the density of the regular
  values.

## References

The stratification is the proof of Sard's theorem in J. Milnor, *Topology from the Differentiable
Viewpoint*, Section 3, and M. Hirsch, *Differential Topology*, Chapter 3.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

open scoped ContDiff Topology

namespace TauCeti

universe u

section Sard

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [Nontrivial F] (ν : Measure F) [IsAddHaarMeasure ν]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → F} {s : Set E} {k : ℕ}

/-- A finite smoothness exponent is not `∞`, the side condition of `ContDiffAt.contDiffOn`. -/
private theorem natCast_ne_infty (m : ℕ) : (m : ℕ∞ω) ≠ ∞ := by simp

/-- The induction behind `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`, on the dimension `n`
of the source. The source is quantified inside the statement because the induction step replaces
it by the kernel of a linear functional, a space of dimension one less. -/
private theorem addHaar_image_eq_zero_of_fderiv_eq_zero_aux (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E ≤ n → ∀ (k : ℕ), n * n + 1 ≤ k → ∀ (f : E → F) (s : Set E),
        (∀ x ∈ s, ContDiffAt ℝ k f x) → (∀ x ∈ s, fderiv ℝ f x = 0) → ν (f '' s) = 0 := by
  induction n with
  | zero =>
    intro E _ _ _ hE k _ f s _ _
    have : Subsingleton E := Module.finrank_zero_iff.mp (Nat.le_zero.mp hE)
    exact (Set.Subsingleton.image (fun x _ y _ ↦ Subsingleton.elim x y) f).measure_zero ν
  | succ n ih =>
    intro E _ _ _ hE k hk f s hf hs
    have hF : 0 < finrank ℝ F := finrank_pos
    have hkK : n + 2 ≤ k := by nlinarith
    -- Split `s` into the innermost stratum, where the derivatives of order `1 ≤ i ≤ n + 1` all
    -- vanish, and the strata where the vanishing stops at some order `i < n + 1`.
    have hsub : s ⊆ {x ∈ s | ∀ i, 1 ≤ i → i ≤ n + 1 → iteratedFDeriv ℝ i f x = 0} ∪
        ⋃ i ∈ Set.Ico 1 (n + 1),
          {x ∈ s | iteratedFDeriv ℝ i f x = 0 ∧ iteratedFDeriv ℝ (i + 1) f x ≠ 0} := by
      intro x hx
      by_cases hflat : ∀ i, 1 ≤ i → i ≤ n + 1 → iteratedFDeriv ℝ i f x = 0
      · exact Or.inl ⟨hx, hflat⟩
      refine Or.inr ?_
      push Not at hflat
      obtain ⟨i, hi1, hin, hine⟩ := hflat
      have h1 : iteratedFDeriv ℝ 1 f x = 0 := by
        ext m
        simp [iteratedFDeriv_one_apply, hs x hx]
      -- Descend from a nonvanishing derivative to the last order at which the derivatives vanish.
      have key : ∀ j : ℕ, j + 1 ≤ n + 1 → iteratedFDeriv ℝ (j + 1) f x ≠ 0 →
          ∃ i ∈ Set.Ico 1 (n + 1), x ∈
            {x | x ∈ s ∧ iteratedFDeriv ℝ i f x = 0 ∧ iteratedFDeriv ℝ (i + 1) f x ≠ 0} := by
        intro j
        induction j with
        | zero => exact fun _ hne ↦ absurd h1 hne
        | succ j ihj =>
          intro hjn hjne
          by_cases hj : iteratedFDeriv ℝ (j + 1) f x = 0
          · exact ⟨j + 1, ⟨Nat.le_add_left 1 j, by omega⟩, hx, hj, hjne⟩
          · exact ihj (by omega) hj
      obtain ⟨i', hi', hxB⟩ := key (i - 1) (by omega) (by rwa [Nat.sub_add_cancel hi1])
      exact mem_biUnion hi' hxB
    refine measure_mono_null (image_mono hsub) ?_
    rw [image_union, image_iUnion₂]
    refine measure_union_null ?_ ((measure_biUnion_null_iff (Set.to_countable _)).2 fun i hi ↦ ?_)
    · -- The innermost stratum: enough derivatives vanish for the flat-stratum estimate.
      refine measure_image_null_of_locally_null fun a ha ↦ ?_
      obtain ⟨u, hu, hfu⟩ := (hf a ha.1).contDiffOn (m := ((n + 1 + 1 : ℕ) : ℕ∞ω))
        (mod_cast hkK) fun h ↦ absurd h (natCast_ne_infty _)
      have humem : interior u ∈ 𝓝 a := isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hu)
      refine ⟨_ ∩ interior u, inter_mem_nhdsWithin _ humem, ?_⟩
      refine addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero (k := n + 1) ν isOpen_interior
        (hfu.mono interior_subset) inter_subset_right (fun x hx ↦ hx.1.2) ?_
      calc finrank ℝ E ≤ n + 1 := hE
        _ < n + 2 := by omega
        _ ≤ (n + 1 + 1) * finrank ℝ F := Nat.le_mul_of_pos_right _ hF
    · -- An intermediate stratum: descend to the kernel of a linear functional.
      refine measure_image_null_of_locally_null fun a ha ↦ ?_
      obtain ⟨has, hai, hai1⟩ := ha
      have hfa : ContDiffAt ℝ ((n * n + 1 + i : ℕ)) f a :=
        (hf a has).of_le (mod_cast show n * n + 1 + i ≤ k by have := hi.2; nlinarith)
      obtain ⟨g, g', θ, -, -, -, -, -, hθ, -, hcover, hrank⟩ :=
        exists_parametrization_iteratedFDeriv_eq_zero (r := n * n + 1) hfa (by positivity) hai hai1
      obtain ⟨w, hw, hθw⟩ := hθ.contDiffOn (m := ((n * n + 1 : ℕ) : ℕ∞ω)) le_rfl
        fun h ↦ absurd h (natCast_ne_infty _)
      have hwmem : interior w ∈ 𝓝 (0 : ↥g'.ker) :=
        isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hw)
      -- Every point of the stratum close to `a` is `θ z` for some `z` where `θ` is `C^r`.
      refine ⟨_ ∩ {x | iteratedFDeriv ℝ i f x = 0 → x ∈ θ '' interior w},
        inter_mem_nhdsWithin _ (hcover _ hwmem), ?_⟩
      have hθz : ∀ z ∈ interior w, ContDiffAt ℝ ((n * n + 1 : ℕ)) θ z := fun z hz ↦
        (hθw.mono interior_subset).contDiffAt (isOpen_interior.mem_nhds hz)
      refine measure_mono_null (fun y hy ↦ ?_)
        (ih ↥g'.ker (by omega) (n * n + 1) le_rfl (f ∘ θ) (interior w ∩ θ ⁻¹' s) ?_ ?_)
      · obtain ⟨x, ⟨⟨hxs, hxi, -⟩, hxV⟩, rfl⟩ := hy
        obtain ⟨z, hz, rfl⟩ := hxV hxi
        exact ⟨z, ⟨hz, hxs⟩, rfl⟩
      · rintro z ⟨hzw, hzs⟩
        exact ((hf (θ z) hzs).of_le (mod_cast show n * n + 1 ≤ k by nlinarith)).comp z (hθz z hzw)
      · rintro z ⟨hzw, hzs⟩
        have hone : (1 : ℕ∞ω) ≤ ((n * n + 1 : ℕ) : ℕ∞ω) := mod_cast Nat.le_add_left 1 (n * n)
        have hfz : DifferentiableAt ℝ f (θ z) :=
          ((hf (θ z) hzs).of_le (mod_cast show 1 ≤ k by nlinarith)).differentiableAt_one
        rw [fderiv_comp z hfz ((hθz z hzw).of_le hone).differentiableAt_one, hs (θ z) hzs,
          ContinuousLinearMap.zero_comp]

/-- **Sard's theorem on the locus where the derivative vanishes.** Let `f` be a map between
finite-dimensional real normed spaces with nontrivial target, and let `s` be a set at each point
of which `f` is `C^k` and the Fréchet derivative of `f` vanishes. If
`finrank ℝ E * finrank ℝ E + 1 ≤ k`, then `f '' s` has additive Haar measure zero.

There is no restriction on the two dimensions: the vanishing of the derivative, rather than a
dimension count, is what the higher derivatives are used against. The bound on `k` is a
sufficient one, not the sharp exponent of the Morse--Sard theorem. -/
theorem addHaar_image_eq_zero_of_fderiv_eq_zero (hk : finrank ℝ E * finrank ℝ E + 1 ≤ k)
    (hf : ∀ x ∈ s, ContDiffAt ℝ k f x) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) : ν (f '' s) = 0 :=
  addHaar_image_eq_zero_of_fderiv_eq_zero_aux ν (finrank ℝ E) E le_rfl k hk f s hf hs

/-- The image under a smooth map of the whole locus where its Fréchet derivative vanishes has
additive Haar measure zero, whatever the two finite dimensions. -/
theorem ContDiff.addHaar_image_setOf_fderiv_eq_zero (hf : ContDiff ℝ ∞ f) :
    ν (f '' {x | fderiv ℝ f x = 0}) = 0 :=
  addHaar_image_eq_zero_of_fderiv_eq_zero ν le_rfl
    (fun _ _ ↦ (contDiff_infty.mp hf _).contDiffAt) fun _ hx ↦ hx

/-- The complement of the image of the locus where the derivative of a smooth map vanishes is
dense. -/
theorem ContDiff.dense_compl_image_setOf_fderiv_eq_zero (hf : ContDiff ℝ ∞ f) :
    Dense (f '' {x | fderiv ℝ f x = 0})ᶜ := by
  let t : Set F := f '' {x | fderiv ℝ f x = 0}
  have ht : (addHaar : Measure F) t = 0 :=
    ContDiff.addHaar_image_setOf_fderiv_eq_zero (ν := addHaar) hf
  have htc : ∀ᵐ x ∂(addHaar : Measure F), x ∈ tᶜ := ae_iff.mpr (by simpa using ht)
  simpa only [ofPred_mem_eq, t] using Measure.dense_of_ae htc

section OneDimensional

variable (hF : finrank ℝ F = 1)

include hF

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
  [FiniteDimensional ℝ E] in
/-- A linear map into a one-dimensional space is surjective exactly when it is nonzero, so the
critical points of a map into such a space are the points where its derivative vanishes. -/
theorem setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero :
    {x | ¬ Surjective (fderiv ℝ f x)} = {x | fderiv ℝ f x = 0} := by
  let _ : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  ext x
  simp only [mem_ofPred_eq, not_iff_comm]
  constructor
  · intro hx
    exact surjective_of_nonzero_of_finrank_eq_one (f := (fderiv ℝ f x : E →ₗ[ℝ] F)) hF
      fun hzero ↦ hx (ContinuousLinearMap.coe_injective hzero)
  · rintro hsurj h
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    obtain ⟨v, hv⟩ := hsurj y
    rw [h] at hv
    exact hy (by simpa using hv.symm)

omit [Nontrivial F] in
/-- **Morse--Sard for a one-dimensional target.** The critical values of a smooth map from a
finite-dimensional real normed space to a one-dimensional one, that is the values it takes at the
points where its derivative is not surjective, form a set of additive Haar measure zero. -/
theorem ContDiff.addHaar_image_criticalPoints_eq_zero_of_finrank_eq_one (hf : ContDiff ℝ ∞ f) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  let _ : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  rw [setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero hF]
  exact ContDiff.addHaar_image_setOf_fderiv_eq_zero ν hf

omit [Nontrivial F] in
/-- The regular values of a smooth map from a finite-dimensional real normed space to a
one-dimensional one are dense. -/
theorem ContDiff.dense_compl_image_criticalPoints_of_finrank_eq_one (hf : ContDiff ℝ ∞ f) :
    Dense (f '' {x | ¬ Surjective (fderiv ℝ f x)})ᶜ := by
  let _ : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  rw [setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero hF]
  exact ContDiff.dense_compl_image_setOf_fderiv_eq_zero hf

end OneDimensional

end Sard

end TauCeti

end
