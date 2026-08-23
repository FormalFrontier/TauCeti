/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.VanishingDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Analysis.Normed.Operator.Surjective
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.LocallyNull

/-!
# The outermost stratum, and the Morse--Sard theorem

The critical values of a sufficiently smooth map between finite-dimensional real normed spaces
form a set of additive Haar measure zero, and its regular values are therefore dense. A point is
critical when the Fréchet derivative there fails to be surjective.

The strata of the critical set are handled in the neighbouring files, and this one supplies the
outermost stratum, where the derivative is nonzero but not surjective, together with the assembly
of all the strata into the theorem itself. The two earlier slices,
`TauCeti.Differentiable.addHaar_image_criticalPoints_eq_zero` (equal dimensions),
`TauCeti.Differentiable.addHaar_image_not_surjective_fderiv_eq_zero_of_finrank_lt_finrank`
(smaller source), are both subsumed by the statement proved here, which needs no relation between
the two dimensions.

The argument for the outermost stratum is Milnor's. Near a point `a` where the derivative does not
vanish, pick `v₀` with `Df(a) v₀ ≠ 0` and a functional `φ` on the target with `φ (Df(a) v₀) = 1`.
Then `u := φ ∘ f` has a nonvanishing differential at `a`, so `x ↦ (u x, π x)` is a local
diffeomorphism onto `ℝ × ker (D u a)` for the projection `π` along `v₀`, and its local inverse `Θ`
parametrizes all the nearby level sets of `u` at once. Splitting the target as `ℝ × ker φ` too,
`f` becomes the map `(t, z) ↦ (t, G t z)` with `G t z := ρ (f (Θ (t, z)))`, where `ρ` projects the
target along `Df(a) v₀`: it preserves the level `t`, so it carries each hyperplane into a
hyperplane. Whenever a point is critical for `f`, it is critical for the restricted map `G t`,
whose source has one dimension less, so the induction hypothesis makes every slice of the image of
the critical set null, and Fubini finishes. Compactness enters only to make the slicing legitimate:
an image with null slices need not be null unless it is measurable, so the
argument runs over the pieces `crit f ∩ closedBall a r`. These are compact because
`TauCeti.isOpen_setOf_surjective` makes the surjective operators an open set, so the critical
locus, its preimage under the continuous derivative, is closed on the ball, and a closed subset of
a compact ball is compact.

The induction is on the dimension of the source, and both spaces are quantified inside the
statement carried through it, since the induction step replaces each of them by a
hyperplane. The regularity `finrank ℝ E * finrank ℝ E + 1` is inherited from
`TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero` and is a sufficient bound, not the sharp
exponent `max 1 (finrank ℝ E - finrank ℝ F + 1)` of the Morse--Sard theorem; no regularity is lost
in the descent, since the inverse function theorem returns a local inverse as smooth as the map.

## Main results

* `TauCeti.addHaar_image_criticalPoints_eq_zero`: the critical values taken on an open set form a
  null set.
* `TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero`: **the Morse--Sard theorem**, its global
  form.
* `TauCeti.ContDiff.dense_compl_image_criticalPoints`: the regular values are dense.

This is Lane F0 of the analytic Heegaard Floer roadmap, where finite-dimensional Sard is the
prerequisite for Sard--Smale and hence for every transversality argument downstream.

## References

The stratification and the Fubini step are the proof of Sard's theorem in J. Milnor, *Topology
from the Differentiable Viewpoint*, Section 3, and M. Hirsch, *Differential Topology*, Chapter 3.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

open scoped ContDiff Topology

namespace TauCeti

universe u v

section Surjective

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map into a trivial space has no critical points, every linear map into it being
surjective. -/
private theorem setOf_not_surjective_fderiv_eq_empty [Subsingleton F] (g : E → F) :
    {x | ¬ Surjective (fderiv ℝ g x)} = ∅ :=
  eq_empty_of_forall_notMem fun _ hx ↦ hx fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- If a continuous linear map `A` hits every vector annihilated by a functional `φ`, and `φ ∘ A`
does not vanish identically, then `A` is surjective: rescaling gives `v₁` with `φ (A v₁) = 1`, and
then `w - φ w • A v₁` is annihilated by `φ`, hence in the range. -/
private theorem surjective_of_ker_subset_range {A : E →L[ℝ] F} {φ : F →L[ℝ] ℝ}
    (hφA : ∃ v, φ (A v) ≠ 0) (h : ∀ y : F, φ y = 0 → ∃ v, A v = y) : Surjective A := by
  obtain ⟨v₀, hv₀⟩ := hφA
  intro w
  set v₁ : E := (φ (A v₀))⁻¹ • v₀ with hv₁def
  have hv₁ : φ (A v₁) = 1 := by
    simp [hv₁def, hv₀]
  obtain ⟨v, hv⟩ := h (w - φ w • A v₁) (by simp [hv₁])
  exact ⟨v + φ w • v₁, by simp [hv]⟩

end Surjective

section MorseSard

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {U : Set E} {f : E → F} (ν : Measure F) [IsAddHaarMeasure ν]

/-- The induction behind `TauCeti.addHaar_image_criticalPoints_eq_zero`, on the dimension `n` of
the source. Both spaces are quantified inside the statement because the induction step replaces
each of them by a hyperplane; they stay in their own universes, since a hyperplane of a space is a
submodule of it. -/
private theorem addHaar_image_criticalPoints_eq_zero_aux (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E ≤ n → ∀ (k : ℕ), n * n + 1 ≤ k →
      ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [IsAddHaarMeasure ν]
        (U : Set E), IsOpen U → ∀ f : E → F, (∀ x ∈ U, ContDiffAt ℝ (k : ℕ∞ω) f x) →
        ν (f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = 0 := by
  induction n with
  | zero =>
    intro E _ _ _ hE k _ F _ _ _ _ _ ν _ U _ f _
    rcases subsingleton_or_nontrivial F with _ | _
    · rw [setOf_not_surjective_fderiv_eq_empty f, inter_empty, image_empty, measure_empty]
    · have : Subsingleton E := Module.finrank_zero_iff.mp (Nat.le_zero.mp hE)
      exact (Set.Subsingleton.image (fun x _ y _ ↦ Subsingleton.elim x y) f).measure_zero ν
  | succ n ih =>
    intro E _ _ _ hE k hk F _ _ _ _ _ ν _ U hU f hf
    -- A trivial target has no critical points at all.
    rcases subsingleton_or_nontrivial F with _ | hF
    · rw [setOf_not_surjective_fderiv_eq_empty f, inter_empty, image_empty, measure_empty]
    have hk1 : 1 ≤ k := by nlinarith
    have hkne : (k : ℕ∞ω) ≠ 0 := by
      simpa using Nat.one_le_iff_ne_zero.1 hk1
    have hkinfty : (k : ℕ∞ω) ≠ ∞ := by simp
    have hknum : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ (k : ℕ∞ω) := by
      have : finrank ℝ E * finrank ℝ E + 1 ≤ k := by nlinarith
      exact_mod_cast this
    have hk' : n * n + 1 ≤ k := by nlinarith
    -- Split off the locus where the derivative vanishes, which the flat strata already cover.
    have hsub : U ∩ {x | ¬ Surjective (fderiv ℝ f x)} ⊆
        (U ∩ {x | fderiv ℝ f x = 0}) ∪
          (U ∩ {x | ¬ Surjective (fderiv ℝ f x)} ∩ {x | fderiv ℝ f x ≠ 0}) := by
      rintro x ⟨hxU, hxc⟩
      by_cases hx0 : fderiv ℝ f x = 0
      · exact Or.inl ⟨hxU, hx0⟩
      · exact Or.inr ⟨⟨hxU, hxc⟩, hx0⟩
    refine measure_mono_null (image_mono hsub) ?_
    rw [image_union]
    refine measure_union_null (addHaar_image_eq_zero_of_fderiv_eq_zero ν hknum
      (fun x hx ↦ hf x hx.1) (fun x hx ↦ hx.2)) ?_
    -- The outermost stratum, one point at a time.
    refine measure_image_null_of_locally_null fun a ha ↦ ?_
    obtain ⟨⟨haU, _⟩, hane⟩ := ha
    -- A direction on which the derivative does not vanish, and a functional dual to its image.
    obtain ⟨v₀, hv₀⟩ : ∃ v, fderiv ℝ f a v ≠ 0 := by
      by_contra hc
      exact hane (ContinuousLinearMap.ext fun v ↦ by
        simpa using not_not.1 (not_exists.1 hc v))
    obtain ⟨φ, hφ⟩ : ∃ φ : F →L[ℝ] ℝ, φ (fderiv ℝ f a v₀) = 1 := by
      obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ (fderiv ℝ f a v₀) (norm_ne_zero_iff.2 hv₀)
      have hgr : g (fderiv ℝ f a v₀) = ‖fderiv ℝ f a v₀‖ := by exact_mod_cast hg
      exact ⟨(‖fderiv ℝ f a v₀‖ : ℝ)⁻¹ • g, by
        simp [hgr, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv₀)]⟩
    set ψ : E →L[ℝ] ℝ := φ.comp (fderiv ℝ f a)
    have hψv₀ : ψ v₀ = 1 := hφ
    -- The two hyperplanes, and the projections onto them along `v₀` and its image.
    set Ek : Submodule ℝ E := LinearMap.ker (ψ : E →ₗ[ℝ] ℝ) with hEkdef
    set Fk : Submodule ℝ F := LinearMap.ker (φ : F →ₗ[ℝ] ℝ) with hFkdef
    let mFk : MeasurableSpace ↥Fk := borel ↥Fk
    have bFk : BorelSpace ↥Fk := ⟨rfl⟩
    have hπmem : ∀ x : E, (ContinuousLinearMap.id ℝ E - ψ.smulRight v₀) x ∈ Ek := by
      intro x
      simp [hEkdef, LinearMap.mem_ker, hψv₀]
    have hρmem : ∀ w : F,
        (ContinuousLinearMap.id ℝ F - φ.smulRight (fderiv ℝ f a v₀)) w ∈ Fk := by
      intro w
      simp [hFkdef, LinearMap.mem_ker, hφ]
    set π : E →L[ℝ] ↥Ek :=
      (ContinuousLinearMap.id ℝ E - ψ.smulRight v₀).codRestrict Ek hπmem
    set ρ : F →L[ℝ] ↥Fk :=
      (ContinuousLinearMap.id ℝ F - φ.smulRight (fderiv ℝ f a v₀)).codRestrict Fk hρmem
    have hπval : ∀ x : E, (π x : E) = x - ψ x • v₀ := fun x ↦ rfl
    have hρval : ∀ w : F, (ρ w : F) = w - φ w • fderiv ℝ f a v₀ := fun w ↦ rfl
    -- The two splittings.
    set eE : E ≃L[ℝ] ℝ × ↥Ek :=
      ContinuousLinearEquiv.equivOfInverse (ψ.prod π)
        ((ContinuousLinearMap.fst ℝ ℝ ↥Ek).smulRight v₀ +
          Ek.subtypeL.comp (ContinuousLinearMap.snd ℝ ℝ ↥Ek))
        (fun x ↦ by simp [hπval]) (fun p ↦ by
          have hp : ψ (p.2 : E) = 0 := p.2.2
          refine Prod.ext ?_ (Subtype.ext ?_)
          · simp [hψv₀, hp]
          · simp [hπval, hψv₀, hp])
    set eF : F ≃L[ℝ] ℝ × ↥Fk :=
      ContinuousLinearEquiv.equivOfInverse (φ.prod ρ)
        ((ContinuousLinearMap.fst ℝ ℝ ↥Fk).smulRight (fderiv ℝ f a v₀) +
          Fk.subtypeL.comp (ContinuousLinearMap.snd ℝ ℝ ↥Fk))
        (fun w ↦ by simp [hρval]) (fun p ↦ by
          have hp : φ (p.2 : F) = 0 := p.2.2
          refine Prod.ext ?_ (Subtype.ext ?_)
          · simp [hφ, hp]
          · simp [hρval, hφ, hp])
    -- The straightening map and its local inverse.
    set hmap : E → ℝ × ↥Ek := fun x ↦ (φ (f x), π x)
    have hfa : HasFDerivAt f (fderiv ℝ f a) a :=
      ((hf a haU).differentiableAt hkne).hasFDerivAt
    have hmapd : HasFDerivAt hmap (eE : E →L[ℝ] ℝ × ↥Ek) a :=
      (φ.hasFDerivAt.comp a hfa).prodMk π.hasFDerivAt
    have hmapC : ContDiffAt ℝ (k : ℕ∞ω) hmap a :=
      (φ.contDiff.comp_contDiffAt a (hf a haU)).prodMk π.contDiff.contDiffAt
    have hstrict : HasStrictFDerivAt hmap (eE : E →L[ℝ] ℝ × ↥Ek) a :=
      hmapC.hasStrictFDerivAt' hmapd hkne
    obtain ⟨Θ, hΘC, hΘleft, hΘright⟩ :
        ∃ Θ : ℝ × ↥Ek → E, ContDiffAt ℝ (k : ℕ∞ω) Θ (hmap a) ∧
          (∀ᶠ x in 𝓝 a, Θ (hmap x) = x) ∧ (∀ᶠ p in 𝓝 (hmap a), hmap (Θ p) = p) :=
      ⟨hmapC.localInverse hmapd hkne, hmapC.to_localInverse hmapd hkne,
        hstrict.eventually_left_inverse, hstrict.eventually_right_inverse⟩
    have hΘa : Θ (hmap a) = a := hΘleft.self_of_nhds
    -- Continuity of the derivative, used both to keep `φ ∘ Df` nonzero and to close the
    -- critical set.
    have hfderivC : ∀ x ∈ U, ContinuousAt (fderiv ℝ f) x := fun x hx ↦
      (hf x hx).continuousAt_fderiv hkne
    have hevalC : Continuous fun A : E →L[ℝ] F ↦ φ (A v₀) :=
      φ.continuous.comp (ContinuousLinearMap.apply ℝ F v₀).continuous
    -- An open neighbourhood of `hmap a` on which the local inverse is smooth and useful.
    obtain ⟨V, hVsub, hVopen, hVmem⟩ : ∃ V, (∀ p ∈ V, ContDiffAt ℝ (k : ℕ∞ω) Θ p ∧
        hmap (Θ p) = p ∧ Θ p ∈ U ∧ φ (fderiv ℝ f (Θ p) v₀) ≠ 0) ∧ IsOpen V ∧ hmap a ∈ V := by
      refine eventually_nhds_iff.1 ?_
      have hΘU : ∀ᶠ p in 𝓝 (hmap a), Θ p ∈ U :=
        hΘC.continuousAt.preimage_mem_nhds (by rw [hΘa]; exact hU.mem_nhds haU)
      have hne : ∀ᶠ p in 𝓝 (hmap a), φ (fderiv ℝ f (Θ p) v₀) ≠ 0 := by
        refine ContinuousAt.eventually_ne ?_ ?_
        · have h1 : ContinuousAt Θ (hmap a) := hΘC.continuousAt
          have h2 : ContinuousAt (fderiv ℝ f) (Θ (hmap a)) := by
            rw [hΘa]; exact hfderivC a haU
          exact hevalC.continuousAt.comp (h2.comp h1)
        · rw [hΘa, hφ]; exact one_ne_zero
      filter_upwards [hΘC.eventually hkinfty, hΘright, hΘU, hne] with p h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    -- An open neighbourhood of `a` carried into it.
    obtain ⟨W, hWsub, hWopen, hWmem⟩ : ∃ W, (∀ x ∈ W, x ∈ U ∧ Θ (hmap x) = x ∧ hmap x ∈ V) ∧
        IsOpen W ∧ a ∈ W := by
      refine eventually_nhds_iff.1 ?_
      filter_upwards [hU.mem_nhds haU, hΘleft,
        hmapC.continuousAt.preimage_mem_nhds (hVopen.mem_nhds hVmem)] with x h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWopen a hWmem
    set K : Set E := Metric.closedBall a (r / 2)
    have hKW : K ⊆ W := (Metric.closedBall_subset_ball (by linarith)).trans hrW
    have hKcomp : IsCompact K := isCompact_closedBall a (r / 2)
    -- The critical points in `K` form a compact set, so their image is measurable.
    have hCKcomp : IsCompact ({x | ¬ Surjective (fderiv ℝ f x)} ∩ K) := by
      refine hKcomp.of_isClosed_subset ?_ inter_subset_right
      have hclosed : IsClosed (K ∩ (fderiv ℝ f) ⁻¹' {A : E →L[ℝ] F | Surjective A}ᶜ) := by
        refine ContinuousOn.preimage_isClosed_of_isClosed ?_ hKcomp.isClosed
          isOpen_setOf_surjective.isClosed_compl
        exact fun x hx ↦ (hfderivC x (hWsub x (hKW hx)).1).continuousWithinAt
      rwa [inter_comm] at hclosed
    have hPcomp : IsCompact (f '' ({x | ¬ Surjective (fderiv ℝ f x)} ∩ K)) := by
      refine hCKcomp.image_of_continuousOn fun x hx ↦ ?_
      exact ((hf x (hWsub x (hKW hx.2)).1).continuousAt).continuousWithinAt
    -- The parametrized family of slice maps.
    set G : ℝ → ↥Ek → ↥Fk := fun t z ↦ ρ (f (Θ (t, z))) with hGdef
    set O : ℝ → Set ↥Ek := fun t ↦ {z | (t, z) ∈ V} with hOdef
    have hOopen : ∀ t, IsOpen (O t) := fun t ↦
      hVopen.preimage (by fun_prop)
    have hGsmooth : ∀ t, ∀ z ∈ O t, ContDiffAt ℝ (k : ℕ∞ω) (G t) z := by
      intro t z hz
      refine ρ.contDiff.comp_contDiffAt z ?_
      refine (hf _ (hVsub (t, z) hz).2.2.1).comp z ?_
      exact (hVsub (t, z) hz).1.comp z (contDiffAt_const.prodMk contDiffAt_id)
    -- A critical point of `f` on a level set is a critical point of the slice map.
    have hcrit : ∀ t, ∀ z ∈ O t, ¬ Surjective (fderiv ℝ f (Θ (t, z))) →
        ¬ Surjective (fderiv ℝ (G t) z) := by
      intro t z hz hx hGz
      refine hx ?_
      obtain ⟨hΘsmooth, -, hΘU, hΘne⟩ := hVsub (t, z) hz
      set x : E := Θ (t, z)
      have hslice : ContDiffAt ℝ (k : ℕ∞ω) (fun w : ↥Ek ↦ Θ (t, w)) z :=
        hΘsmooth.comp z (contDiffAt_const.prodMk contDiffAt_id)
      set T : ↥Ek →L[ℝ] E := fderiv ℝ (fun w : ↥Ek ↦ Θ (t, w)) z
      have hT : HasFDerivAt (fun w : ↥Ek ↦ Θ (t, w)) T z :=
        (hslice.differentiableAt hkne).hasFDerivAt
      have hfx : HasFDerivAt f (fderiv ℝ f x) x :=
        ((hf x hΘU).differentiableAt hkne).hasFDerivAt
      have hGd : HasFDerivAt (G t) (ρ.comp ((fderiv ℝ f x).comp T)) z :=
        ρ.hasFDerivAt.comp z (hfx.comp z hT)
      -- The composite `φ ∘ f ∘ Θ (t, ·)` is constant, so `φ ∘ Df ∘ T` vanishes.
      have hconst : ∀ w ∈ O t, φ (f (Θ (t, w))) = t := fun w hw ↦ by
        have := (hVsub (t, w) hw).2.1
        exact congrArg Prod.fst this
      have hzero : ∀ w : ↥Ek, φ (fderiv ℝ f x (T w)) = 0 := by
        have heq : (fun w : ↥Ek ↦ φ (f (Θ (t, w)))) =ᶠ[𝓝 z] fun _ ↦ t :=
          Filter.eventuallyEq_of_mem ((hOopen t).mem_nhds hz) hconst
        have hd : HasFDerivAt (fun w : ↥Ek ↦ φ (f (Θ (t, w))))
            (φ.comp ((fderiv ℝ f x).comp T)) z := φ.hasFDerivAt.comp z (hfx.comp z hT)
        have hzero' : φ.comp ((fderiv ℝ f x).comp T) = 0 :=
          (hd.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_const t z)
        intro w
        simpa using congrArg (fun A : ↥Ek →L[ℝ] ℝ ↦ A w) hzero'
      refine surjective_of_ker_subset_range ⟨v₀, hΘne⟩ fun y hy ↦ ?_
      obtain ⟨w, hw⟩ := hGz ⟨y, hy⟩
      refine ⟨T w, ?_⟩
      have := congrArg (Subtype.val) hw
      rw [hGd.fderiv] at this
      simpa [hρval, hzero w] using this
    -- Every slice of the image of the critical set is null.
    have hslicenull : ∀ t : ℝ, (addHaar : Measure ↥Fk)
        (Prod.mk t ⁻¹' (eF '' (f '' ({x | ¬ Surjective (fderiv ℝ f x)} ∩ K)))) = 0 := by
      intro t
      have hEkfin : finrank ℝ ↥Ek ≤ n := by
        have hsurj : Function.Surjective (ψ : E →ₗ[ℝ] ℝ) := fun c ↦
          ⟨c • v₀, by simp [hψv₀]⟩
        have hrank := LinearMap.finrank_range_add_finrank_ker (ψ : E →ₗ[ℝ] ℝ)
        rw [LinearMap.range_eq_top.2 hsurj, ← hEkdef] at hrank
        simp only [finrank_top, finrank_self] at hrank
        omega
      refine measure_mono_null ?_
        (ih ↥Ek hEkfin k hk' ↥Fk addHaar (O t) (hOopen t) (G t) (hGsmooth t))
      rintro y ⟨-, ⟨x, ⟨hxc, hxK⟩, rfl⟩, hxy⟩
      obtain ⟨-, hxΘ, hxV⟩ := hWsub x (hKW hxK)
      have hfst : φ (f x) = t := congrArg Prod.fst hxy
      have hsnd : ρ (f x) = y := congrArg Prod.snd hxy
      have hxΘ' : Θ (φ (f x), π x) = x := hxΘ
      have hxV' : (φ (f x), π x) ∈ V := hxV
      have hxeq : Θ (t, π x) = x := by rw [← hfst]; exact hxΘ'
      have hmem : π x ∈ O t := by
        rw [hOdef, Set.mem_ofPred_eq, ← hfst]; exact hxV'
      have hGval : G t (π x) = ρ (f x) := by simp only [hGdef, hxeq]
      refine ⟨π x, ⟨hmem, hcrit t _ hmem ?_⟩, ?_⟩
      · rw [hxeq]; exact hxc
      · rw [hGval, hsnd]
    -- Fubini, and back across the splitting of the target.
    have hprod : ((volume : Measure ℝ).prod (addHaar : Measure ↥Fk))
        (eF '' (f '' ({x | ¬ Surjective (fderiv ℝ f x)} ∩ K))) = 0 :=
      measure_prod_null_of_ae_null (hPcomp.image eF.continuous).isClosed.measurableSet
        (Filter.Eventually.of_forall hslicenull)
    have hnull : ν (f '' ({x | ¬ Surjective (fderiv ℝ f x)} ∩ K)) = 0 := by
      have := (ContinuousLinearEquiv.quasiMeasurePreserving_addHaar ν
        ((volume : Measure ℝ).prod (addHaar : Measure ↥Fk)) eF).preimage_null hprod
      rwa [Set.preimage_image_eq _ eF.injective] at this
    refine ⟨(U ∩ {x | ¬ Surjective (fderiv ℝ f x)} ∩ {x | fderiv ℝ f x ≠ 0}) ∩
      Metric.ball a (r / 2), inter_mem_nhdsWithin _
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))), ?_⟩
    refine measure_mono_null (image_mono ?_) hnull
    rintro x ⟨⟨⟨-, hxc⟩, -⟩, hxb⟩
    exact ⟨hxc, Metric.ball_subset_closedBall hxb⟩

/-- **The Morse--Sard theorem** on an open set. The values taken by a sufficiently smooth map at
the points of an open set where its Fréchet derivative is not surjective form a set of additive
Haar measure zero, with no relation required between the two finite dimensions. -/
theorem addHaar_image_criticalPoints_eq_zero {n : ℕ∞ω} (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ n f x)
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = 0 :=
  addHaar_image_criticalPoints_eq_zero_aux (finrank ℝ E) E le_rfl
    (finrank ℝ E * finrank ℝ E + 1) le_rfl F ν U hU f fun x hx ↦ (hf x hx).of_le hk

/-- **The Morse--Sard theorem.** The critical values of a sufficiently smooth map between
finite-dimensional real normed spaces, that is the values it takes at the points where its Fréchet
derivative is not surjective, form a set of additive Haar measure zero. No relation between the
two dimensions is required. -/
theorem ContDiff.addHaar_image_criticalPoints_eq_zero {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  simpa using TauCeti.addHaar_image_criticalPoints_eq_zero (U := univ) ν isOpen_univ
    (fun x _ ↦ hf.contDiffAt) hk

/-- The regular values of a sufficiently smooth map between finite-dimensional real normed spaces
are dense: this is the form in which the Morse--Sard theorem is used in transversality
arguments. -/
theorem ContDiff.dense_compl_image_criticalPoints {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense (f '' {x | ¬ Surjective (fderiv ℝ f x)})ᶜ :=
  interior_eq_empty_iff_dense_compl.1 <| Measure.interior_eq_empty_of_null <|
    TauCeti.ContDiff.addHaar_image_criticalPoints_eq_zero (ν := addHaar) hf hk

end MorseSard

end TauCeti

end
