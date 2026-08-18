/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.Riemannian.PiecewisePath

/-!
# The piecewise smooth description of the Riemannian distance

do Carmo defines the distance between two points of a Riemannian manifold as the infimum of the
lengths of the *piecewise* `C¹` paths joining them, whereas Mathlib's `Manifold.riemannianEDist`
is the infimum over `C¹` paths only. This file proves that the two infima agree.

The bridge is corner smoothing. Each piece of a piecewise `C¹` path is first reparametrized
affinely onto `[0, 1]`, which changes neither its endpoints nor its length, and then flattened
near its endpoints by `TauCeti.exists_contMDiff_pathELength_eq`; the flattened pieces can be
concatenated with `TauCeti.exists_contMDiff_pathELength_eq_add` while staying globally `C¹`.
Iterating over the partition replaces a broken path by a `C¹` path with the same endpoints and
exactly the same length, so neither infimum can be smaller than the other.

## Main results

* `TauCeti.Manifold.IsPiecewiseContMDiffOn.exists_contMDiff_pathELength_eq`: **corner smoothing**,
  every piecewise `C¹` path has a globally `C¹` path on `[0, 1]` with the same endpoints and the
  same length.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.riemannianEDist_le_pathELength`: a piecewise `C¹` path
  bounds the Riemannian extended distance between its endpoints.
* `TauCeti.Manifold.riemannianEDist_eq_iInf_pathELength_piecewise` and
  `TauCeti.Manifold.riemannianEDist_eq_iInf_pathELength_piecewise_zero_one`: the piecewise `C¹`
  infimum, over arbitrary parameter intervals and over `[0, 1]`, is `Manifold.riemannianEDist`.

Only Mathlib's `Manifold.pathELength` and `Manifold.riemannianEDist` occur here; the piecewise
formulation is exposed exclusively through the comparison theorems above, and no competing notion
of length or distance is introduced.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 1, Definition 2.9 and Chapter 7, Section 2,
  Definition 2.4.
* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Corner smoothing and the piecewise-`C¹` comparison".
-/

public section

open Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
  {γ : ℝ → M} {a b : ℝ}

/-- A `C¹` path on a compact interval admits a globally `C¹` path on `[0, 1]` with the same
endpoints and the same length. This is the single-piece case of corner smoothing; the
reparametrization is affine, so it changes neither the endpoints nor the length. -/
theorem exists_contMDiff_pathELength_eq_of_le (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η 0 = γ a ∧ η 1 = γ b ∧
      Manifold.pathELength I η 0 1 = Manifold.pathELength I γ a b := by
  set f := ContinuousAffineMap.lineMap (R := ℝ) a b with hf
  have hmaps : f '' Icc 0 1 ⊆ Icc a b := by
    rw [hf, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
    simp [hab, segment_eq_Icc]
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ f) (Icc 0 1) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact f.contDiff.contDiffOn
    · rw [← image_subset_iff]
      exact hmaps
  obtain ⟨η, hη, hη₀, hη₁, hlen, -, -⟩ := TauCeti.exists_contMDiff_pathELength_eq hcomp
  refine ⟨η, hη, ?_, ?_, ?_⟩
  · simpa [hf, ContinuousAffineMap.coe_lineMap_eq] using hη₀
  · simpa [hf, ContinuousAffineMap.coe_lineMap_eq] using hη₁
  · rw [hlen, hf]
    have key := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := γ)
      (f := ContinuousAffineMap.lineMap (R := ℝ) a b) (a := 0) (b := 1) zero_le_one
      (by
        rw [ContinuousAffineMap.coe_lineMap_eq]
        exact (AffineMap.lineMap_mono hab).monotoneOn _)
      (ContinuousAffineMap.lineMap (R := ℝ) a b).differentiableOn
      (by
        simpa [ContinuousAffineMap.coe_lineMap_eq] using
          hγ.mdifferentiableOn one_ne_zero)
    simpa [ContinuousAffineMap.coe_lineMap_eq] using key

/-- **Corner smoothing along an explicit partition.** A path which is `C¹` on every piece of a
finite ordered partition is replaced by a globally `C¹` path on `[0, 1]` with the same endpoints
whose length is the sum of the lengths of the pieces.

The induction concatenates the smoothed pieces one at a time with
`TauCeti.exists_contMDiff_pathELength_eq_add`, which is available precisely because each smoothed
piece is constant near its endpoints. -/
private theorem exists_contMDiff_pathELength_eq_sum (γ : ℝ → M) :
    ∀ (k : ℕ) (τ : Fin (k + 2) → ℝ), (∀ i : Fin (k + 1), τ i.castSucc ≤ τ i.succ) →
      (∀ i : Fin (k + 1), ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (τ i.castSucc) (τ i.succ))) →
      ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η 0 = γ (τ 0) ∧
        η 1 = γ (τ (Fin.last (k + 1))) ∧
        Manifold.pathELength I η 0 1 =
          ∑ i : Fin (k + 1), Manifold.pathELength I γ (τ i.castSucc) (τ i.succ) := by
  intro k
  induction k with
  | zero =>
      intro τ hτ hγ
      obtain ⟨η, hη, hη₀, hη₁, hlen⟩ := exists_contMDiff_pathELength_eq_of_le (hτ 0) (hγ 0)
      exact ⟨η, hη, by simpa using hη₀, by simpa using hη₁, by simpa using hlen⟩
  | succ k ih =>
      intro τ hτ hγ
      obtain ⟨α, hα, hα₀, hα₁, hαlen⟩ := exists_contMDiff_pathELength_eq_of_le (hτ 0) (hγ 0)
      obtain ⟨β, hβ, hβ₀, hβ₁, hβlen⟩ := ih (fun i ↦ τ i.succ)
        (fun i ↦ by simpa only [Fin.succ_castSucc] using hτ i.succ)
        (fun i ↦ by simpa only [Fin.succ_castSucc] using hγ i.succ)
      obtain ⟨η, hη, hη₀, hη₁, hηlen, -, -⟩ :=
        TauCeti.exists_contMDiff_pathELength_eq_add hα.contMDiffOn hβ.contMDiffOn
          (hα₁.trans hβ₀.symm)
      refine ⟨η, hη, ?_, ?_, ?_⟩
      · rw [hη₀, hα₀, Fin.castSucc_zero]
      · rw [hη₁, hβ₁, Fin.succ_last]
      · rw [hηlen, hαlen, hβlen]
        conv_rhs => rw [Fin.sum_univ_succ]
        simp only [Fin.succ_castSucc, Fin.castSucc_zero]

/-- **Corner smoothing.** Every piecewise `C¹` path admits a globally `C¹` path on `[0, 1]` with
the same endpoints and exactly the same `Manifold.pathELength`.

This is the theorem which makes the piecewise `C¹` and the `C¹` descriptions of the Riemannian
distance agree: a broken competitor can always be rounded off at its corners without gaining or
losing length. The regularity index is `1` throughout because `Manifold.riemannianEDist` is an
infimum over `C¹` paths; the smoothed path is only claimed to be `C¹`, since the affine
reparametrization of a piece is composed with a transition function which flattens it at the
junctions. -/
theorem IsPiecewiseContMDiffOn.exists_contMDiff_pathELength_eq
    (h : IsPiecewiseContMDiffOn I 1 γ a b) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η 0 = γ a ∧ η 1 = γ b ∧
      Manifold.pathELength I η 0 1 = Manifold.pathELength I γ a b := by
  obtain ⟨k, τ, hτa, hτb, hτ, hpieces, hsum⟩ := h.exists_partition_sum_pathELength_eq
  obtain ⟨η, hη, hη₀, hη₁, hlen⟩ :=
    exists_contMDiff_pathELength_eq_sum γ k τ (fun i ↦ (hτ i).le) hpieces
  exact ⟨η, hη, by rw [hη₀, hτa], by rw [hη₁, hτb], by rw [hlen, hsum]⟩

/-- The Riemannian extended distance between the endpoints of a piecewise `C¹` path is at most
the length of that path. This is Mathlib's `Manifold.riemannianEDist_le_pathELength` for broken
competitors. -/
theorem IsPiecewiseContMDiffOn.riemannianEDist_le_pathELength
    (h : IsPiecewiseContMDiffOn I 1 γ a b) :
    Manifold.riemannianEDist I (γ a) (γ b) ≤ Manifold.pathELength I γ a b := by
  obtain ⟨η, hη, hη₀, hη₁, hlen⟩ := h.exists_contMDiff_pathELength_eq
  calc Manifold.riemannianEDist I (γ a) (γ b)
      ≤ Manifold.pathELength I η 0 1 :=
        Manifold.riemannianEDist_le_pathELength hη.contMDiffOn hη₀ hη₁ zero_le_one
    _ = Manifold.pathELength I γ a b := hlen

variable (I) in
/-- **do Carmo's distance is Mathlib's distance.** The Riemannian extended distance, defined by
Mathlib as an infimum over `C¹` paths, is also the infimum of the lengths of the piecewise `C¹`
paths joining the two points, over all parameter intervals.

The inequality `≥` holds because a `C¹` path is piecewise `C¹`, and `≤` because corner smoothing
turns a piecewise `C¹` competitor into a `C¹` one of the same length. -/
theorem riemannianEDist_eq_iInf_pathELength_piecewise (x y : M) :
    Manifold.riemannianEDist I x y =
      ⨅ (γ : ℝ → M) (a : ℝ) (b : ℝ) (_ : IsPiecewiseContMDiffOn I 1 γ a b)
        (_ : γ a = x) (_ : γ b = y), Manifold.pathELength I γ a b := by
  refine le_antisymm ?_ (le_of_forall_gt fun r hr ↦ ?_)
  · refine le_iInf fun γ ↦ le_iInf fun a ↦ le_iInf fun b ↦ le_iInf fun h ↦
      le_iInf fun hx ↦ le_iInf fun hy ↦ ?_
    subst hx
    subst hy
    exact h.riemannianEDist_le_pathELength
  · obtain ⟨γ, hγ₀, hγ₁, hγ, hlt⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
    refine lt_of_le_of_lt ?_ hlt
    exact iInf_le_of_le γ (iInf_le_of_le 0 (iInf_le_of_le 1
      (iInf_le_of_le (IsPiecewiseContMDiffOn.of_contMDiffOn zero_lt_one hγ)
        (iInf_le_of_le hγ₀ (iInf_le_of_le hγ₁ le_rfl)))))

variable (I) in
/-- The Riemannian extended distance is the infimum of the lengths of the piecewise `C¹` paths
joining the two points on the fixed parameter interval `[0, 1]`. Restricting to `[0, 1]` loses
nothing, because corner smoothing already delivers its `C¹` competitor there. -/
theorem riemannianEDist_eq_iInf_pathELength_piecewise_zero_one (x y : M) :
    Manifold.riemannianEDist I x y =
      ⨅ (γ : ℝ → M) (_ : IsPiecewiseContMDiffOn I 1 γ 0 1)
        (_ : γ 0 = x) (_ : γ 1 = y), Manifold.pathELength I γ 0 1 := by
  refine le_antisymm ?_ (le_of_forall_gt fun r hr ↦ ?_)
  · refine le_iInf fun γ ↦ le_iInf fun h ↦ le_iInf fun hx ↦ le_iInf fun hy ↦ ?_
    subst hx
    subst hy
    exact h.riemannianEDist_le_pathELength
  · obtain ⟨γ, hγ₀, hγ₁, hγ, hlt⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
    refine lt_of_le_of_lt ?_ hlt
    exact iInf_le_of_le γ (iInf_le_of_le (IsPiecewiseContMDiffOn.of_contMDiffOn zero_lt_one hγ)
      (iInf_le_of_le hγ₀ (iInf_le_of_le hγ₁ le_rfl)))

end TauCeti.Manifold
