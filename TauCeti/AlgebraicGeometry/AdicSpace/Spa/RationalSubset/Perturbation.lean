/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.Basic
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.RingTheory.Valuation.Basic
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Rational subsets do not move under small perturbations

**A strengthening of Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Proposition 7.34.** Wedhorn
assumes a complete Hausdorff affinoid ring; the results here need only a Huber ring `A`. Fix a pair
of definition `(A₀, I)`, a ring of integral elements `A⁺`, a finite numerator set `T` whose ideal
`T · A` is open, and a denominator `s`. There is a basic neighbourhood `Iⁿ` of zero such that
replacing each numerator and the denominator by anything within `Iⁿ` of it leaves the rational
subset unchanged:

```text
R(T'/s') = R(T/s).
```

The perturbed data are not indexed by `T`: `T'` is any finite set each of whose elements is
`Iⁿ`-close to some element of `T` and which has an `Iⁿ`-close element for each of them. That is
what the statement actually needs, and it avoids carrying a bijection `T ≃ T'` — the same set may
be presented with different cardinality after perturbation.

## Main results

* `TauCeti.ValuationSpectrum.valuation_lt_of_mem_idealImage` : elements of a sufficiently small
  basic neighbourhood have value strictly below the rational subset's denominator.
* `TauCeti.ValuationSpectrum.exists_forall_rationalSubset_eq_of_sub_mem_idealImage` : Proposition
  7.34, with the perturbation measured by an explicit power of the ideal of definition.
* `TauCeti.ValuationSpectrum.exists_mem_nhds_forall_rationalSubset_eq_of_sub_mem` : the same
  statement over a Huber ring, with the perturbation measured by a neighbourhood of zero and no
  pair of definition in sight.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.29 and
  Proposition 7.34.
-/

public section

namespace TauCeti.ValuationSpectrum

open Filter Topology TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- Membership in a rational subset, phrased with the canonical valuation of the point rather
than with its valuative relation. -/
theorem mem_rationalSubset_iff_valuation (Aplus : Subring A) (T : Finset A) (s : A)
    (v : Spv A) :
    v ∈ rationalSubset Aplus T s ↔
      v ∈ spa Aplus ∧ (∀ t ∈ T, v.valuation t ≤ v.valuation s) ∧ v.valuation s ≠ 0 := by
  rw [mem_rationalSubset_iff]
  refine and_congr_right fun _ ↦ and_congr ?_ ?_
  · exact forall₂_congr fun t _ ↦ (valuation_le_iff v t s).symm
  · exact ⟨fun h h0 ↦ h ((valuation_le_iff v s 0).mp (by simp [h0])),
      fun h h' ↦ h (by simpa using (valuation_le_iff v s 0).mpr h')⟩

/-- **A neighbourhood of zero is strictly dominated by the denominator of a rational subset.**
If the numerator ideal `T · A` supplies the decomposition of
`TauCeti.Huber.PairOfDefinition.exists_forall_mem_idealImage_exists_sum_eq` in degree `n`, then
at a continuous point at which every `t ∈ T` is dominated by a nonzero `v s`, every element of
`Iⁿ` has value strictly below `v s`.

The hypothesis is the decomposition itself rather than the openness of `T · A`, because
`TauCeti.ValuationSpectrum.exists_forall_rationalSubset_eq_of_sub_mem_idealImage` applies the
estimate with two different denominators and one fixed exponent. -/
theorem valuation_lt_of_mem_idealImage (P : PairOfDefinition A) {T : Finset A} {n : ℕ}
    (hdec : ∀ a ∈ P.idealImage n, ∃ w : A → A,
      (∀ t ∈ T, w t ∈ P.idealImage 1) ∧ ∑ t ∈ T, t * w t = a)
    {v : Spv A} (hv : v.IsContinuous) {s : A} (hs : v.valuation s ≠ 0)
    (hle : ∀ t ∈ T, v.valuation t ≤ v.valuation s) {a : A} (ha : a ∈ P.idealImage n) :
    v.valuation a < v.valuation s := by
  obtain ⟨w, hw, hsum⟩ := hdec a ha
  rw [← hsum]
  refine Valuation.map_sum_lt _ hs fun t ht ↦ ?_
  have h1 : v.valuation (w t) < 1 :=
    ((isContinuous_def v).mp hv).lt_one_of_isTopologicallyNilpotent
      (P.isTopologicallyNilpotent_of_mem_idealImage one_ne_zero (hw t ht))
  calc v.valuation (t * w t) = v.valuation t * v.valuation (w t) := map_mul _ _ _
    _ ≤ v.valuation s * v.valuation (w t) := mul_le_mul' (hle t ht) le_rfl
    _ < v.valuation s := mul_lt_of_lt_one_right (zero_lt_iff.mpr hs) h1

variable [IsTopologicalRing A]

/-- **A strengthening of Wedhorn Proposition 7.34.** Wedhorn assumes a complete Hausdorff
affinoid ring; here, for a numerator set `T` in a Huber ring with `T · A` open, there is an
exponent `n` such that perturbing the numerators and the denominator inside the basic
neighbourhood `Iⁿ` of zero does not change the rational subset.

The two matching hypotheses say that `T'` and `T` are `Iⁿ`-close as *sets*: every perturbed
numerator is near an original one and conversely. No hypothesis is placed on `T' · A`, and `A` is
not assumed complete. -/
theorem exists_forall_rationalSubset_eq_of_sub_mem_idealImage (P : PairOfDefinition A)
    (Aplus : Subring A)
    (T : Finset A) (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (s : A) :
    ∃ n : ℕ, ∀ (T' : Finset A) (s' : A),
      (∀ t ∈ T, ∃ u ∈ T', t - u ∈ P.idealImage n) →
      (∀ u ∈ T', ∃ t ∈ T, u - t ∈ P.idealImage n) →
      s - s' ∈ P.idealImage n →
      rationalSubset Aplus T' s' = rationalSubset Aplus T s := by
  classical
  obtain ⟨n, hn⟩ := P.exists_forall_mem_idealImage_exists_sum_eq T hT
  refine ⟨n, fun T' s' hTT' hT'T hss' ↦ ?_⟩
  choose! u hu hδ using hTT'
  ext v
  rw [mem_rationalSubset_iff_valuation, mem_rationalSubset_iff_valuation]
  constructor
  · rintro ⟨hspa, hT'le, hs'⟩
    have hv : v.IsContinuous := ((mem_spa_iff _ _).mp hspa).1
    -- every displacement is strictly below `v s'`, by a maximality argument
    have hsmall : ∀ t ∈ T, v.valuation (t - u t) < v.valuation s' := by
      by_contra hcon
      push Not at hcon
      obtain ⟨t₁, ht₁, hge⟩ := hcon
      obtain ⟨t₀, ht₀, hmax⟩ :=
        T.exists_max_image (fun t ↦ v.valuation (t - u t)) ⟨t₁, ht₁⟩
      have hge₀ : v.valuation s' ≤ v.valuation (t₀ - u t₀) := hge.trans (hmax t₁ ht₁)
      have hγ0 : v.valuation (t₀ - u t₀) ≠ 0 := fun h ↦ hs' (le_antisymm (h ▸ hge₀) zero_le)
      have hTγ : ∀ t ∈ T, v.valuation t ≤ v.valuation (t₀ - u t₀) := fun t ht ↦
        (Valuation.le_max_sub v.valuation t (u t)).trans
          (max_le ((hT'le (u t) (hu t ht)).trans hge₀) (hmax t ht))
      exact absurd (valuation_lt_of_mem_idealImage P hn hv hγ0 hTγ (hδ t₀ ht₀)) (lt_irrefl _)
    have hTle : ∀ t ∈ T, v.valuation t ≤ v.valuation s' := fun t ht ↦
      (Valuation.le_max_sub v.valuation t (u t)).trans
        (max_le (hT'le (u t) (hu t ht)) (hsmall t ht).le)
    have hss : v.valuation s = v.valuation s' := by
      have he : s' + (s - s') = s := by ring
      rw [← he]
      exact Valuation.map_add_eq_of_lt_left _
        (valuation_lt_of_mem_idealImage P hn hv hs' hTle hss')
    exact ⟨hspa, fun t ht ↦ hss ▸ hTle t ht, hss ▸ hs'⟩
  · rintro ⟨hspa, hTle, hs⟩
    have hv : v.IsContinuous := ((mem_spa_iff _ _).mp hspa).1
    have hlt : ∀ a ∈ P.idealImage n, v.valuation a < v.valuation s :=
      fun a ha ↦ valuation_lt_of_mem_idealImage P hn hv hs hTle ha
    have hss : v.valuation s' = v.valuation s := by
      have he : s - (s - s') = s' := by ring
      rw [← he]
      exact Valuation.map_sub_eq_of_lt_left _ (hlt _ hss')
    refine ⟨hspa, fun y hy ↦ ?_, hss ▸ hs⟩
    obtain ⟨t, ht, hyt⟩ := hT'T y hy
    exact hss ▸ (Valuation.le_max_sub v.valuation y t).trans
      (max_le (hTle t ht) (hlt _ hyt).le)

/-- **A generalization of Wedhorn Proposition 7.34.** The source assumes a complete Hausdorff
affinoid ring; this theorem shows that, already over a Huber ring, a rational subset with open
numerator ideal is unchanged by perturbing its defining data inside a suitable neighbourhood of
zero.

This is the form the later theory uses: no pair of definition appears, so the neighbourhood is
the only datum a caller has to produce. -/
theorem exists_mem_nhds_forall_rationalSubset_eq_of_sub_mem [IsHuberRing A]
    (Aplus : Subring A)
    (T : Finset A) (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (s : A) :
    ∃ V ∈ 𝓝 (0 : A), ∀ (T' : Finset A) (s' : A),
      (∀ t ∈ T, ∃ u ∈ T', t - u ∈ V) →
      (∀ u ∈ T', ∃ t ∈ T, u - t ∈ V) →
      s - s' ∈ V →
      rationalSubset Aplus T' s' = rationalSubset Aplus T s := by
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  obtain ⟨n, hn⟩ :=
    exists_forall_rationalSubset_eq_of_sub_mem_idealImage P Aplus T hT s
  exact ⟨(P.idealImage n : Set A),
    (P.isOpen_idealImage n).mem_nhds (P.idealImage n).zero_mem, hn⟩

end TauCeti.ValuationSpectrum

end
