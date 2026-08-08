/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Contour.MeromorphicLaurent
public import TauCeti.Analysis.Contour.PolarPart.Decomposition
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions

/-!
# Discharging the HW conditions into the per-pole hypotheses

The polar-part principal-value theorem (`Contour.PolarPartDecomposition.hasCauchyPVAt_polarPart`)
takes raw per-crossing hypotheses: interiority of the crossings, flatness at each surviving
coefficient's order, and the tangent-power sector equation. This file discharges them from the
roadmap-level data: closedness with the basepoint off the pole gives interiority; condition
(A′) gives the flatness through the downward restriction; condition (B) gives the sector
equation through the crossing-angle resonance bridge and the uniqueness of Laurent
coefficients — the decomposition's coefficients are the canonical ones, so the condition's own
Laurent witness constrains them.

## Main results

* `Contour.PolarPartDecomposition.coeff_eq_meromorphicPolarCoeffAt` — a decomposition of
  canonical order has the canonical coefficients.
* `Contour.ConditionAprime.flatOfOrder_of_crossing` — condition (A′) discharges the gated
  flatness hypothesis (for every index below the order; no surviving coefficient needed).
* `Contour.ConditionB.pow_unit_tangent_eq_of_coeff_ne_zero` — condition (B) discharges the gated
  sector hypothesis.
* `Contour.mem_Ioo_of_closed_of_ne` — on a closed curve with basepoint off `z`, every
  crossing of `z` is interior.

## Provenance

The condition-(B) discharge corresponds to `condB_to_h_B_at_crossings_corner` of
`Crossing.lean` in the AINTLIB `LeanModularForms` development (there through a decomposition
constructed from the condition's own witness; here through coefficient uniqueness against the
canonical data). See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a
generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- **Interior crossings from a closed curve rooted off the point**: if `γ a = γ b ≠ z`, every
parameter of `[a, b]` where `γ` takes the value `z` is interior. -/
theorem mem_Ioo_of_closed_of_ne {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hclosed : γ a = γ b) (hγa : γ a ≠ z) :
    ∀ t ∈ Icc a b, γ t = z → t ∈ Ioo a b := by
  intro t ht h_eq
  refine ⟨lt_of_le_of_ne ht.1 fun h => hγa ?_, lt_of_le_of_ne ht.2 fun h => hγa ?_⟩
  · rw [h]; exact h_eq
  · rw [hclosed, ← h]; exact h_eq

/-- Interior membership in the `min`/`max` form the condition clauses use. -/
private theorem interior_mem_minmax {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Ioo a b) :
    t ∈ Ioo (min a b) (max a b) := by
  rwa [min_eq_left hab, max_eq_right hab]

/-- At an interior parameter, a limit of `deriv γ` from the right is the immersion's one-sided
tangent, hence non-zero. -/
private theorem tendsto_deriv_ne_zero_right {γ : ℝ → ℂ} {a b t : ℝ} {L : ℂ}
    (h_imm : IsPwC1ImmersionOn γ a b) (ht : t ∈ Ioo a b)
    (hL : Tendsto (deriv γ) (𝓝[>] t) (𝓝 L)) : L ≠ 0 := by
  obtain ⟨W, hW_ne, hW⟩ := h_imm.exists_deriv_right_limit (by
    rw [min_eq_left (ht.1.trans ht.2).le, max_eq_right (ht.1.trans ht.2).le]
    exact ⟨ht.1.le, ht.2⟩)
  rwa [tendsto_nhds_unique hL hW]

/-- At an interior parameter, a limit of `deriv γ` from the left is the immersion's one-sided
tangent, hence non-zero. -/
private theorem tendsto_deriv_ne_zero_left {γ : ℝ → ℂ} {a b t : ℝ} {L : ℂ}
    (h_imm : IsPwC1ImmersionOn γ a b) (ht : t ∈ Ioo a b)
    (hL : Tendsto (deriv γ) (𝓝[<] t) (𝓝 L)) : L ≠ 0 := by
  obtain ⟨W, hW_ne, hW⟩ := h_imm.exists_deriv_left_limit (by
    rw [min_eq_left (ht.1.trans ht.2).le, max_eq_right (ht.1.trans ht.2).le]
    exact ⟨ht.1, ht.2.le⟩)
  rwa [tendsto_nhds_unique hL hW]

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- **A decomposition of canonical order has the canonical coefficients**: near `s ∈ S` the
decomposition exhibits `f` as its polar part at `s` plus a function analytic there, so by
uniqueness of finite principal-part expansions its coefficients are
`meromorphicPolarCoeffAt`. -/
theorem coeff_eq_meromorphicPolarCoeffAt (decomp : PolarPartDecomposition f S U)
    (hU : IsOpen U) (hSU : (S : Set ℂ) ⊆ U) (s : S) (hMero : MeromorphicAt f ↑s)
    (h_ord : decomp.order s = meromorphicPolarOrderAt f ↑s) (k : Fin (decomp.order s)) :
    decomp.coeff s k = meromorphicPolarCoeffAt hMero ⟨k.val, h_ord ▸ k.isLt⟩ := by
  classical
  set g : ℂ → ℂ :=
    fun z => decomp.analyticRemainder z + ∑ s' ∈ S.attach.erase s, decomp.polarPart s' z
    with hg_def
  have h_sum_an : AnalyticAt ℂ
      (fun z => ∑ s' ∈ S.attach.erase s, decomp.polarPart s' z) ↑s := by
    refine Finset.analyticAt_fun_sum _ fun s' hs' => ?_
    have h_ne : (↑s : ℂ) ≠ ↑s' :=
      (Subtype.coe_injective.ne (Finset.ne_of_mem_erase hs')).symm
    rw [show decomp.polarPart s' = fun z => ∑ k : Fin (decomp.order s'),
        decomp.coeff s' k / (z - (↑s' : ℂ)) ^ (k.val + 1) from
      funext (decomp.polarPart_eq s')]
    exact Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.div
      ((analyticAt_id.sub analyticAt_const).pow _)
      (pow_ne_zero _ (sub_ne_zero.mpr h_ne))
  have h_g_cont : ContinuousAt g ↑s :=
    (decomp.analyticRemainder_differentiableOn.continuousOn.continuousAt
      (hU.mem_nhds (hSU s.2))).add h_sum_an.continuousAt
  have h_off : ∀ᶠ z in 𝓝 (↑s : ℂ), z ∉ (↑S : Set ℂ) \ {(↑s : ℂ)} := by
    have h_closed : IsClosed ((↑S : Set ℂ) \ {(↑s : ℂ)}) :=
      (S.finite_toSet.subset Set.sdiff_subset).isClosed
    exact h_closed.isOpen_compl.mem_nhds (by simp)
  have h_exp : ∀ᶠ z in 𝓝[≠] (↑s : ℂ), f z = g z + ∑ k : Fin (decomp.order s),
      decomp.coeff s k / (z - (↑s : ℂ)) ^ (k.val + 1) := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds (hSU s.2)),
      nhdsWithin_le_nhds h_off, self_mem_nhdsWithin] with z hzU hzS hz_ne
    have h_f := decomp.f_eq z ⟨hzU, fun hzS' => hzS ⟨hzS', hz_ne⟩⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_attach S s)] at h_f
    rw [h_f, decomp.polarPart_eq s z, hg_def]
    ring
  have h_wit := laurent_coeff_eq_meromorphicPolarCoeffAt hMero h_g_cont h_exp k.val
  rwa [dif_pos k.isLt, dif_pos (h_ord ▸ k.isLt)] at h_wit

end PolarPartDecomposition

/-- **Condition (A′) discharges the flatness hypothesis** of the polar-part principal-value
theorem: at each crossing of `s`, the pole's canonical order pins `meromorphicOrderAt`, the
condition gives flatness of the full order, and the downward restriction gives it at each
surviving coefficient's order. -/
theorem ConditionAprime.flatOfOrder_of_crossing {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    {S' : Finset ℂ} (hA : ConditionAprime γ a b f S') {S : Finset ℂ} {U : Set ℂ}
    (decomp : PolarPartDecomposition f S U) (s : S) (hsS' : (s : ℂ) ∈ S')
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b)
    (h_ord : decomp.order s = meromorphicPolarOrderAt f ↑s) :
    ∀ k : Fin (decomp.order s), 1 ≤ k.val →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → FlatOfOrder γ t (k.val + 1) := by
  intro k hk1 t ht h_eq
  have ht_Ioo := h_interior t ht h_eq
  have h_pos : 0 < meromorphicPolarOrderAt f ↑s := by
    have := k.isLt; omega
  have h_flat_full := hA.interior t (interior_mem_minmax hab ht_Ioo)
    (by rw [h_eq]; exact hsS') (meromorphicPolarOrderAt f ↑s) (by omega)
    (by rw [h_eq]; exact meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos h_pos)
  refine h_flat_full.of_le (by have := k.isLt; omega)
    (h_imm.continuousOn.continuousAt ?_)
  rw [uIcc_of_le hab]
  exact Icc_mem_nhds ht_Ioo.1 ht_Ioo.2

/-- **Condition (B) discharges the sector hypothesis** of the polar-part principal-value
theorem: a surviving coefficient of index `≥ 1` makes `s` a pole of order `> 1`, the
condition's sector compatibility at the crossing angle carries a Laurent witness whose
coefficients are the decomposition's by uniqueness, and its resonance transfers to the unit
tangent powers through the crossing-angle bridge. -/
theorem ConditionB.pow_unit_tangent_eq_of_coeff_ne_zero {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    (hB : ConditionB γ a b f) {S : Finset ℂ} {U : Set ℂ}
    (decomp : PolarPartDecomposition f S U) (hU : IsOpen U) (hSU : (S : Set ℂ) ⊆ U)
    (s : S) (hMero : MeromorphicAt f ↑s) (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b)
    (h_ord : decomp.order s = meromorphicPolarOrderAt f ↑s) :
    ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → ∀ L_R L_L : ℂ,
        Tendsto (deriv γ) (𝓝[>] t) (𝓝 L_R) → Tendsto (deriv γ) (𝓝[<] t) (𝓝 L_L) →
        (L_R / (‖L_R‖ : ℂ)) ^ k.val = ((-L_L) / (‖L_L‖ : ℂ)) ^ k.val := by
  intro k hk1 hc t ht h_eq L_R L_L hR hL
  have ht_Ioo := h_interior t ht h_eq
  have h_can := decomp.coeff_eq_meromorphicPolarCoeffAt hU hSU s hMero h_ord k
  have h_gt : 1 < meromorphicPolarOrderAt f ↑s := by
    have := k.isLt; omega
  have h_sec := hB.interior t (interior_mem_minmax hab ht_Ioo)
    (by rw [h_eq]; exact meromorphicOrderAt_lt_neg_one_of_one_lt_meromorphicPolarOrderAt h_gt)
  rw [h_eq] at h_sec
  obtain ⟨N', a', g', hg', h_exp, h_reso⟩ := h_sec.laurent_compatible
  have h_wit := laurent_coeff_eq_meromorphicPolarCoeffAt hMero hg'.continuousAt h_exp k.val
  rw [dif_pos (show k.val < meromorphicPolarOrderAt f ↑s from h_ord ▸ k.isLt)] at h_wit
  have h_ne : meromorphicPolarCoeffAt hMero ⟨k.val, h_ord ▸ k.isLt⟩ ≠ 0 := h_can ▸ hc
  by_cases hkN : k.val < N'
  · rw [dif_pos hkN] at h_wit
    obtain ⟨m, hm⟩ := h_reso ⟨k.val, hkN⟩ (fun h0 => h_ne (h_wit ▸ h0)) hk1
    exact pow_unit_tangent_eq_of_resonance
      (tendsto_deriv_ne_zero_right h_imm ht_Ioo hR)
      (tendsto_deriv_ne_zero_left h_imm ht_Ioo hL) hR hL ⟨m, hm⟩
  · rw [dif_neg hkN] at h_wit
    exact absurd h_wit.symm h_ne

end TauCeti.Contour

end
