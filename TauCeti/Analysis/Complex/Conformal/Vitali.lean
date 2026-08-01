/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Montel
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Vitali's convergence theorem

Vitali's theorem upgrades pointwise convergence on a set with an accumulation point to locally
uniform convergence for a locally bounded sequence of holomorphic functions. This completes the
Vitali component of layer **L1 (normal families / Montel)** of the conformal-mapping roadmap.

The proof applies `TauCeti.montel` twice. First choose one locally uniform subsequential limit `g`.
For an arbitrary subsequence, Montel supplies a further locally uniform limit `q`. Both limits
agree on the pointwise convergence set, hence on the whole preconnected domain by Mathlib's
analytic identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`. Thus every subsequence has a further
subsequence converging to `g`; the sequential convergence criterion, applied to continuous maps on
each compact subset, gives locally uniform convergence of the original sequence.

## Main result

* `TauCeti.vitali` — a locally bounded sequence of holomorphic functions which converges pointwise
  on a set with an accumulation point in the domain converges locally uniformly to a holomorphic
  function.
* `TauCeti.vitali_of_tendsto` — the same theorem with a prescribed pointwise limit on the
  convergence set.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0–L3
material overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505).
This file is therefore a **temporary shim**: if a human-curated Vitali theorem lands in Mathlib,
this statement should be backed by it, or deleted and its consumers refactored to the upstream API.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
-/

public section

open Complex Filter Set Topology

namespace TauCeti

variable {Ω A : Set ℂ} {F : ℕ → ℂ → ℂ}

/-- Two locally uniform subsequential limits agree on a set where the original sequence converges
pointwise. -/
private theorem eqOn_of_subseq_limits
    (hAΩ : A ⊆ Ω)
    (hpoint : ∀ z ∈ A, ∃ w, Tendsto (fun n => F n z) atTop (𝓝 w))
    {φ ψ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) (hψ : Tendsto ψ atTop atTop)
    {g q : ℂ → ℂ}
    (hg : TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop Ω)
    (hq : TendstoLocallyUniformlyOn (fun n => F (ψ n)) q atTop Ω) :
    A.EqOn g q := by
  intro z hz
  obtain ⟨w, hw⟩ := hpoint z hz
  have hgw : Tendsto (fun n => F (φ n) z) atTop (𝓝 w) := hw.comp hφ
  have hqw : Tendsto (fun n => F (ψ n) z) atTop (𝓝 w) := hw.comp hψ
  exact (tendsto_nhds_unique (hg.tendsto_at (hAΩ hz)) hgw).trans
    (tendsto_nhds_unique (hq.tendsto_at (hAΩ hz)) hqw).symm

/-- **Vitali's convergence theorem.** Let `Ω` be an open preconnected subset of `ℂ`. A locally
bounded sequence of holomorphic functions on `Ω` which converges pointwise on a subset `A ⊆ Ω`
having an accumulation point in `Ω` converges locally uniformly on `Ω` to a holomorphic function.

The pointwise limit on `A` need not be supplied: its existence is enough to determine the
holomorphic limit uniquely. -/
theorem vitali (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hAΩ : A ⊆ Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hacc : AccPt z₀ (𝓟 A))
    (hpoint : ∀ z ∈ A, ∃ w, Tendsto (fun n => F n z) atTop (𝓝 w)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ TendstoLocallyUniformlyOn F g atTop Ω := by
  obtain ⟨φ, g, hφ, hg, hφconv⟩ := montel hΩ hF hb
  refine ⟨g, hg, (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2 ?_⟩
  intro K hKΩ hK
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hrestr :
      Tendsto
        (fun n => ⟨K.domRestrict (F n), ((hF n).continuousOn.mono hKΩ).domRestrict⟩ :
          ℕ → C(K, ℂ))
        atTop
        (𝓝 ⟨K.domRestrict g, (hg.continuousOn.mono hKΩ).domRestrict⟩) := by
    apply tendsto_of_subseq_tendsto
    intro ψ hψ
    have hbψ : IsLocallyBoundedOn (fun n => F (ψ n)) Ω := by
      rw [isLocallyBoundedOn_def]
      intro L hLΩ hL
      obtain ⟨C, hC⟩ := isLocallyBoundedOn_def.mp hb L hLΩ hL
      exact ⟨C, fun n => hC (ψ n)⟩
    obtain ⟨θ, q, hθ, hq, hθconv⟩ :=
      montel hΩ (fun n => hF (ψ n)) hbψ
    have hqgA : A.EqOn q g := eqOn_of_subseq_limits hAΩ hpoint
      (hψ.comp hθ.tendsto_atTop) hφ.tendsto_atTop hθconv hφconv
    have hqg : Ω.EqOn q g :=
      (hq.analyticOnNhd hΩ).eqOn_of_preconnected_of_frequently_eq
        (hg.analyticOnNhd hΩ) hconn hz₀
        ((accPt_iff_frequently_nhdsNE.mp hacc).mono fun z hz => hqgA hz)
    refine ⟨θ, ?_⟩
    have hcompact :
        TendstoUniformlyOn (fun n => F (ψ (θ n))) g atTop K :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
        ((hθconv.congr_right hqg).mono hKΩ)
    exact ((hg.continuousOn.mono hKΩ).tendsto_domRestrict_iff_tendstoUniformlyOn
      (fun n => (hF (ψ (θ n))).continuousOn.mono hKΩ)).2 hcompact
  exact ((hg.continuousOn.mono hKΩ).tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun n => (hF n).continuousOn.mono hKΩ)).1 hrestr

/-- **Vitali's theorem with prescribed pointwise values.** Under the hypotheses of `vitali`, if
the sequence converges pointwise on `A` to a specified function `g`, its locally uniform
holomorphic limit agrees with `g` throughout `A`.

No regularity of `g` away from `A` is assumed or concluded. -/
theorem vitali_of_tendsto (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hAΩ : A ⊆ Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hacc : AccPt z₀ (𝓟 A))
    {g : ℂ → ℂ} (hpoint : ∀ z ∈ A, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q Ω ∧ A.EqOn q g ∧
      TendstoLocallyUniformlyOn F q atTop Ω := by
  obtain ⟨q, hq, hconv⟩ :=
    vitali hΩ hconn hF hb hAΩ hz₀ hacc fun z hz => ⟨g z, hpoint z hz⟩
  refine ⟨q, hq, fun z hz => ?_, hconv⟩
  exact tendsto_nhds_unique (hconv.tendsto_at (hAΩ hz)) (hpoint z hz)

end TauCeti
