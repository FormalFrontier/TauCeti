/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Montel.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.Ascoli

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

When the sequence already converges pointwise on the *whole* of `Ω`, none of that machinery is
needed. Local boundedness makes the sequence equicontinuous on `Ω`
(`TauCeti.IsLocallyBoundedOn.equicontinuousOn`, the Cauchy-estimate half of Montel's theorem), and
on an equicontinuous family pointwise convergence *is* uniform convergence on each compact subset,
by Mathlib's Arzelà–Ascoli lemma `Equicontinuous.tendsto_uniformFun_iff_pi`. This is why the
whole-domain statements below are not corollaries of `TauCeti.vitali`: they spend no identity
theorem, hence need neither an accumulation point nor connectivity of `Ω`, and no selection
theorem, hence do not run on `TauCeti.montel` at all.

## Main results

* `TauCeti.vitali` — a locally bounded sequence of holomorphic functions on an open *preconnected*
  `Ω` which converges pointwise on a set with an accumulation point in the domain converges locally
  uniformly to a holomorphic function.
* `TauCeti.vitali_of_tendsto` — the same theorem with a prescribed pointwise limit on the
  convergence set.
* `TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto` — a locally bounded
  sequence of holomorphic functions converging pointwise on the whole of `Ω` converges to that
  limit **locally uniformly**: on such a sequence, pointwise convergence and locally uniform
  convergence are the same thing.
* `TauCeti.exists_differentiableOn_tendstoLocallyUniformlyOn_of_isLocallyBoundedOn` — its
  existential companion, for a consumer who knows the sequence converges at each point of `Ω`
  without a name for the limit.

Holomorphy of such a pointwise limit, and termwise differentiation along it, are then Mathlib's
`TendstoLocallyUniformlyOn.differentiableOn` and `TendstoLocallyUniformlyOn.deriv` applied to the
third of these.

## The scalar target

Unlike the estimates of `Conformal/NormalFamilies.lean` and the Montel results they feed, which
are stated for a target complex normed space `E`, this file keeps the roadmap's scalar target `ℂ`.
For `TauCeti.vitali` the reason is the proof: it runs `TauCeti.montel`, which is genuinely false
for a target that is not proper, so an `E`-valued version of that argument would prove only the
finite-dimensional case. Vitali's theorem does hold for an arbitrary Banach target (Arendt and
Nikolski, *Vector-valued holomorphic functions revisited*, Math. Z. **234** (2000), §2), but by a
different argument — convergence of the Taylor coefficients at an accumulation point, and a clopen
propagation — so that generality is a separate theorem rather than a weakening of this one. The
whole-domain statements spend no selection theorem, so their argument is target-agnostic; they too
are stated at `ℂ`, the generality the conformal-mapping roadmap sets for the theorems this entry
adds and the one at which its consumers use them.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0–L3
material overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505).
This file is therefore a **temporary shim**: if a human-curated Vitali theorem lands in Mathlib,
this statement should be backed by it, or deleted and its consumers refactored to the upstream API.
Mathlib's `TendstoLocallyUniformlyOn.differentiableOn`, its identity theorem and its Arzelà–Ascoli
framework are consumed rather than restated.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
-/

public section

open Complex Filter Set Topology

namespace TauCeti

variable {Ω A : Set ℂ} {F : ℕ → ℂ → ℂ}

/-! ### Vitali's theorem -/

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
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hrestr :
      Tendsto
        (fun n => ⟨K.domRestrict (F n), ((hF n).continuousOn.mono hKΩ).domRestrict⟩ :
          ℕ → C(K, ℂ))
        atTop
        (𝓝 ⟨K.domRestrict g, (hg.continuousOn.mono hKΩ).domRestrict⟩) := by
    apply tendsto_of_subseq_tendsto
    intro ψ hψ
    obtain ⟨θ, q, hθ, hq, hθconv⟩ :=
      montel hΩ (fun n => hF (ψ n)) (hb.comp ψ)
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

No regularity of `g` away from `A` is assumed or concluded; when `A` is all of `Ω` the limit is
`g` itself, which is
`TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto`. -/
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

/-! ### Pointwise convergence on the whole domain -/

/-- **On a locally bounded sequence of holomorphic functions, pointwise convergence is locally
uniform convergence.** If a locally bounded sequence of holomorphic functions on an open `Ω`
converges pointwise at every point of `Ω`, it converges locally uniformly to that pointwise limit.

This is not a case of `TauCeti.vitali`, which asks `Ω` preconnected in order to propagate an
identification made on a small set `A` to the whole domain: here the identification is available at
every point already, so the identity theorem — and with it the connectivity — is not needed. The
converse implication is immediate, locally uniform convergence being pointwise convergence at each
point of `Ω`.

Neither is it a case of `TauCeti.montel`: only the equicontinuity half of Montel's theorem is
spent, not the selection theorem. On a compact `K ⊆ Ω` local boundedness makes the
restricted sequence equicontinuous (`TauCeti.IsLocallyBoundedOn.equicontinuousOn`), and on an
equicontinuous family the topology of uniform convergence and the topology of pointwise convergence
have the same convergent sequences, which is Mathlib's Arzelà–Ascoli lemma
`Equicontinuous.tendsto_uniformFun_iff_pi`. -/
theorem tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto (hΩ : IsOpen Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω) {g : ℂ → ℂ}
    (hpoint : ∀ z ∈ Ω, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    TendstoLocallyUniformlyOn F g atTop Ω := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2 fun K hKΩ hK => ?_
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heq : Equicontinuous (K.domRestrict ∘ F) :=
    (equicontinuous_restrict_iff F).2 ((hb.equicontinuousOn hΩ hF).mono hKΩ)
  rw [tendstoUniformlyOn_iff_restrict]
  exact UniformFun.tendsto_iff_tendstoUniformly.1
    ((heq.tendsto_uniformFun_iff_pi atTop (K.domRestrict g)).2
      (tendsto_pi_nhds.2 fun z => hpoint z (hKΩ z.2)))

/-- **The pointwise limit need not be named.** A locally bounded sequence of holomorphic functions
on an open `Ω` which converges at each point of `Ω` converges locally uniformly on `Ω` to a
holomorphic function — the existential companion of the statement above, in the shape
`TauCeti.vitali` takes on a subset `A`.

The limit is `fun z => limUnder atTop fun n => F n z`, which the hypothesis identifies as the
pointwise limit on `Ω`; no connectivity of `Ω` and no accumulation point is involved, exactly as
above, and holomorphy of the limit is `TendstoLocallyUniformlyOn.differentiableOn`. -/
theorem exists_differentiableOn_tendstoLocallyUniformlyOn_of_isLocallyBoundedOn
    (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hpoint : ∀ z ∈ Ω, ∃ w, Tendsto (fun n => F n z) atTop (𝓝 w)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ TendstoLocallyUniformlyOn F g atTop Ω :=
  have h : ∀ z ∈ Ω, Tendsto (fun n => F n z) atTop (𝓝 (limUnder atTop fun n => F n z)) :=
    fun z hz => tendsto_nhds_limUnder (hpoint z hz)
  have hconv := tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto hΩ hF hb h
  ⟨_, hconv.differentiableOn (.of_forall hF) hΩ, hconv⟩

end TauCeti
