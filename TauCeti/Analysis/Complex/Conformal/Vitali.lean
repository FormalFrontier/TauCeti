/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Montel.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Vitali's convergence theorem

Vitali's theorem upgrades pointwise convergence on a set with an accumulation point to locally
uniform convergence for a locally bounded sequence of holomorphic functions. This completes the
Vitali component of layer **L1 (normal families / Montel)** of the conformal-mapping roadmap.

Everything below runs on one principle, isolated here as
`tendstoLocallyUniformlyOn_of_forall_subseq_eqOn`: for a locally bounded family of holomorphic
functions, a candidate limit `g` continuous on `Ω` which every *locally uniform subsequential*
limit agrees with on `Ω` is already the locally uniform limit of the whole sequence. Indeed
`TauCeti.montel` supplies a locally uniform limit inside every subsequence, so the hypothesis says
that every subsequence has a further subsequence converging to `g`; the sequential convergence
criterion `tendsto_of_subseq_tendsto`, applied to the restrictions to a compact subset as
continuous maps, then gives convergence of the original sequence there. Only the identification of
the subsequential limits changes from one statement below to the next:

* for `TauCeti.vitali`, `g` is one subsequential limit chosen by Montel, and two subsequential
  limits agree on the pointwise convergence set `A`, hence on the whole *preconnected* `Ω` by
  Mathlib's analytic identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` —
  which is where the accumulation point of `A` is spent;
* for the pointwise-limit forms, `g` is the prescribed pointwise limit and the identification is
  the uniqueness of limits in a Hausdorff space, point by point. No identity theorem, no
  accumulation point, and — this is the reason these are not corollaries of `TauCeti.vitali`
  — no connectivity hypothesis on `Ω` is needed.

## Main results

* `TauCeti.vitali` — a locally bounded sequence of holomorphic functions which converges pointwise
  on a set with an accumulation point in the domain converges locally uniformly to a holomorphic
  function.
* `TauCeti.vitali_of_tendsto` — the same theorem with a prescribed pointwise limit on the
  convergence set.
* `TauCeti.differentiableOn_of_isLocallyBoundedOn_of_forall_tendsto` — a locally bounded
  sequence of holomorphic functions converging pointwise on the whole of `Ω` has a
  **holomorphic** pointwise limit.
* `TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto` — and it converges
  to that limit **locally uniformly**: on a locally bounded holomorphic sequence, pointwise
  convergence and locally uniform convergence are the same thing.
* `TauCeti.tendstoLocallyUniformlyOn_deriv_of_isLocallyBoundedOn_of_forall_tendsto` — hence the
  derivatives converge locally uniformly to the derivative of the pointwise limit, by
  Weierstrass' theorem (`TendstoLocallyUniformlyOn.deriv`); differentiating a pointwise limit
  termwise is legitimate for a locally bounded holomorphic sequence.

## The target

The target is a proper complex normed space `E`, the generality at which
`Conformal/Montel/Basic.lean` states the selection theorem this file runs on; the conformal-mapping
consumers instantiate `E = ℂ`. Properness cannot be dropped from the argument, `TauCeti.montel`
being false without it. Vitali's theorem does hold for an arbitrary Banach target (Arendt and
Nikolski, *Vector-valued holomorphic functions revisited*, Math. Z. **234** (2000), §2), but by a
different argument — convergence of the Taylor coefficients at an accumulation point, and a clopen
propagation — so that generality is a separate theorem rather than a weakening of these.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0–L3
material overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505).
This file is therefore a **temporary shim**: if a human-curated Vitali theorem lands in Mathlib,
this statement should be backed by it, or deleted and its consumers refactored to the upstream API.
Mathlib's Weierstrass convergence theorem `TendstoLocallyUniformlyOn.deriv` and its identity
theorem are consumed rather than restated.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
-/

public section

open Complex Filter Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
variable {Ω A : Set ℂ} {F : ℕ → ℂ → E} {g : ℂ → E}

/-! ### The subsequence principle -/

/-- **Every subsequential limit is `g` implies the sequence converges to `g`.** For a locally
bounded sequence of holomorphic functions on an open `Ω` and a candidate limit `g` continuous on
`Ω`, it suffices to know that every locally uniform limit of a subsequence agrees with `g` on `Ω`.

`TauCeti.montel` produces such a limit inside each subsequence, so the hypothesis makes every
subsequence have a further subsequence converging locally uniformly to `g`, which
`tendsto_of_subseq_tendsto` converts into convergence of the whole sequence. That criterion is
about a *sequence in a topological space*, so it is applied on each compact `K ⊆ Ω` to the
restrictions `K.domRestrict (F n)` as elements of `C(K, E)`, where compact-open convergence is
uniform convergence on `K`.

Kept private: it is the shared engine of the theorems below, whose hypotheses are the checkable
ones, and its own hypothesis is not in a form a consumer can supply without redoing their work. -/
private theorem tendstoLocallyUniformlyOn_of_forall_subseq_eqOn (hΩ : IsOpen Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hg : ContinuousOn g Ω)
    (hlim : ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∀ q : ℂ → E,
      TendstoLocallyUniformlyOn (fun n => F (ψ n)) q atTop Ω → Ω.EqOn q g) :
    TendstoLocallyUniformlyOn F g atTop Ω := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2 fun K hKΩ hK => ?_
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine ((hg.mono hKΩ).tendsto_domRestrict_iff_tendstoUniformlyOn
    fun n => (hF n).continuousOn.mono hKΩ).1 (tendsto_of_subseq_tendsto fun ψ hψ => ?_)
  obtain ⟨θ, q, hθ, -, hθconv⟩ := montel hΩ (fun n => hF (ψ n)) (hb.comp ψ)
  refine ⟨θ, ((hg.mono hKΩ).tendsto_domRestrict_iff_tendstoUniformlyOn
    fun n => (hF (ψ (θ n))).continuousOn.mono hKΩ).2 ?_⟩
  refine (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp ?_
  exact (hθconv.congr_right (hlim (ψ ∘ θ) (hψ.comp hθ.tendsto_atTop) q hθconv)).mono hKΩ

/-! ### Vitali's theorem -/

omit [NormedSpace ℂ E] [ProperSpace E] in
/-- Two locally uniform subsequential limits agree on a set where the original sequence converges
pointwise. -/
private theorem eqOn_of_subseq_limits (hAΩ : A ⊆ Ω)
    (hpoint : ∀ z ∈ A, ∃ w, Tendsto (fun n => F n z) atTop (𝓝 w))
    {φ ψ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) (hψ : Tendsto ψ atTop atTop)
    {p q : ℂ → E}
    (hp : TendstoLocallyUniformlyOn (fun n => F (φ n)) p atTop Ω)
    (hq : TendstoLocallyUniformlyOn (fun n => F (ψ n)) q atTop Ω) :
    A.EqOn p q := by
  intro z hz
  obtain ⟨w, hw⟩ := hpoint z hz
  exact (tendsto_nhds_unique (hp.tendsto_at (hAΩ hz)) (hw.comp hφ)).trans
    (tendsto_nhds_unique (hq.tendsto_at (hAΩ hz)) (hw.comp hψ)).symm

/-- **Vitali's convergence theorem.** Let `Ω` be an open preconnected subset of `ℂ`. A locally
bounded sequence of holomorphic functions on `Ω` which converges pointwise on a subset `A ⊆ Ω`
having an accumulation point in `Ω` converges locally uniformly on `Ω` to a holomorphic function.

The pointwise limit on `A` need not be supplied: its existence is enough to determine the
holomorphic limit uniquely. -/
theorem vitali (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hAΩ : A ⊆ Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hacc : AccPt z₀ (𝓟 A))
    (hpoint : ∀ z ∈ A, ∃ w, Tendsto (fun n => F n z) atTop (𝓝 w)) :
    ∃ g : ℂ → E, DifferentiableOn ℂ g Ω ∧ TendstoLocallyUniformlyOn F g atTop Ω := by
  obtain ⟨φ, g, hφ, hg, hφconv⟩ := montel hΩ hF hb
  refine ⟨g, hg, tendstoLocallyUniformlyOn_of_forall_subseq_eqOn hΩ hF hb hg.continuousOn
    fun ψ hψ q hq => ?_⟩
  have hqd : DifferentiableOn ℂ q Ω := hq.differentiableOn (.of_forall fun n => hF (ψ n)) hΩ
  refine (hqd.analyticOnNhd hΩ).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hΩ) hconn
    hz₀ ((accPt_iff_frequently_nhdsNE.mp hacc).mono fun z hz => ?_)
  exact eqOn_of_subseq_limits hAΩ hpoint hψ hφ.tendsto_atTop hq hφconv hz

/-- **Vitali's theorem with prescribed pointwise values.** Under the hypotheses of `vitali`, if
the sequence converges pointwise on `A` to a specified function `g`, its locally uniform
holomorphic limit agrees with `g` throughout `A`.

No regularity of `g` away from `A` is assumed or concluded; when `A` is all of `Ω` the limit is
`g` itself, which is
`TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto`. -/
theorem vitali_of_tendsto (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hAΩ : A ⊆ Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hacc : AccPt z₀ (𝓟 A))
    (hpoint : ∀ z ∈ A, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    ∃ q : ℂ → E, DifferentiableOn ℂ q Ω ∧ A.EqOn q g ∧
      TendstoLocallyUniformlyOn F q atTop Ω := by
  obtain ⟨q, hq, hconv⟩ :=
    vitali hΩ hconn hF hb hAΩ hz₀ hacc fun z hz => ⟨g z, hpoint z hz⟩
  refine ⟨q, hq, fun z hz => ?_, hconv⟩
  exact tendsto_nhds_unique (hconv.tendsto_at (hAΩ hz)) (hpoint z hz)

/-! ### Pointwise convergence on the whole domain -/

/-- **The pointwise limit of a locally bounded sequence of holomorphic functions is holomorphic.**
No connectivity of `Ω` is assumed, and no accumulation point has to be exhibited: `TauCeti.montel`
extracts a holomorphic locally uniform limit along a subsequence, and that limit is the pointwise
limit `g`, limits in a Hausdorff space being unique. -/
theorem differentiableOn_of_isLocallyBoundedOn_of_forall_tendsto (hΩ : IsOpen Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hpoint : ∀ z ∈ Ω, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    DifferentiableOn ℂ g Ω := by
  obtain ⟨φ, q, hφ, hq, hφconv⟩ := montel hΩ hF hb
  exact hq.congr fun z hz =>
    tendsto_nhds_unique ((hpoint z hz).comp hφ.tendsto_atTop) (hφconv.tendsto_at hz)

/-- **On a locally bounded sequence of holomorphic functions, pointwise convergence is locally
uniform convergence.** If a locally bounded sequence of holomorphic functions on an open `Ω`
converges pointwise at every point of `Ω`, it converges locally uniformly to that pointwise limit.

This is not a case of `TauCeti.vitali`, which asks `Ω` preconnected in order to propagate an
identification made on a small set `A` to the whole domain: here the identification is available at
every point already, so the identity theorem — and with it the connectivity — is not needed. The
converse implication is immediate, locally uniform convergence being pointwise convergence at each
point of `Ω`. -/
theorem tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto (hΩ : IsOpen Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hpoint : ∀ z ∈ Ω, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    TendstoLocallyUniformlyOn F g atTop Ω := by
  refine tendstoLocallyUniformlyOn_of_forall_subseq_eqOn hΩ hF hb
    (differentiableOn_of_isLocallyBoundedOn_of_forall_tendsto hΩ hF hb hpoint).continuousOn
    fun ψ hψ q hq z hz => ?_
  exact tendsto_nhds_unique (hq.tendsto_at hz) ((hpoint z hz).comp hψ)

/-- **A locally bounded holomorphic sequence may be differentiated termwise along a pointwise
limit.** If a locally bounded sequence of holomorphic functions converges pointwise on an open `Ω`,
the derivatives converge locally uniformly to the derivative of the pointwise limit.

Pointwise convergence alone says nothing about derivatives; what makes the conclusion available is
that `TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto` promotes the
hypothesis to locally uniform convergence, on which Mathlib's Weierstrass theorem
`TendstoLocallyUniformlyOn.deriv` acts. -/
theorem tendstoLocallyUniformlyOn_deriv_of_isLocallyBoundedOn_of_forall_tendsto (hΩ : IsOpen Ω)
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hpoint : ∀ z ∈ Ω, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    TendstoLocallyUniformlyOn (fun n => deriv (F n)) (deriv g) atTop Ω :=
  (tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto hΩ hF hb hpoint).deriv
    (.of_forall hF) hΩ

end TauCeti
