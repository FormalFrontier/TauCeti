/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic
public import TauCeti.Analysis.Complex.HolomorphicSheaf

/-!
# Analytic continuation as a lift to the étalé space of holomorphic germs

`Conformal/Continuation/Basic.lean` defines `TauCeti.IsAnalyticContinuationAlong` — a family `f`
of functions carrying, at each parameter time `t`, a germ at `γ t`, locally constant in `t` — and
its docstring records, without proof, that

> reading the germs as points of the étale space of holomorphic germs over `ℂ`, the condition says
> precisely that `t ↦ (germ of f t at γ t)` is a continuous lift of `γ`.

`TauCeti/Analysis/Complex/HolomorphicSheaf.lean` builds that space. This file proves the sentence
(`TauCeti.isAnalyticContinuationAlong_iff_continuousOn_germPoint`) and spends it: the étalé
projection is a separated local homeomorphism there, which is exactly what Mathlib's abstract
monodromy theorem `IsLocalHomeomorph.monodromy_theorem` asks of a map, so that theorem applies
verbatim to holomorphic germs (`TauCeti.monodromy_theorem_etaleSpace`).

## The dictionary

Given that each `f t` is analytic at `γ t` and that `γ` is continuous, the two remaining clauses of
a continuation — that nearby parameter times carry the same germ — and continuity of
`t ↦ germPoint (f t) (γ t)` say the same thing, and the proof is a translation in both directions
of the same fact about the étalé topology, namely that the germs of one section over one open set
form a neighbourhood of each of them:

* forwards, `f t =ᶠ[𝓝 (γ t)] f t₀` for `t` near `t₀` says the germ map agrees near `t₀` with
  `germPoint (f t₀) ∘ γ`, and the germ map of a *single* holomorphic function is continuous
  (`TauCeti.HolomorphicPresheaf.continuousOn_germPoint`), being the section of the étalé space
  that function sweeps out;
* backwards, continuity puts the lifted point, for `t` near `t₀`, in the set of germs of one
  section representing `f t₀`, and reading that membership back through
  `TauCeti.HolomorphicPresheaf.germAt_eq_iff` — the identity of two germs is the eventual identity
  of two analytic functions — is the locality clause.

The base point of the lift is `γ t` by construction (`TauCeti.HolomorphicPresheaf.base_germPoint`),
so no separate lifting condition has to be stated. In the other direction a continuous map into
the étalé space is a continuation of its own representatives
(`TauCeti.isAnalyticContinuationAlong_repFun`), so the two notions are interchangeable rather than
merely comparable.

## Monodromy, and what this does not replace

`Conformal/Monodromy.lean` proves the monodromy theorem for germ families directly, by a metric
stability argument, and its docstring names building the étalé space and rederiving the theorem
from Mathlib's abstract one as follow-up work. That rederivation is
`TauCeti.monodromy_theorem_etaleSpace`, and it is stated where the abstract theorem states it:
about continuous lifts of the rows of a homotopy rel endpoints, not about germ families. It does
not replace `TauCeti.monodromy_theorem_of_free_homotopy`, whose homotopy is allowed to move the
endpoints and whose conclusion is a continuation along the path the far endpoint sweeps out;
Mathlib's abstract theorem is rel endpoints and gives an equality of points, so the free-homotopy
form remains the business of the metric engine in `Conformal/Monodromy.lean`. What is gained here
is the interface: monodromy for holomorphic germs is now an instance of covering-space-style path
lifting, in the vocabulary the deck-group and uniformization consumers of layer **L4** of
`TauCetiRoadmap/ConformalMapping/README.md` speak.

## Main results

* `TauCeti.isAnalyticContinuationAlong_iff_continuousOn_germPoint` — **a continuation along a path
  is exactly a continuous lift of that path to the étalé space of holomorphic germs**.
* `TauCeti.isAnalyticContinuationAlong_repFun` — the converse reading: a continuous map into the
  étalé space continues the germs it carries along its own base path.
* `TauCeti.monodromy_theorem_etaleSpace` — **the monodromy theorem in étalé-space form**, from
  Mathlib's abstract monodromy theorem and the separatedness proved in
  `TauCeti/Analysis/Complex/HolomorphicSheaf.lean`.

## Generality

The germs are germs of maps `ℂ → ℂ`, the target of the sheaf built in
`TauCeti/Analysis/Complex/HolomorphicSheaf.lean`, whereas `TauCeti.IsAnalyticContinuationAlong` is
stated for maps `ℂ → E` into a complex Banach space; the specialisation is discussed there, and is
the one the conformal-mapping consumers use. The parameter space `X` and the parameter set `s` are
arbitrary, as in `Conformal/Continuation/Basic.lean`: nothing below needs the parameter set to be
an interval, and the monodromy statement is the only place the unit interval appears.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* O. Forster, *Lectures on Riemann Surfaces* (GTM 81), §§6--7.
-/

public section

namespace TauCeti

open CategoryTheory Metric Opposite Set TopologicalSpace Topology unitInterval

variable {X : Type*} [TopologicalSpace X] {f : X → ℂ → ℂ} {γ : X → ℂ} {s : Set X}

/-! ### A continuation along a path is a continuous lift -/

/-- **Analytic continuation along a path is a continuous lift to the étalé space of holomorphic
germs.** Assume each `f t` is analytic at `γ t` and that `γ` is continuous on the parameter set.
Then `f` is an analytic continuation along `γ` exactly when the germ it carries, read as a point
of the étalé space of holomorphic germs, depends continuously on the parameter.

The lifting condition itself needs no hypothesis: the germ point of `f t` at `γ t` sits over
`γ t` by construction. So the content of the equivalence is that the locality clause of a
continuation — nearby parameter times carry the same germ — is continuity in the étalé
topology. -/
theorem isAnalyticContinuationAlong_iff_continuousOn_germPoint (hγ : ContinuousOn γ s)
    (hf : ∀ t ∈ s, AnalyticAt ℂ (f t) (γ t)) :
    IsAnalyticContinuationAlong f γ s ↔
      ContinuousOn (fun t => HolomorphicPresheaf.germPoint (f t) (γ t)) s := by
  constructor
  · intro hcont t₀ ht₀
    obtain ⟨r, hr, hball⟩ := (hf t₀ ht₀).exists_ball_analyticOnNhd
    have hat : ContinuousAt (HolomorphicPresheaf.germPoint (f t₀)) (γ t₀) :=
      (HolomorphicPresheaf.continuousOn_germPoint
        (U := ⟨ball (γ t₀) r, isOpen_ball⟩) hball).continuousAt
          (isOpen_ball.mem_nhds (mem_ball_self hr))
    refine (hat.comp_continuousWithinAt (hγ t₀ ht₀)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [hcont.locallyEq t₀ ht₀] with t ht using HolomorphicPresheaf.germPoint_congr ht
  · intro hcont
    refine ⟨hγ, hf, fun t ht => ?_⟩
    obtain ⟨r, hr, hball⟩ := (hf t ht).exists_ball_analyticOnNhd
    set B : Opens (TopCat.of ℂ) := ⟨ball (γ t) r, isOpen_ball⟩
    have hbB : γ t ∈ B := mem_ball_self hr
    set sec := HolomorphicPresheaf.toSection B (f t) hball
    have hsec : HolomorphicPresheaf.sectionFun sec =ᶠ[𝓝 (γ t)] f t :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hbB)
        (HolomorphicPresheaf.sectionFun_toSection hball)
    have hgerm : holomorphicPresheaf.germ B (γ t) hbB sec =
        (HolomorphicPresheaf.germPoint (f t) (γ t)).germ :=
      (HolomorphicPresheaf.germAt_eq_germ_of_eventuallyEq hbB sec hsec).symm
    have hnbhd := TopCat.Presheaf.EtaleSpace.eventually_nhds
      (HolomorphicPresheaf.germPoint (f t) (γ t)) hbB sec hgerm
    filter_upwards [(hcont t ht).eventually hnbhd, self_mem_nhdsWithin] with u hu hus
    obtain ⟨hbu, hgu⟩ := hu
    have h₁ : HolomorphicPresheaf.germAt (f u) (γ u) =
        HolomorphicPresheaf.germAt (HolomorphicPresheaf.sectionFun sec) (γ u) :=
      hgu.trans (HolomorphicPresheaf.germAt_eq_germ hbu sec).symm
    have h₂ : f u =ᶠ[𝓝 (γ u)] HolomorphicPresheaf.sectionFun sec :=
      (HolomorphicPresheaf.germAt_eq_iff (hf u hus)
        (HolomorphicPresheaf.analyticOnNhd_sectionFun sec _ hbu)).mp h₁
    exact h₂.trans (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hbu)
      (HolomorphicPresheaf.sectionFun_toSection hball))

/-- **A continuation along a path is a continuous lift**, the forward half of
`TauCeti.isAnalyticContinuationAlong_iff_continuousOn_germPoint` with its hypotheses read off the
continuation itself. -/
theorem IsAnalyticContinuationAlong.continuousOn_germPoint
    (hcont : IsAnalyticContinuationAlong f γ s) :
    ContinuousOn (fun t => HolomorphicPresheaf.germPoint (f t) (γ t)) s :=
  (isAnalyticContinuationAlong_iff_continuousOn_germPoint hcont.continuousOn
    hcont.analyticAt).mp hcont

/-- **A continuous map into the étalé space continues its own representatives.** Choosing at each
parameter time a holomorphic representative of the germ carried there gives an analytic
continuation along the base path of the lift.

Together with `TauCeti.IsAnalyticContinuationAlong.continuousOn_germPoint` this says that
continuations along a path and continuous lifts of it are the same data, up to the choice of a
representative for a germ. -/
theorem isAnalyticContinuationAlong_repFun {Γ : X → holomorphicPresheaf.EtaleSpace}
    (hΓ : ContinuousOn Γ s) :
    IsAnalyticContinuationAlong (fun t => HolomorphicPresheaf.repFun (Γ t))
      (fun t => (Γ t).base) s := by
  refine (isAnalyticContinuationAlong_iff_continuousOn_germPoint
    ((TopCat.Presheaf.EtaleSpace.continuous_base holomorphicPresheaf).comp_continuousOn hΓ)
    (fun t _ => HolomorphicPresheaf.analyticAt_repFun (Γ t))).mpr ?_
  simpa only [Function.comp_apply, HolomorphicPresheaf.germPoint_repFun] using hΓ

/-! ### Monodromy -/

/-- **The monodromy theorem, in étalé-space form.** If the rows `h (t, ·)` of a homotopy rel
endpoints of paths in `ℂ` all lift continuously to the étalé space of holomorphic germs, from one
and the same starting germ, then all the lifts finish at the same germ.

This is Mathlib's `IsLocalHomeomorph.monodromy_theorem` applied to the étalé projection, whose two
hypotheses — that it is a local homeomorphism and that it is separated — are
`TauCeti.HolomorphicPresheaf.isLocalHomeomorph_base` and
`TauCeti.HolomorphicPresheaf.isSeparatedMap_base`. Combined with
`TauCeti.isAnalyticContinuationAlong_iff_continuousOn_germPoint`, which turns a continuation into
such a lift, it is the covering-space reading of `TauCeti.monodromy_theorem`. -/
theorem monodromy_theorem_etaleSpace {c₀ c₁ : C(I, ℂ)} (h : c₀.HomotopyRel c₁ {0, 1})
    (Γ : I → C(I, holomorphicPresheaf.EtaleSpace))
    (hlift : ∀ t x, (Γ t x).base = h (t, x)) (hstart : ∀ t, Γ t 0 = Γ 0 0) (t : I) :
    Γ t 1 = Γ 0 1 :=
  HolomorphicPresheaf.isLocalHomeomorph_base.monodromy_theorem
    HolomorphicPresheaf.isSeparatedMap_base h Γ hlift hstart t

end TauCeti
