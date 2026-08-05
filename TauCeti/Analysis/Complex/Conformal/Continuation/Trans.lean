/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic

/-!
# Analytic continuation along a concatenation of paths

`Continuation/Basic.lean` carries a holomorphic germ along a single path and proves that the
result is determined by the initial germ. This file supplies the other half of the basic calculus
of analytic continuation: continuing along `γ` and then along `δ` is continuing along the
concatenated path `γ.trans δ`, and conversely a continuation along a concatenation restricts to
one along each factor.

## The gluing engine

Both directions rest on two general facts about `TauCeti.IsAnalyticContinuationAlong`, proved
here for an arbitrary parameter space:

* only the values of the path on the parameter set matter
  (`TauCeti.IsAnalyticContinuationAlong.congr_path`), the companion of the germ-level
  `TauCeti.IsAnalyticContinuationAlong.congr` already available;
* one family of germs that continues over each of two **closed** parameter sets continues over
  their union (`TauCeti.IsAnalyticContinuationAlong.union`).

Closedness is what makes the union statement true and is not a convenience: the condition
`∀ᶠ u in 𝓝[s] t, …` defining a continuation is vacuous at a parameter time `t` outside the
closure of `s`, so a set may be enlarged by points it does not cling to for free, and the union
of two closed sets adds no new clinging. Without it the germ carried on one piece would be
unrelated to the germ carried on the other at a shared limit point.

The restriction direction needs no new engine at all: reading `γ` as the first half of
`γ.trans δ` is a reparametrisation, and `TauCeti.IsAnalyticContinuationAlong.reparam` already
transports a continuation along any reparametrisation.

## The concatenated family

The family of germs carried along `γ.trans δ` is written down explicitly, as
`TauCeti.transFamily`: on the first half of the parameter interval it is the family carried along
`γ`, read at twice the parameter, and on the second half the one carried along `δ`. The two halves
are compared at the junction, where `TauCeti.transFamily` takes the value coming from `γ`; the
hypothesis of `TauCeti.IsAnalyticContinuationAlong.trans` is exactly that the germ `γ` delivers
there agrees with the germ `δ` starts from.

## Moving the base point

The pay-off is that continuability inside a domain does not depend on the base point:
`TauCeti.continuesInside_of_isAnalyticContinuationAlong` says that if a germ continues inside `U`
from `z₀` — the hypothesis the monodromy theorem for a simply connected domain runs on
(`Conformal/GlobalBranch.lean`) — and is continued along a path inside `U` to a germ at `z₁`, then
that germ continues inside `U` from `z₁`. Concatenation supplies the paths issuing from `z₁`, and
restriction plus uniqueness of continuation along a fixed path identify the germ reached halfway.

## Main results

* `TauCeti.IsAnalyticContinuationAlong.congr_path` — a continuation depends on the path only
  through its values on the parameter set.
* `TauCeti.IsAnalyticContinuationAlong.union` — continuations glue over two closed parameter sets.
* `TauCeti.transFamily` — the family of germs carried along a concatenation.
* `TauCeti.IsAnalyticContinuationAlong.trans` — **continuations concatenate**: two continuations
  whose germs match at the junction assemble into a continuation along `γ.trans δ`.
* `TauCeti.continuesAlong_trans` — the germ-level form: a germ that continues along `γ` to a germ
  that continues along `δ` continues along `γ.trans δ`.
* `TauCeti.continuesInside_of_isAnalyticContinuationAlong` — **continuability inside a domain
  travels with the germ**: continuing inside `U` along a path of `U` again continues inside `U`.

## Coordination with upstream Mathlib

This is basic API for layer **L4** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`), analytic continuation and the reflection
principle. Mathlib has no analytic continuation along a path, and L4 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself. So
nothing here is a shim under the roadmap's shim-deletion clause, which covers L0–L3 only. The
`Path.trans` concatenation and its `Path.extend` calculus are consumed from Mathlib rather than
rebuilt.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §2–3.
-/

public section

namespace TauCeti

open Filter Set Topology unitInterval

/-! ### Gluing continuations over a union of parameter sets -/

section Glue

variable {X : Type*} [TopologicalSpace X] {f : X → ℂ → ℂ} {γ γ' : X → ℂ} {s t : Set X}

namespace IsAnalyticContinuationAlong

/-- **A continuation depends on the path only through its values on the parameter set.** This is
the path-level companion of `TauCeti.IsAnalyticContinuationAlong.congr`, which says the same for
the family of germs. -/
theorem congr_path (hf : IsAnalyticContinuationAlong f γ s) (h : EqOn γ' γ s) :
    IsAnalyticContinuationAlong f γ' s where
  continuousOn := hf.continuousOn.congr h
  analyticAt u hu := by rw [h hu]; exact hf.analyticAt u hu
  locallyEq u hu := by
    filter_upwards [hf.locallyEq u hu, self_mem_nhdsWithin] with v hv hvs
    rwa [h hvs]

/-- **Continuations glue over closed parameter sets.** One family of germs that is a continuation
along `γ` over each of two closed parameter sets is a continuation over their union.

Closedness is essential rather than cosmetic. At a parameter time outside the closure of `s` the
locality condition over `s` is vacuous, so it says nothing about how the germ carried there
relates to the germs carried on `s`; taking `s` and `t` closed makes every parameter time of the
union cling only to the piece it already lies in. -/
theorem union (hf : IsAnalyticContinuationAlong f γ s) (hg : IsAnalyticContinuationAlong f γ t)
    (hs : IsClosed s) (ht : IsClosed t) : IsAnalyticContinuationAlong f γ (s ∪ t) where
  continuousOn := hf.continuousOn.union_of_isClosed hg.continuousOn hs ht
  analyticAt u hu := hu.elim (hf.analyticAt u) (hg.analyticAt u)
  locallyEq u _ := by
    rw [nhdsWithin_union, eventually_sup]
    constructor
    · by_cases hus : u ∈ s
      · exact hf.locallyEq u hus
      · have hcl : u ∉ closure s := by rwa [hs.closure_eq]
        rw [notMem_closure_iff_nhdsWithin_eq_bot.mp hcl]
        exact eventually_bot
    · by_cases hut : u ∈ t
      · exact hg.locallyEq u hut
      · have hcl : u ∉ closure t := by rwa [ht.closure_eq]
        rw [notMem_closure_iff_nhdsWithin_eq_bot.mp hcl]
        exact eventually_bot

end IsAnalyticContinuationAlong

end Glue

/-! ### The family of germs carried along a concatenation -/

section Trans

variable {a b c : ℂ} {f₀ : ℂ → ℂ} {F G : I → ℂ → ℂ}

/-- The family of germs carried along a concatenation `γ.trans δ` of paths, assembled from the
family `F` carried along `γ` and the family `G` carried along `δ`: on the first half of the
parameter interval it is `F`, read at twice the parameter, and on the second half it is `G`, read
at twice the parameter minus one. The junction time `1 / 2` is assigned the germ coming from `F`,
matching the convention of `Path.trans`. -/
noncomputable def transFamily (F G : I → ℂ → ℂ) (u : I) : ℂ → ℂ :=
  if (u : ℝ) ≤ 1 / 2 then F (projIcc 0 1 zero_le_one (2 * u))
  else G (projIcc 0 1 zero_le_one (2 * u - 1))

/-- On the first half of the parameter interval the concatenated family is the first family. -/
theorem transFamily_of_le_half (F G : I → ℂ → ℂ) {u : I} (hu : (u : ℝ) ≤ 1 / 2) :
    transFamily F G u = F (projIcc 0 1 zero_le_one (2 * u)) :=
  if_pos hu

/-- Strictly past the junction the concatenated family is the second family. -/
theorem transFamily_of_half_lt (F G : I → ℂ → ℂ) {u : I} (hu : 1 / 2 < (u : ℝ)) :
    transFamily F G u = G (projIcc 0 1 zero_le_one (2 * u - 1)) :=
  if_neg (not_le.mpr hu)

@[simp]
theorem transFamily_zero (F G : I → ℂ → ℂ) : transFamily F G 0 = F 0 := by
  rw [transFamily_of_le_half F G (by norm_num)]
  congr 1
  ext
  norm_num [coe_projIcc]

@[simp]
theorem transFamily_one (F G : I → ℂ → ℂ) : transFamily F G 1 = G 1 := by
  rw [transFamily_of_half_lt F G (by norm_num)]
  congr 1
  ext
  norm_num [coe_projIcc]

/-- **Continuations concatenate.** If `F` continues a germ along `p`, `G` continues a germ along
`q`, and the germ `F` delivers at the end of `p` is the germ `G` starts from, then
`TauCeti.transFamily F G` is a continuation along the concatenated path `p.trans q`.

Its germ at parameter time `0` is that of `F 0` and its germ at time `1` is that of `G 1`
(`TauCeti.transFamily_zero`, `TauCeti.transFamily_one`), so continuing along `p` and then along
`q` carries the initial germ of `F` to the terminal germ of `G`. -/
theorem IsAnalyticContinuationAlong.trans {p : Path a b} {q : Path b c}
    (hF : IsAnalyticContinuationAlong F (⇑p) univ)
    (hG : IsAnalyticContinuationAlong G (⇑q) univ) (hFG : F 1 =ᶠ[𝓝 b] G 0) :
    IsAnalyticContinuationAlong (transFamily F G) (⇑(p.trans q)) univ := by
  have hcoe : Continuous fun u : I => (u : ℝ) := continuous_subtype_val
  have hclosed₁ : IsClosed {u : I | (u : ℝ) ≤ 1 / 2} := isClosed_le hcoe continuous_const
  have hclosed₂ : IsClosed {u : I | 1 / 2 ≤ (u : ℝ)} := isClosed_le continuous_const hcoe
  have hunion : {u : I | (u : ℝ) ≤ 1 / 2} ∪ {u : I | 1 / 2 ≤ (u : ℝ)} = univ :=
    eq_univ_of_forall fun u => (le_total (u : ℝ) (1 / 2)).imp id id
  -- The first half of the concatenation is `p`, reparametrised by doubling.
  have hφ₁ : Continuous fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u) :=
    continuous_projIcc.comp (by fun_prop)
  have h₁ := hF.reparam (φ := fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u))
    (s' := {u : I | (u : ℝ) ≤ 1 / 2}) hφ₁.continuousOn (mapsTo_univ _ _)
  have hpath₁ : EqOn (⇑(p.trans q))
      ((⇑p) ∘ fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u))
      {u : I | (u : ℝ) ≤ 1 / 2} := by
    intro u hu
    calc (p.trans q) u
        = (p.trans q).extend (u : ℝ) := ((p.trans q).extend_extends' u).symm
      _ = p.extend (2 * u) := Path.extend_trans_of_le_half p q hu
      _ = p (projIcc (0 : ℝ) 1 zero_le_one (2 * u)) := rfl
  have h₁' : IsAnalyticContinuationAlong (transFamily F G) (⇑(p.trans q))
      {u : I | (u : ℝ) ≤ 1 / 2} :=
    (h₁.congr_path hpath₁).congr fun u hu => by
      rw [transFamily_of_le_half F G hu]
      exact .rfl
  -- The second half of the concatenation is `q`, reparametrised by doubling and shifting.
  have hφ₂ : Continuous fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1) :=
    continuous_projIcc.comp (by fun_prop)
  have h₂ := hG.reparam (φ := fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1))
    (s' := {u : I | 1 / 2 ≤ (u : ℝ)}) hφ₂.continuousOn (mapsTo_univ _ _)
  have hpath₂ : EqOn (⇑(p.trans q))
      ((⇑q) ∘ fun u : I => projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1))
      {u : I | 1 / 2 ≤ (u : ℝ)} := by
    intro u hu
    calc (p.trans q) u
        = (p.trans q).extend (u : ℝ) := ((p.trans q).extend_extends' u).symm
      _ = q.extend (2 * u - 1) := Path.extend_trans_of_half_le p q hu
      _ = q (projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1)) := rfl
  have h₂' : IsAnalyticContinuationAlong (transFamily F G) (⇑(p.trans q))
      {u : I | 1 / 2 ≤ (u : ℝ)} := by
    refine (h₂.congr_path hpath₂).congr fun u hu => ?_
    have hu' : 1 / 2 ≤ (u : ℝ) := hu
    rcases eq_or_lt_of_le hu' with heq | hlt
    · -- At the junction the two halves are compared through the matching hypothesis.
      have e₁ : projIcc (0 : ℝ) 1 zero_le_one (2 * u) = 1 := by
        ext; rw [coe_projIcc, ← heq]; norm_num
      have e₀ : projIcc (0 : ℝ) 1 zero_le_one (2 * u - 1) = 0 := by
        ext; rw [coe_projIcc, ← heq]; norm_num
      have hpt : (p.trans q) u = b := by rw [hpath₂ hu]; simp [e₀]
      rw [transFamily_of_le_half F G heq.ge, e₁, hpt]
      simpa [e₀] using hFG
    · rw [transFamily_of_half_lt F G hlt]
      exact .rfl
  have hglue := h₁'.union h₂' hclosed₁ hclosed₂
  rwa [hunion] at hglue

/-- **Continuability is transitive along a concatenation.** If `F` continues the germ of `f₀`
along `p`, and the germ `F 1` it delivers at the end of `p` continues along `q`, then `f₀`
continues along `p.trans q`. -/
theorem continuesAlong_trans {p : Path a b} {q : Path b c}
    (hF : IsAnalyticContinuationAlong F (⇑p) univ) (hF0 : F 0 =ᶠ[𝓝 a] f₀)
    (hq : ContinuesAlong (F 1) (⇑q)) : ContinuesAlong f₀ (⇑(p.trans q)) := by
  obtain ⟨G, hG, hG0⟩ := continuesAlong_iff_exists.mp hq
  rw [q.source] at hG0
  refine continuesAlong_iff_exists.mpr ⟨transFamily F G, hF.trans hG hG0.symm, ?_⟩
  rw [transFamily_zero, (p.trans q).source]
  exact hF0

/-! ### Restricting a continuation to the factors of a concatenation -/

/-- Reading a continuation along `p.trans q` on the first half of the parameter interval gives a
continuation along `p`. -/
private theorem isAnalyticContinuationAlong_comp_half_left {H : I → ℂ → ℂ} {p : Path a b}
    {q : Path b c} (h : IsAnalyticContinuationAlong H (⇑(p.trans q)) univ) :
    IsAnalyticContinuationAlong (fun t : I => H (projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2)))
      (⇑p) univ := by
  have hψ : Continuous fun t : I => projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2) :=
    continuous_projIcc.comp (by fun_prop)
  refine (h.reparam (φ := fun t : I => projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2))
    (s' := univ) hψ.continuousOn (mapsTo_univ _ _)).congr_path fun t _ => ?_
  have ht : (t : ℝ) / 2 ≤ 1 / 2 := by linarith [t.2.2]
  calc (p : I → ℂ) t
      = p.extend (t : ℝ) := (p.extend_extends' t).symm
    _ = p.extend (2 * ((t : ℝ) / 2)) := by ring_nf
    _ = (p.trans q).extend ((t : ℝ) / 2) := (Path.extend_trans_of_le_half p q ht).symm
    _ = (p.trans q) (projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2)) := rfl

/-- Reading a continuation along `p.trans q` on the second half of the parameter interval gives a
continuation along `q`. -/
private theorem isAnalyticContinuationAlong_comp_half_right {H : I → ℂ → ℂ} {p : Path a b}
    {q : Path b c} (h : IsAnalyticContinuationAlong H (⇑(p.trans q)) univ) :
    IsAnalyticContinuationAlong
      (fun t : I => H (projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2))) (⇑q) univ := by
  have hψ : Continuous fun t : I => projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2) :=
    continuous_projIcc.comp (by fun_prop)
  refine (h.reparam (φ := fun t : I => projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2))
    (s' := univ) hψ.continuousOn (mapsTo_univ _ _)).congr_path fun t _ => ?_
  have ht : 1 / 2 ≤ ((t : ℝ) + 1) / 2 := by linarith [t.2.1]
  calc (q : I → ℂ) t
      = q.extend (t : ℝ) := (q.extend_extends' t).symm
    _ = q.extend (2 * (((t : ℝ) + 1) / 2) - 1) := by ring_nf
    _ = (p.trans q).extend (((t : ℝ) + 1) / 2) := (Path.extend_trans_of_half_le p q ht).symm
    _ = (p.trans q) (projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2)) := rfl

/-! ### Continuability inside a domain travels with the germ -/

/-- **Continuability inside a domain does not depend on the base point.** If the germ of `f₀` at
`z₀` continues inside `U`, and `F` continues it along a path `p` from `z₀` to `z₁` that stays in
`U`, then the germ `F 1` delivered at `z₁` continues inside `U` in its own right.

So `TauCeti.ContinuesInside`, the hypothesis of the monodromy theorem for a simply connected
domain, is a condition on the domain and on the branch being carried, not on the point one starts
from: a path issuing from `z₁` is continued by prefixing `p` to it, and uniqueness of continuation
along `p` identifies the germ reached halfway with `F 1`. -/
theorem continuesInside_of_isAnalyticContinuationAlong {U : Set ℂ} {z₀ z₁ : ℂ}
    (H : ContinuesInside f₀ U z₀) {p : Path z₀ z₁} (hpU : ∀ t, p t ∈ U)
    (hF : IsAnalyticContinuationAlong F (⇑p) univ) (hF0 : F 0 =ᶠ[𝓝 z₀] f₀) :
    ContinuesInside (F 1) U z₁ := by
  refine ContinuesInside.of_forall fun d hd hdU hd0 => ?_
  obtain ⟨e, q, rfl⟩ : ∃ (e : ℂ) (q : Path z₁ e), (⇑q : I → ℂ) = d :=
    ⟨d 1, ⟨⟨d, hd⟩, hd0, rfl⟩, rfl⟩
  have hpq : ∀ t, (p.trans q) t ∈ U := by
    intro t
    have hmem : (p.trans q) t ∈ range (p.trans q) := mem_range_self t
    rw [Path.trans_range] at hmem
    rcases hmem with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs]; exact hpU s
    · rw [← hs]; exact hdU s
  obtain ⟨K, hK, hK0⟩ := continuesAlong_iff_exists.mp
    (H.continuesAlong (p.trans q).continuous hpq (p.trans q).source)
  rw [(p.trans q).source] at hK0
  -- The first factor: the germ reached at the junction is the one `F` delivers.
  have hleft := isAnalyticContinuationAlong_comp_half_left hK
  have hzero : projIcc (0 : ℝ) 1 zero_le_one (((0 : I) : ℝ) / 2) = 0 := by
    ext; norm_num [coe_projIcc]
  have hstart : (fun t : I => K (projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2))) 0
      =ᶠ[𝓝 (p 0)] F 0 := by
    simp only [hzero]
    rw [p.source]
    exact hK0.trans hF0.symm
  have hmid := hleft.eventuallyEq hF isPreconnected_univ (mem_univ 0) (mem_univ 1) hstart
  rw [p.target] at hmid
  -- The second factor: it starts at the junction germ, hence at `F 1`.
  have hright := isAnalyticContinuationAlong_comp_half_right hK
  have hjunction : projIcc (0 : ℝ) 1 zero_le_one ((((0 : I) : ℝ) + 1) / 2)
      = projIcc (0 : ℝ) 1 zero_le_one (((1 : I) : ℝ) / 2) := by
    ext; norm_num [coe_projIcc]
  refine continuesAlong_iff_exists.mpr
    ⟨fun t : I => K (projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2)), hright, ?_⟩
  rw [q.source]
  simpa only [hjunction] using hmid

end Trans

end TauCeti
