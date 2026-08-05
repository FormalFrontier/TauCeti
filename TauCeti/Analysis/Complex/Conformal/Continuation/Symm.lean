/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Continuation.Trans

/-!
# Analytic continuation along a reversed path

`Continuation/Basic.lean` carries a holomorphic germ along a single path and proves the result
determined by the initial germ; `Continuation/Trans.lean` concatenates two continuations and
restricts a continuation along a concatenation to its factors. This file supplies the remaining
operation of the calculus: **reversal**. Continuing along `p` and then continuing the germ so
reached back along `p.symm` returns the germ one started from, so the continuation relation on
germs is symmetric, not merely reflexive and transitive.

## The reversed family

Reversal costs nothing at the level of `TauCeti.IsAnalyticContinuationAlong`: reading the family
`F` backwards, as `F ∘ σ`, is a reparametrisation of the parameter interval by the central
symmetry `σ`, and `TauCeti.IsAnalyticContinuationAlong.reparam` already transports a continuation
along any reparametrisation. What `TauCeti.IsAnalyticContinuationAlong.symm` adds is to state the
result against `Path.symm` rather than against the composite `⇑p ∘ σ`, which is the form the
`Path`-level calculus of `Continuation/Trans.lean` consumes and the form in which the comparisons
below are stated.

## Reversal inverts continuation

The mathematical content is the comparison
`TauCeti.IsAnalyticContinuationAlong.eventuallyEq_of_symm`: *any* continuation `G` along `p.symm`
that starts at the germ `F` delivers at `b` ends at the germ `F` started from at `a`. This is
uniqueness of continuation along a fixed path (`TauCeti.IsAnalyticContinuationAlong.eventuallyEq`)
applied to the two continuations `G` and `F ∘ σ` along `p.symm`, which agree at the initial
parameter time; the hypothesis is on `G`'s initial germ alone, so nothing forces `G` to *be* the
reversal of `F`.

Combined with the restriction theorems of `Continuation/Trans.lean` this gives the monodromy of a
backtracking loop directly, without appealing to the monodromy theorem: a continuation along
`p.trans p.symm` carries the same germ at both ends
(`TauCeti.IsAnalyticContinuationAlong.eventuallyEq_of_trans_symm`). Reading a continuation along
the concatenation on its two halves produces a continuation along `p` and one along `p.symm` that
are *literally the same family* at the junction parameter, so the comparison applies with the
matching hypothesis discharged by `rfl`.

## Continuability travels both ways

`TauCeti.continuesInside_of_isAnalyticContinuationAlong` (`Continuation/Trans.lean`) moves the
base point of `TauCeti.ContinuesInside` forward along a path of the domain. Reversal supplies the
converse and hence the equivalence
`TauCeti.continuesInside_iff_of_isAnalyticContinuationAlong`: two germs joined by a continuation
inside `U` continue inside `U` together, or neither does. So the hypothesis of the monodromy
theorem for a simply connected domain (`Conformal/GlobalBranch.lean`) is a property of the branch
being carried and of the domain, unattached to any distinguished point of the branch.

## Main results

* `TauCeti.IsAnalyticContinuationAlong.symm` — **continuations reverse**: reading a continuation
  along `p` backwards is a continuation along `p.symm`.
* `TauCeti.continuesAlong_symm` — the germ-level form: the germ delivered at the far end of `p`
  continues along `p.symm`.
* `TauCeti.IsAnalyticContinuationAlong.eventuallyEq_of_symm` — **reversal inverts continuation**:
  a continuation along `p.symm` starting from the germ delivered by a continuation along `p` ends
  at the germ that continuation started from.
* `TauCeti.ContinuesAlong.trans_symm` — a germ that continues along `p` continues along the round
  trip `p.trans p.symm`.
* `TauCeti.IsAnalyticContinuationAlong.eventuallyEq_of_trans_symm` — **a backtracking loop has
  trivial monodromy**: a continuation along `p.trans p.symm` ends at the germ it began with.
* `TauCeti.continuesInside_iff_of_isAnalyticContinuationAlong` — **continuability inside a domain
  is a property of the branch**: germs joined by a continuation inside `U` continue inside `U`
  together.

## Coordination with upstream Mathlib

This is basic API for layer **L4** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`), analytic continuation and the reflection principle.
Mathlib has no analytic continuation along a path, and L4 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself. So
nothing here is a shim under the roadmap's shim-deletion clause, which covers L0–L3 only. The
reversal `Path.symm` and the central symmetry `unitInterval.symm` are consumed from Mathlib rather
than rebuilt, and no Mathlib source is vendored.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §2–3.
-/

public section

namespace TauCeti

open Filter Set Topology unitInterval

section Symm

variable {a b : ℂ} {f₀ : ℂ → ℂ} {F G H : I → ℂ → ℂ}

/-! ### The reversed continuation -/

/-- **Continuations reverse.** Reading the family `F` backwards, as `F ∘ σ`, turns a continuation
along `p` into a continuation along the reversed path `p.symm`.

Reversing the parameter is a reparametrisation, so
`TauCeti.IsAnalyticContinuationAlong.reparam` does the work; the point of naming the special case
is that the conclusion is stated against `Path.symm`, so that it composes with the concatenation
calculus of `Continuation/Trans.lean`. Since `σ` is a bijection of the parameter interval, no part
of the path is dropped and the statement is an equivalence in substance, its converse being this
theorem applied to `p.symm` together with `Path.symm_symm`. -/
theorem IsAnalyticContinuationAlong.symm {p : Path a b}
    (hF : IsAnalyticContinuationAlong F (⇑p) univ) :
    IsAnalyticContinuationAlong (F ∘ σ) (⇑p.symm) univ :=
  (hF.reparam continuous_symm.continuousOn (mapsTo_univ _ _)).congr_path fun _ _ => rfl

/-- **The germ delivered at the far end continues back.** If `F` continues along `p`, then the
germ `F 1` it delivers at the endpoint of `p` continues along `p.symm`, the reversed family being
the witness. This is the germ-level reading of `TauCeti.IsAnalyticContinuationAlong.symm`, and the
counterpart for reversal of `TauCeti.continuesAlong_trans`. -/
theorem continuesAlong_symm {p : Path a b} (hF : IsAnalyticContinuationAlong F (⇑p) univ) :
    ContinuesAlong (F 1) (⇑p.symm) := by
  refine continuesAlong_iff_exists.mpr ⟨F ∘ σ, hF.symm, ?_⟩
  rw [p.symm.source]
  simp only [Function.comp_apply, symm_zero]
  exact .rfl

/-- **Reversal inverts continuation.** Let `F` be a continuation along `p` and let `G` be *any*
continuation along the reversed path `p.symm` whose initial germ at `b` is the germ `F` delivers
there. Then the germ `G` delivers at `a` is the germ `F` started from.

So continuing a germ out along a path and back along the same path in reverse returns the germ,
whichever continuation is used for the return leg: `G` is only assumed to start at the right germ,
not to be built from `F`. The proof compares `G` with the reversed family `F ∘ σ`, which
`TauCeti.IsAnalyticContinuationAlong.symm` makes a continuation along `p.symm` as well; the two
agree at the initial parameter time, so uniqueness along a fixed path
(`TauCeti.IsAnalyticContinuationAlong.eventuallyEq`) makes them agree at the terminal one. -/
theorem IsAnalyticContinuationAlong.eventuallyEq_of_symm {p : Path a b}
    (hF : IsAnalyticContinuationAlong F (⇑p) univ)
    (hG : IsAnalyticContinuationAlong G (⇑p.symm) univ) (hFG : G 0 =ᶠ[𝓝 b] F 1) :
    G 1 =ᶠ[𝓝 a] F 0 := by
  have h0 : G 0 =ᶠ[𝓝 (p.symm 0)] (F ∘ σ) 0 := by
    rw [p.symm.source]
    simpa only [Function.comp_apply, symm_zero] using hFG
  have h1 := hG.eventuallyEq hF.symm isPreconnected_univ (mem_univ 0) (mem_univ 1) h0
  rwa [p.symm.target, Function.comp_apply, symm_one] at h1

/-! ### The round trip -/

/-- **A germ that continues along a path continues along the round trip.** Concatenating `p` with
its reversal continues the germ of `f₀`, by `TauCeti.continuesAlong_trans` fed with
`TauCeti.continuesAlong_symm`. -/
theorem ContinuesAlong.trans_symm {p : Path a b} (h : ContinuesAlong f₀ (⇑p)) :
    ContinuesAlong f₀ (⇑(p.trans p.symm)) := by
  obtain ⟨F, hF, hF0⟩ := continuesAlong_iff_exists.mp h
  rw [p.source] at hF0
  exact continuesAlong_trans hF hF0 (continuesAlong_symm hF)

/-- **A backtracking loop has trivial monodromy.** A continuation along `p.trans p.symm` carries
the same germ at both ends of the parameter interval.

The loop `p.trans p.symm` is null-homotopic, so `TauCeti.monodromy_theorem_of_homotopy_refl`
also covers it — but only under the far stronger hypothesis that the germ continues along *every*
path of a null-homotopy of the loop. Here one continuation along the loop itself is enough, and
the proof uses neither a homotopy nor compactness. Restricting it to the two halves of the
concatenation
(`TauCeti.IsAnalyticContinuationAlong.left_of_trans`, `.right_of_trans`) gives a continuation
along `p` and one along `p.symm` which are the same family read at the same junction parameter, so
`TauCeti.IsAnalyticContinuationAlong.eventuallyEq_of_symm` applies with its matching hypothesis
discharged by `rfl`. -/
theorem IsAnalyticContinuationAlong.eventuallyEq_of_trans_symm {p : Path a b}
    (hH : IsAnalyticContinuationAlong H (⇑(p.trans p.symm)) univ) :
    H 1 =ᶠ[𝓝 a] H 0 := by
  -- The two halves, as continuations along `p` and along `p.symm`.
  have hleft := hH.left_of_trans
  have hright := hH.right_of_trans
  -- The two halves read the same parameter of `H` at the junction.
  have hjunction : projIcc (0 : ℝ) 1 zero_le_one ((((0 : I) : ℝ) + 1) / 2)
      = projIcc (0 : ℝ) 1 zero_le_one (((1 : I) : ℝ) / 2) := by
    ext; norm_num [coe_projIcc]
  have hFG : (fun t : I => H (projIcc (0 : ℝ) 1 zero_le_one (((t : ℝ) + 1) / 2))) 0
      =ᶠ[𝓝 b] (fun t : I => H (projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / 2))) 1 := by
    simp only [hjunction]
    exact .rfl
  have h := hleft.eventuallyEq_of_symm hright hFG
  -- The outer parameters are the endpoints of the concatenation.
  have hone : projIcc (0 : ℝ) 1 zero_le_one ((((1 : I) : ℝ) + 1) / 2) = 1 := by
    ext; norm_num [coe_projIcc]
  have hzero : projIcc (0 : ℝ) 1 zero_le_one (((0 : I) : ℝ) / 2) = 0 := by
    ext; norm_num [coe_projIcc]
  simpa only [hone, hzero] using h

/-! ### Continuability inside a domain, both ways -/

/-- **Continuability inside a domain is a property of the branch.** If `F` continues the germ of
`f₀` at `z₀` along a path `p` of `U` to the germ `F 1` at `z₁`, then that germ continues
inside `U` exactly when the germ of `f₀` does.

The `←` direction is `TauCeti.continuesInside_of_isAnalyticContinuationAlong`, which moves the
base point forward along `p`; the `→` direction moves it back along `p.symm`, carrying the germ
`F 1` to the germ `F 0`, which is the germ of `f₀`. So neither endpoint of the path is
distinguished: `TauCeti.ContinuesInside`, the hypothesis of the monodromy theorem for a simply
connected domain, depends only on the domain and on the branch, and any point the branch reaches
inside `U` may be used as its base point. -/
theorem continuesInside_iff_of_isAnalyticContinuationAlong {U : Set ℂ} {z₀ z₁ : ℂ}
    {p : Path z₀ z₁} (hpU : ∀ t, p t ∈ U) (hF : IsAnalyticContinuationAlong F (⇑p) univ)
    (hF0 : F 0 =ᶠ[𝓝 z₀] f₀) :
    ContinuesInside (F 1) U z₁ ↔ ContinuesInside f₀ U z₀ := by
  refine ⟨fun h => ?_, fun h => continuesInside_of_isAnalyticContinuationAlong h hpU hF hF0⟩
  have hstart : (F ∘ σ) 0 =ᶠ[𝓝 z₁] F 1 := by
    simp only [Function.comp_apply, symm_zero]
    exact .rfl
  have hback := continuesInside_of_isAnalyticContinuationAlong h
    (p := p.symm) (fun t => hpU (σ t)) hF.symm hstart
  rw [Function.comp_apply, symm_one] at hback
  exact hback.congr hF0

end Symm

end TauCeti
