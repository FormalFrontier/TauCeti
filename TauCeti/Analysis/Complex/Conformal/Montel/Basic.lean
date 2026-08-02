/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Montel.Precompact
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Montel's selection theorem

A locally bounded family of holomorphic functions on an open set `Ω ⊆ ℂ` is a normal family: every
sequence drawn from it has a subsequence converging locally uniformly on `Ω`, and the limit is
again holomorphic. This is the **Montel selection** component of layer **L1 (normal families /
Montel)** of the conformal-mapping roadmap, and the compactness engine the Riemann mapping theorem
runs on. The other component L1 lists, Vitali's theorem, is proved in `Conformal/Vitali.lean`,
which applies the selection theorem below.

The compactness this runs on is `Conformal/Montel/Precompact.lean`: the restricted family is
relatively compact in `C(↥Ω, ℂ)` with its compact-open topology, and there it is *equivalent* to
local boundedness. What is added here is the passage from that compactness to a convergent
subsequence, and the identification of the limit.

An open subset of `ℂ` is locally compact and second countable, hence σ-compact and so hemicompact —
a countable cofinal family of compacts — which is what makes the compact-open topology on
`C(↥Ω, ℂ)` first countable (local compactness alone would not suffice), and
`IsCompact.tendsto_subseq` extracts a convergent subsequence. Finally
`ContinuousMap.tendsto_iff_tendstoLocallyUniformly` turns compact-open convergence into locally
uniform convergence, and `TendstoLocallyUniformlyOn.differentiableOn` gives holomorphy of the limit.

No compact exhaustion or diagonal argument is needed: Mathlib's Arzelà–Ascoli framework, invoked
in `Conformal/Montel/Precompact.lean`, subsumes both.

## Main results

* `TauCeti.montel` — a locally bounded family of holomorphic functions on an open set has a
  locally uniformly convergent subsequence, with holomorphic limit.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0–L3
material overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
which proves a Montel equicontinuity statement internally as a private lemma. **This file is
therefore a temporary shim**: once the corresponding Mathlib results land, this statement should be
backed by them — or deleted and its consumers refactored — rather than maintained as an independent
re-proof. What Tau Ceti adds at L1 is named, discoverable API, not first proof.

Note this is the **analytic** normal-families theorem; it is deliberately not routed through
Mathlib's `Analysis/LocallyConvex/Montel.lean` (`MontelSpace`), which is an unrelated notion.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
-/

public section

open Complex Metric Filter Topology Set BoundedContinuousFunction

namespace TauCeti

variable {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}

/-- **Montel's selection theorem.** A locally bounded family of holomorphic functions on an open
set `Ω ⊆ ℂ` is normal: every sequence from it has a subsequence converging locally uniformly on
`Ω`, and the limit is holomorphic.

The local boundedness hypothesis cannot be dropped: on any *nonempty* open `Ω`, the holomorphic
family `F n z = n` has no locally uniformly convergent subsequence. (On `Ω = ∅` the conclusion is
vacuous, so nonemptiness is needed for the counterexample.) -/
theorem montel (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hb : IsLocallyBoundedOn F Ω) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧ DifferentiableOn ℂ g Ω ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop Ω := by
  classical
  haveI : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  set f : ℕ → C(Ω, ℂ) := fun n => ⟨Ω.domRestrict (F n), ((hF n).continuousOn).domRestrict⟩
  -- The relative compactness of the restricted family, from `Conformal/Montel/Precompact.lean`.
  have hcpt : IsCompact (closure (Set.range f)) :=
    isCompact_closure_range_of_isLocallyBoundedOn hΩ hF hb fun _ => rfl
  obtain ⟨a, -, φ, hφ, hconv⟩ := hcpt.tendsto_subseq (x := f) fun n => subset_closure ⟨n, rfl⟩
  -- Compact-open convergence is locally uniform convergence; extend the limit off `Ω` by zero.
  have hlim : ((fun z => if hz : z ∈ Ω then a ⟨z, hz⟩ else 0) ∘ (Subtype.val : Ω → ℂ))
      = fun x : Ω => a x := by
    funext x
    simp [x.2]
  have hconvOn : TendstoLocallyUniformlyOn (fun n => F (φ n))
      (fun z => if hz : z ∈ Ω then a ⟨z, hz⟩ else 0) atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hlim]
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv
  exact ⟨φ, _, hφ, hconvOn.differentiableOn (Eventually.of_forall fun n => hF (φ n)) hΩ, hconvOn⟩

end TauCeti
