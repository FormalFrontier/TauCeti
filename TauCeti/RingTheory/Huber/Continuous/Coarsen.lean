/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Continuous.OfCofinal
public import TauCeti.RingTheory.Valuation.Coarsen
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Continuity of a vertical generization

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Remark 7.11(2).**

A vertical generization `v/H` of a continuous valuation on a Huber ring is again continuous. The
cofinality half of the argument is topology-free and lives in
`TauCeti.RingTheory.Valuation.Coarsen` as `Valuation.cofinalValue_coarsenByUnits_restrict`.
Wedhorn states the hypothesis as `H ⊊ Γ_v`: the convex subgroup is proper **in the value group**,
not in the ambient codomain. That is why the coarsening here is applied to `v.restrict`, which is
the presentation of `v` on its own value group; `H ≠ ⊤` is then literally Wedhorn's properness.

Properness is not decoration. If `H` were all of `Γ_v` the coarsening would take only the values
`0` and `1`, so `{a | w a < w b}` would be the support of `v`, and continuity would force that
support to be open — which it need not be.

## Main results

* `Valuation.IsContinuous.coarsenByUnits_restrict`: the coarsening of a continuous valuation by a
  proper convex subgroup of its value group is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.11 and Corollary 1.21.
-/

public section

namespace Valuation

open TauCeti TauCeti.Huber MonoidWithZeroHom

variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Remark 7.11(2).** A vertical generization of a continuous valuation by a proper
convex subgroup of its value group is again continuous. -/
theorem IsContinuous.coarsenByUnits_restrict [IsTopologicalRing A] [IsHuberRing A]
    {v : Valuation A Γ₀} (hv : v.IsContinuous) {H : ConvexSubgroup (ValueGroup₀ (.ofClass v))ˣ}
    (hH : H ≠ ⊤) : (v.restrict.coarsenByUnits H).IsContinuous := by
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  obtain ⟨s, hs⟩ := P.fg_idealOfDefinition
  refine P.isContinuous_of_forall_cofinalValue _ hs (fun a ha ↦ ?_) fun t ht ↦ ?_
  · rw [coarsenByUnits_apply, ← map_one (coarsenMapOfValueGroup H)]
    exact coarsenMapOfValueGroup_monotone H
      ((v.isEquiv_restrict.isContinuous_iff.mp hv).lt_one_of_isTopologicallyNilpotent
        (P.isTopologicallyNilpotent_of_mem_idealOfDefinition ha)).le
  · exact cofinalValue_coarsenByUnits_restrict hH
      (hv.cofinalValue_of_isTopologicallyNilpotent
        (P.isTopologicallyNilpotent_of_mem_idealOfDefinition (hs ▸ Ideal.subset_span ht)))

end Valuation

end
