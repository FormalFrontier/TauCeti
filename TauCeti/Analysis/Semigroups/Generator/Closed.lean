/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Identity
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closedness of semigroup generators

This file proves that the infinitesimal generator of a strongly continuous semigroup on a real
Banach space is a closed `LinearPMap`. The proof uses the Laplace-transform resolvent: for any
parameter above a growth exponent, the generator graph is the equalizer

`R(lambda) (lambda x - y) = x`.

The forward implication is the resolvent left-inverse identity on the generator domain. The
reverse implication uses that the resolvent maps into the domain and is a right inverse to
`lambda I - A`. Since the resolvent is bounded, the equalizer is closed.

## Main results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.mem_generator_graph_iff_resolvent_eq`:
  membership in the generator graph is characterized by one resolvent equation.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.isClosed_generator`: the generator of every
  strongly continuous semigroup is closed.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Proposition II.1.4.
-/

public section

noncomputable section

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

/-- A pair `(x, y)` belongs to the graph of the generator precisely when applying an admissible
resolvent to `lambda x - y` recovers `x`.

This characterization presents the graph as the equalizer of two continuous maps and is also a
convenient elimination rule when a resolvent equation is easier to establish than domain
membership directly. -/
theorem mem_generator_graph_iff_resolvent_eq (S : StronglyContinuousSemigroup X)
    {omega M : ℝ} (hb : S.HasGrowthBound omega M) (lambda : ℝ) (hlambda : omega < lambda)
    (p : X × X) :
    p ∈ S.generator.graph ↔
      S.resolvent hb lambda hlambda (lambda • p.1 - p.2) = p.1 := by
  constructor
  · rw [LinearPMap.mem_graph_iff]
    rintro ⟨x, hx, hAx⟩
    let x' : S.domain := ⟨(x : X), by
      rw [← S.generator_domain]
      exact x.property⟩
    have hgen : S.generator ⟨(x' : X), by
        rw [S.generator_domain]
        exact x'.property⟩ = p.2 := by
      rw [← hAx]
    have hleft := S.resolventLeftInv hb lambda hlambda x'
    rw [hgen, hx] at hleft
    exact hleft
  · intro h
    let z : S.generator.domain :=
      ⟨S.resolvent hb lambda hlambda (lambda • p.1 - p.2),
        by
          rw [S.generator_domain]
          exact S.resolvent_mem_domain hb lambda hlambda _⟩
    have hz : (z : X) = p.1 := h
    rw [LinearPMap.mem_graph_iff]
    refine ⟨z, hz, ?_⟩
    have hright := S.resolventRightInv hb lambda hlambda (lambda • p.1 - p.2)
    have hright' : lambda • (z : X) - S.generator z = lambda • p.1 - p.2 := by
      simpa only [z] using hright
    calc
      S.generator z = lambda • (z : X) - (lambda • (z : X) - S.generator z) :=
        (sub_sub_cancel _ _).symm
      _ = lambda • p.1 - (lambda • p.1 - p.2) := by rw [hright', hz]
      _ = p.2 := sub_sub_cancel _ _

/-- The infinitesimal generator of a strongly continuous semigroup on a real Banach space is a
closed unbounded operator. -/
theorem isClosed_generator (S : StronglyContinuousSemigroup X) : S.generator.IsClosed := by
  obtain ⟨omega, M, hb⟩ := S.existsGrowthBound
  let lambda := omega + 1
  have hlambda : omega < lambda := by simp [lambda]
  rw [LinearPMap.IsClosed]
  have hgraph : (S.generator.graph : Set (X × X)) =
      {p | S.resolvent hb lambda hlambda (lambda • p.1 - p.2) = p.1} := by
    ext p
    exact S.mem_generator_graph_iff_resolvent_eq hb lambda hlambda p
  rw [hgraph]
  exact isClosed_eq
    ((S.resolvent hb lambda hlambda).continuous.comp
      ((continuous_fst.const_smul lambda).sub continuous_snd))
    continuous_fst

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
