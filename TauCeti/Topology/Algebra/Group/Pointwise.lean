/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Closures and pointwise quotients

Mathlib relates `closure` to a pointwise product when one factor is *open* — `IsOpen.mul_closure`
and its neighbours in `Mathlib/Topology/Algebra/Group/Pointwise.lean` — and to a pointwise scalar
product when the action is jointly continuous, in `smul_set_closure_subset`. The containment for
division, which needs neither openness nor a group structure, is not there.

It is what a Baire argument needs. Such an argument produces a set whose *closure* has interior,
and the step from there to a neighbourhood of the identity runs through `D / D` for that closure
`D`; without this containment there is no way back from `closure s / closure t` to a closure.

## Main results

* `TauCeti.closure_div_closure_subset`, with its additive form
  `TauCeti.closure_sub_closure_subset`.
-/

public section

open Pointwise

namespace TauCeti

variable {G : Type*} [TopologicalSpace G] [Div G] [ContinuousDiv G]

/-- **Division carries closures into the closure of the quotient.** Neither set need be open,
unlike in the `IsOpen.mul_closure` family, and `G` need only carry a continuous division — no
group structure, and in particular no inverse. -/
@[to_additive /-- **Subtraction carries closures into the closure of the difference.** Neither set
need be open, and `G` need only carry a continuous subtraction — no group structure, and in
particular no negation. -/]
theorem closure_div_closure_subset (s t : Set G) : closure s / closure t ⊆ closure (s / t) :=
  calc closure s / closure t
      = (fun p : G × G ↦ p.1 / p.2) '' (closure s ×ˢ closure t) := by
        rw [Set.image_prod, Set.image2_div]
    _ = (fun p : G × G ↦ p.1 / p.2) '' closure (s ×ˢ t) := by rw [closure_prod_eq]
    _ ⊆ closure ((fun p : G × G ↦ p.1 / p.2) '' (s ×ˢ t)) :=
        image_closure_subset_closure_image (continuous_fst.div' continuous_snd)
    _ = closure (s / t) := by rw [Set.image_prod, Set.image2_div]

end TauCeti

end
