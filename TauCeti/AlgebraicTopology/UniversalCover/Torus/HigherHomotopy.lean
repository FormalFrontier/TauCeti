/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

/-!
# Higher homotopy groups of a torus

Every homotopy group of an indexed product is the indexed product of the homotopy groups of
its factors. Since the homotopy groups of a real circle vanish in dimensions at least two, the
same is true for any indexed product of real circles. In particular, all higher homotopy groups
of the finite-dimensional torus `Tᵏ` vanish.

Together with the fundamental-group computation in
`TauCeti.AlgebraicTopology.UniversalCover.Torus.FundamentalGroup`, this completes the
`π_n(Tᵏ)` application in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13.

## Main declarations

* `TauCeti.AddCircle.subsingleton_homotopyGroup_pi`: every homotopy group in dimension at
  least two of an indexed product of real circles is trivial.
* `TauCeti.AddCircle.homotopyGroup_pi_eq_one`,
  `TauCeti.AddCircle.homotopyGroupPi_pi_eq_one`: the corresponding equality statements.
-/

public section

namespace TauCeti

open scoped Topology Topology.Homotopy

namespace AddCircle

variable {N ι : Type*} [Nontrivial N] (p : ι → ℝ) (x : ∀ i, AddCircle (p i))

/-- Every higher homotopy group of an indexed product of real circles is trivial. The index
type `N` being nontrivial expresses that the homotopy dimension is at least two. -/
instance subsingleton_homotopyGroup_pi :
    Subsingleton (HomotopyGroup N (∀ i, AddCircle (p i)) x) := by
  constructor
  intro a b
  apply (HomotopyGroup.piEquiv x).injective
  funext i
  exact Subsingleton.elim _ _

/-- Every higher homotopy class of an indexed product of real circles is the identity. -/
theorem homotopyGroup_pi_eq_one [DecidableEq N]
    (a : HomotopyGroup N (∀ i, AddCircle (p i)) x) : a = 1 :=
  Subsingleton.elim _ _

/-- Every element of `π_(n + 2)` of an indexed product of real circles is the identity. -/
theorem homotopyGroupPi_pi_eq_one (n : ℕ)
    (a : π_ (n + 2) (∀ i, AddCircle (p i)) x) : a = 1 :=
  homotopyGroup_pi_eq_one p x a

end AddCircle

end TauCeti
