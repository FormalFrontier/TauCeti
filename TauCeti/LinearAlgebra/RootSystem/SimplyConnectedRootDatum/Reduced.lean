/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Reducedness of the simply-laced pinned root data

The pinned simply connected root data of types `A`, `D`, `E₆`, `E₇`, and `E₈` are reduced. Their
character and cocharacter lattices use different preferred bases, so reducedness is not obtained
by identifying each root with its coroot. Instead, their coordinate constructions all exhibit a
symmetric root--coroot pairing. `RootPairing.isReduced_of_pairing_comm` then rules out nontrivial
multiples among their roots.

These instances supply the reducedness hypothesis needed to apply Mathlib's Geck construction to
the rational scalar extensions of the pinned data. The non-simply-laced types require a separate
argument because their root--coroot pairings are not symmetric.

## Main results

* Reducedness results for `DynkinType.typeASimplyConnectedRootDatum`,
  `typeDSimplyConnectedRootDatum`, `e6SimplyConnectedRootDatum`,
  `e7SimplyConnectedRootDatum`, and `e8SimplyConnectedRootDatum`.
* `DynkinType.isReduced_simplyConnectedRootDatum_of_isSimplyLaced`: the uniform reducedness
  theorem for every valid simply-laced Dynkin type.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I, IV--VII.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*.
-/

public section

namespace TauCeti.DynkinType

/-- The pinned simply connected root datum of type `A` is reduced. -/
theorem isReduced_typeASimplyConnectedRootDatum (n : ℕ) :
    (typeASimplyConnectedRootDatum n).IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ pairing_typeASimplyConnectedRootDatum_comm

/-- The pinned simply connected root datum of type `D` is reduced. -/
theorem isReduced_typeDSimplyConnectedRootDatum (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ (pairing_typeDSimplyConnectedRootDatum_comm hn)

/-- The pinned simply connected root datum of type `E₆` is reduced. -/
instance instIsReducedE6SimplyConnectedRootDatum : e6SimplyConnectedRootDatum.IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ fun i j => by
    simpa only [e6SimplyConnectedRootDatum_pairing] using e6Root_dotProduct_e6Coroot_comm i j

/-- The pinned simply connected root datum of type `E₇` is reduced. -/
instance instIsReducedE7SimplyConnectedRootDatum : e7SimplyConnectedRootDatum.IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ fun i j => by
    simpa only [e7SimplyConnectedRootDatum_pairing] using e7Root_dotProduct_e7Coroot_comm i j

/-- The pinned simply connected root datum of type `E₈` is reduced. -/
instance instIsReducedE8SimplyConnectedRootDatum : e8SimplyConnectedRootDatum.IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ fun i j => by
    simpa only [e8SimplyConnectedRootDatum_pairing] using e8Root_dotProduct_e8Coroot_comm i j

attribute [local instance] instIsReducedE6SimplyConnectedRootDatum
  instIsReducedE7SimplyConnectedRootDatum instIsReducedE8SimplyConnectedRootDatum

/-- The pinned simply connected root datum of every valid simply-laced Dynkin type is reduced. -/
theorem isReduced_simplyConnectedRootDatum_of_isSimplyLaced (t : DynkinType) (ht : t.Valid)
    (hs : t.IsSimplyLaced) : (t.simplyConnectedRootDatum ht).IsReduced := by
  cases t with
  | A n =>
      rw [simplyConnectedRootDatum_A]
      exact isReduced_typeASimplyConnectedRootDatum n
  | B n => simp at hs
  | C n => simp at hs
  | D n =>
      rw [simplyConnectedRootDatum_D]
      exact isReduced_typeDSimplyConnectedRootDatum n (valid_D.mp ht)
  | E6 =>
      rw [simplyConnectedRootDatum_E6]
      exact instIsReducedE6SimplyConnectedRootDatum
  | E7 =>
      rw [simplyConnectedRootDatum_E7]
      exact instIsReducedE7SimplyConnectedRootDatum
  | E8 =>
      rw [simplyConnectedRootDatum_E8]
      exact instIsReducedE8SimplyConnectedRootDatum
  | F4 => simp at hs
  | G2 => simp at hs

end TauCeti.DynkinType
