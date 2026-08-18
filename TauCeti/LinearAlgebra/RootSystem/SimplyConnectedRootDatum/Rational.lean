/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

public section

/-!
# The rational root system of a Dynkin type

`TauCeti.DynkinType.simplyConnectedRootDatum` pins one integral root datum per valid Dynkin type,
on the lattices `Fin t.rank → ℤ`. The constructions which build a semisimple Lie algebra out of a
root system want instead a root *system* over a field of characteristic zero: the roots must span
the ambient space, which they do not in general over the simply connected character lattice, since
that lattice is the weight lattice and the roots only span the root lattice inside it. The two
lattices agree exactly when the Cartan matrix is unimodular, so integrally the roots do span for
`E₈`, `F₄` and `G₂`, and fail to span for every other valid type.

This file base-changes the pinned datum to `ℚ`, using `TauCeti.rootPairingBaseChange`, and proves
that the result is a genuine root system: the roots span, because the `t.rank` simple roots are
linearly independent in a space of dimension `t.rank`, and the coroots span, because they already
did over `ℤ`. The pinned base and the Bourbaki-numbered Cartan matrix survive the base change
unchanged, so the rational system realizes the same Dynkin type as the datum it comes from.

What is *not* proved here is that the rational system is reduced and irreducible. Both are
properties of the explicit root tables rather than of the base change: irreducibility is false over
`ℤ`, so it cannot be transported at all, and reducedness has not been established for the pinned
tables. They are the two remaining hypotheses of Geck's construction
`RootPairing.GeckConstruction.lieAlgebra`, which is what turns this root system into the split
semisimple Lie algebra whose Chevalley basis a Chevalley--Demazure group scheme is built from.

## Main definitions

* `TauCeti.DynkinType.rationalRootSystem`: the pinned datum of a valid Dynkin type, base-changed
  to `ℚ`.
* `TauCeti.DynkinType.rationalBase`: its Bourbaki-numbered base.

## Main results

* `TauCeti.DynkinType.instIsRootSystemRationalRootSystem`: the roots and coroots span.
* `TauCeti.DynkinType.hasCartanType_rationalRootSystem`: the rational system realizes its own
  Dynkin type against the pinned numbering.
* `TauCeti.DynkinType.pairingIn_rationalRootSystem`: its Cartan integers are those of the datum.

## References

The passage from a root datum over `ℤ` to the root system over `ℚ` it determines is standard; see
N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1. This supplies the
root-system input of the Chevalley basis in Layer 9, "pinned Chevalley--Demazure group schemes over
`ℤ`", of `TauCetiRoadmap/ReductiveGroups/README.md`, whose consumer is milestone L0 of the
`CFSGStatement` roadmap.
-/

namespace TauCeti.DynkinType

open _root_.Matrix Set
open Submodule (span)

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-! ## The base change to `ℚ` -/

/-- **The rational root system of a valid Dynkin type**: the pinned simply connected root datum
with its roots and coroots read in `Fin t.rank → ℚ`. The pairing is again the dot product, and the
reflection permutation is unchanged. -/
def rationalRootSystem :
    RootPairing (Fin t.numRoots) ℚ (Fin t.rank → ℚ) (Fin t.rank → ℚ) :=
  rootPairingBaseChange ℚ (t.simplyConnectedRootDatum ht)
    (toLinearMap_simplyConnectedRootDatum t ht)

/-- The Bourbaki-numbered base of `TauCeti.DynkinType.rationalRootSystem`, supported on the same
first `t.rank` root indices as the base of the integral datum. -/
def rationalBase : (t.rationalRootSystem ht).Base :=
  rootPairingBaseChangeBase ℚ (t.simplyConnectedRootDatum ht)
    (toLinearMap_simplyConnectedRootDatum t ht) (t.simplyConnectedBase ht)

@[simp] theorem root_rationalRootSystem (i : Fin t.numRoots) (k : Fin t.rank) :
    (t.rationalRootSystem ht).root i k = ((t.simplyConnectedRootDatum ht).root i k : ℚ) := by
  rw [rationalRootSystem, root_rootPairingBaseChange, piAlgebraMap_apply]
  simp

@[simp] theorem coroot_rationalRootSystem (i : Fin t.numRoots) (k : Fin t.rank) :
    (t.rationalRootSystem ht).coroot i k = ((t.simplyConnectedRootDatum ht).coroot i k : ℚ) := by
  rw [rationalRootSystem, coroot_rootPairingBaseChange, piAlgebraMap_apply]
  simp

@[simp] theorem reflectionPerm_rationalRootSystem :
    (t.rationalRootSystem ht).reflectionPerm = (t.simplyConnectedRootDatum ht).reflectionPerm :=
  reflectionPerm_rootPairingBaseChange ..

/-- The pairing of the rational system is the dot product of `Fin t.rank → ℚ` with itself. -/
@[simp] theorem toLinearMap_rationalRootSystem (x y : Fin t.rank → ℚ) :
    (t.rationalRootSystem ht).toLinearMap x y = x ⬝ᵥ y :=
  toLinearMap_rootPairingBaseChange ..

@[simp] theorem pairing_rationalRootSystem (i j : Fin t.numRoots) :
    (t.rationalRootSystem ht).pairing i j = ((t.simplyConnectedRootDatum ht).pairing i j : ℚ) := by
  rw [rationalRootSystem, pairing_rootPairingBaseChange]
  simp

@[simp] theorem support_rationalBase :
    (t.rationalBase ht).support = (t.simplyConnectedBase ht).support :=
  support_rootPairingBaseChangeBase ..

instance instIsCrystallographicRationalRootSystem : (t.rationalRootSystem ht).IsCrystallographic :=
  isCrystallographic_rootPairingBaseChange ..

/-- The Cartan integers of the rational system are those of the integral datum. -/
@[simp] theorem pairingIn_rationalRootSystem (i j : Fin t.numRoots) :
    (t.rationalRootSystem ht).pairingIn ℤ i j = (t.simplyConnectedRootDatum ht).pairingIn ℤ i j :=
  pairingIn_rootPairingBaseChange ..

/-! ## The rational system is a root system -/

/-- The coroots of the rational system span the rational cocharacter space, because the coroots of
the simply connected datum already span the cocharacter lattice. -/
theorem span_range_coroot_rationalRootSystem_eq_top :
    span ℚ (range (t.rationalRootSystem ht).coroot) = ⊤ :=
  span_range_coroot_rootPairingBaseChange_eq_top ℚ _ _ (span_coroot_simplyConnectedRootDatum t ht)

/-- The simple roots of the rational system are `t.rank` linearly independent vectors in a space of
dimension `t.rank`, so the roots span the rational character space. This is the statement which
fails integrally outside the unimodular types `E₈`, `F₄` and `G₂`: over `ℤ` the roots span only the
root lattice, which is a proper sublattice of the weight lattice whenever the Cartan matrix has
determinant other than `1`. -/
theorem span_range_root_rationalRootSystem_eq_top :
    span ℚ (range (t.rationalRootSystem ht).root) = ⊤ := by
  have hli : LinearIndependent ℚ fun i : ((t.rationalBase ht).support : Finset _) =>
      (t.rationalRootSystem ht).root i := (t.rationalBase ht).linearIndepOn_root
  have hcard : Fintype.card ((t.rationalBase ht).support : Finset _) =
      Module.finrank ℚ (Fin t.rank → ℚ) := by
    rw [Fintype.card_coe, Module.finrank_fin_fun, support_rationalBase]
    exact card_support_simplyConnectedBase t ht
  refine top_le_iff.mp ?_
  rw [← hli.span_eq_top_of_card_eq_finrank' hcard]
  exact Submodule.span_mono (by rintro - ⟨i, rfl⟩; exact mem_range_self (i : Fin t.numRoots))

instance instIsRootSystemRationalRootSystem : (t.rationalRootSystem ht).IsRootSystem where
  span_root_eq_top := span_range_root_rationalRootSystem_eq_top t ht
  span_coroot_eq_top := span_range_coroot_rationalRootSystem_eq_top t ht

/-! ## Acceptance: the rational system realizes its own Dynkin type -/

/-- **The rational system has Cartan type `t`.** The base change leaves both the support of the
pinned base and every Cartan integer alone, so the relabelling exhibited by the integral datum
still works. -/
theorem hasCartanType_rationalRootSystem :
    HasCartanType (t.rationalRootSystem ht) (t.rationalBase ht) t := by
  obtain ⟨e, he⟩ := (hasCartanType_iff _ _).1 (hasCartanType_simplyConnectedRootDatum t ht)
  refine (hasCartanType_iff _ _).2 ⟨(supportEquivRootPairingBaseChangeBase ℚ _ _ _).trans e,
    fun i j => ?_⟩
  exact (cartanMatrix_rootPairingBaseChangeBase ℚ _ _ _ i j).trans (he _ _)

end

end TauCeti.DynkinType
