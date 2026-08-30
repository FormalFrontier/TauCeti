/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme

/-!
# Pinned root subgroups in the points of the Geck carrier

`TauCeti.DynkinType.geckRootSubgroup` is the scheme morphism from the additive group scheme into
the explicit Geck carrier, while `TauCeti.DynkinType.geckRootSubgroupMatrix` is its represented
matrix on points. This file supplies the missing group-homomorphism-valued interface between them:

```text
geckRootSubgroupPoints i A : Multiplicative A →* geckPoints A.
```

The codomain restriction is justified by the existing theorem that every represented root-subgroup
matrix lies in the carrier. The accompanying coercion theorem connects the new map to the matrix
API, so later functoriality and Frobenius proofs can reuse the established matrix equations without
unfolding the construction.

## Main declarations

* `TauCeti.DynkinType.geckRootSubgroupPoints`: the parametrized positive or negative simple-root
  subgroup inside the point group of the Geck carrier.
* `TauCeti.DynkinType.coe_geckRootSubgroupPoints`: its underlying general-linear matrix.

## References

The carrier and root-subgroup construction follows M. Geck, *On the construction of semisimple Lie
algebras and Chevalley groups*, Proc. Amer. Math. Soc. **145** (2017), 3233--3247, and J. C.
Jantzen, *Representations of Algebraic Groups*, II.1.

This advances the "Root subgroup maps" and "Points over an algebraically closed field" targets in
Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. Milestones L0 and L1 of
`TauCetiRoadmap/CFSGStatement/README.md` consume this exact point-valued map as
`ValidLieTypeIndex.simpleRootSubgroup` and in the equation `Frob_q (x_i(t)) = x_i(t ^ q)`.
-/

public section

namespace TauCeti.DynkinType

universe v

noncomputable section

-- Matrices form a Lie ring through their commutator, which is how Geck's construction reads them.
attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- **The parametrized numbered root subgroup inside the Geck carrier points.** The parameter is
read through the canonical multiplicative copy of the additive group of `A`. -/
noncomputable def geckRootSubgroupPoints (i : Fin t.rank ⊕ Fin t.rank)
    (A : Type v) [CommRing A] : Multiplicative A →* t.geckPoints ht A :=
  MonoidHom.codRestrict
    ((t.geckRootSubgroupMatrix ht i).comp
      (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm.toMonoidHom)
    (t.geckPoints ht A) fun u =>
      t.geckRootSubgroupMatrix_mem_geckPoints ht A i
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)

/-- A parametrized Geck root-subgroup point has the represented root-subgroup matrix as its
underlying general-linear element. -/
@[simp]
theorem coe_geckRootSubgroupPoints (i : Fin t.rank ⊕ Fin t.rank)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    (t.geckRootSubgroupPoints ht i A u :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      t.geckRootSubgroupMatrix ht i
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := (rfl)

end

end TauCeti.DynkinType
