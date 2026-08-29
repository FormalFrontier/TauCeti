/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Frobenius
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GraphAutomorphism

/-!
# The graph-twisted Frobenius of the pinned Geck carrier

For a valid Dynkin type `t` and a symmetry `σ` of its Bourbaki-numbered Dynkin diagram, the points
of `TauCeti.DynkinType.geckGroupScheme` over a value ring of exponential characteristic `p` carry
two commuting endomorphisms: the `q`-power Frobenius `TauCeti.DynkinType.geckFrobenius`, with
`q = p ^ k`, and the graph automorphism `TauCeti.DynkinType.geckGraphAutPoints`. This file records
that they commute and composes them.

The composite `TauCeti.DynkinType.geckTwistedFrobenius` acts on the pinned generating families by

```text
F (xᵢ(u)) = x_{σ i}(u ^ q),        F (t(s)) = t(s ^ q ∘ σ⁻¹),
```

with `i` ranging over the numbered raising and lowering generators. The first equation is the
defining relation of a graph-twisted Steinberg endomorphism on the simple root subgroups: the
parameter is raised to the `q`-th power and the numbering is permuted by the diagram symmetry,
with no sign or scaling attached, which is what a pinning normalizes away.

Commutation is a special case of naturality: the Frobenius endomorphism is the map on points
induced by the iterated Frobenius of the value ring, and the graph automorphism is natural in that
ring because it is conjugation by a permutation matrix whose entries are `0` and `1`, and which is
therefore fixed entrywise by any ring map. So the commutation is
`TauCeti.DynkinType.geckPointsMap_comp_geckGraphAutPoints`, read at the iterated Frobenius.

Two limitations carry over from the two factors. This is the twisted Frobenius of the *carrier*,
not of the elementary subgroup its root subgroups generate, and the Geck weights span the root
lattice rather than, in general, the full character lattice, so this carrier is not yet the simply
connected one a finite group of Lie type is built from. Nothing below asserts that any subgroup
appearing here is finite, is simple, or is a named finite group, and no fixed-point subgroup is
computed.

## Main definitions

* `TauCeti.DynkinType.geckTwistedFrobenius`: the graph-twisted `p ^ k`-power Frobenius on the
  points of the pinned Geck carrier.

## Main results

* `TauCeti.DynkinType.geckGraphAutPoints_comp_geckFrobenius`: the graph automorphism commutes with
  the Frobenius.
* `TauCeti.DynkinType.geckTwistedFrobenius_eq_geckFrobenius_comp`: the twisted Frobenius is that
  composite in either order.
* `TauCeti.DynkinType.coe_geckTwistedFrobenius`: the twisted Frobenius conjugates the entrywise
  Frobenius by the pinned symmetry matrix.
* `TauCeti.DynkinType.geckTwistedFrobenius_geckRootSubgroupMatrix`: the defining equation on the
  pinned numbered root subgroups.
* `TauCeti.DynkinType.geckTwistedFrobenius_geckTorusMatrix`: the equation on the pinned weight
  torus.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs Amer. Math. Soc. **80** (1968),
  §11.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17.

This composes the graph-automorphism and Frobenius halves of the pinning and points targets of
Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L1, ordinary and
graph-twisted Steinberg maps, of `TauCetiRoadmap/CFSGStatement/README.md`, whose `²A`, `²D`, `²E₆`
and `³D₄` branches are `γ ∘ Frob_q` and whose required relation is that `γ` commutes with `Frob_q`.
-/

public section

namespace TauCeti.DynkinType

universe v

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {sigma : Equiv.Perm (Fin t.rank)}
variable (hsigma : sigma ∈ t.diagramSymmetry) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The graph automorphism of the points of the pinned Geck carrier commutes with its
Frobenius endomorphism.** This is the relation the graph-twisted Steinberg maps of a finite group
of Lie type are required to satisfy. -/
theorem geckGraphAutPoints_comp_geckFrobenius :
    (t.geckGraphAutPoints ht hsigma A).toMonoidHom.comp (t.geckFrobenius ht p k A) =
      (t.geckFrobenius ht p k A).comp (t.geckGraphAutPoints ht hsigma A).toMonoidHom := by
  have hF : t.geckFrobenius ht p k A = t.geckPointsMap ht (iterateFrobenius A p k) :=
    MonoidHom.ext fun g => Subtype.ext
      ((t.coe_geckFrobenius ht p k A g).trans (t.coe_geckPointsMap ht _ g).symm)
  rw [hF]
  exact (t.geckPointsMap_comp_geckGraphAutPoints ht hsigma (iterateFrobenius A p k)).symm

/-- **The graph-twisted `p ^ k`-power Frobenius on the points of the pinned Geck carrier**, the
graph automorphism attached to a diagram symmetry composed with the Frobenius endomorphism. The
two factors commute, so composing them in the other order gives the same map.

This is the composite on the carrier and nothing more: no fixed-point subgroup is computed and no
finiteness is asserted. Its intended application is the twisted branches of a finite group of Lie
type, where `p` is prime, `0 < k`, `A` is an algebraic closure of `ZMod p` and `σ` is an involution
or a triality of the diagram; reading it as the Steinberg endomorphism of such a group first
requires identifying this carrier with the simply connected group, which is not done here. -/
def geckTwistedFrobenius : t.geckPoints ht A →* t.geckPoints ht A :=
  (t.geckGraphAutPoints ht hsigma A).toMonoidHom.comp (t.geckFrobenius ht p k A)

/-- The twisted Frobenius applies the Frobenius first and then the graph automorphism. -/
theorem geckTwistedFrobenius_apply (g : t.geckPoints ht A) :
    t.geckTwistedFrobenius ht hsigma p k A g =
      t.geckGraphAutPoints ht hsigma A (t.geckFrobenius ht p k A g) := (rfl)

/-- The twisted Frobenius is the composite in either order. -/
theorem geckTwistedFrobenius_eq_geckFrobenius_comp :
    t.geckTwistedFrobenius ht hsigma p k A =
      (t.geckFrobenius ht p k A).comp (t.geckGraphAutPoints ht hsigma A).toMonoidHom := by
  rw [geckTwistedFrobenius, geckGraphAutPoints_comp_geckFrobenius]

/-- The twisted Frobenius conjugates the entrywise Frobenius by the matrix of the pinned
coordinate permutation. -/
@[simp]
theorem coe_geckTwistedFrobenius (g : t.geckPoints ht A) :
    (t.geckTwistedFrobenius ht hsigma p k A g :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      t.geckGraphAutMatrix ht hsigma A *
          Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g *
        (t.geckGraphAutMatrix ht hsigma A)⁻¹ := by
  rw [geckTwistedFrobenius_apply, coe_geckGraphAutPoints, coe_geckFrobenius]

/-- **The twisted Frobenius raises the parameter of a numbered Geck root subgroup to its
`p ^ k`-th power and renumbers it by the diagram symmetry.** This is the defining equation of a
graph-twisted Steinberg map on the pinned simple root subgroups. -/
@[simp]
theorem geckTwistedFrobenius_geckRootSubgroupMatrix (i : Fin t.rank ⊕ Fin t.rank)
    (u : Multiplicative A) :
    t.geckTwistedFrobenius ht hsigma p k A
        ⟨t.geckRootSubgroupMatrix ht i
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u),
          t.geckRootSubgroupMatrix_mem_geckPoints ht A i _⟩ =
      ⟨t.geckRootSubgroupMatrix ht (diagramRootGeneratorPerm sigma i)
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k))),
        t.geckRootSubgroupMatrix_mem_geckPoints ht A _ _⟩ := by
  rw [geckTwistedFrobenius_apply, geckFrobenius_geckRootSubgroupMatrix,
    geckGraphAutPoints_geckRootSubgroupMatrix]

/-- **The twisted Frobenius raises a point of the pinned Geck weight torus to its `p ^ k`-th power
and relabels its coordinates** by the inverse of the diagram symmetry. -/
@[simp]
theorem geckTwistedFrobenius_geckTorusMatrix (s : Fin t.rank → Aˣ) :
    t.geckTwistedFrobenius ht hsigma p k A
        ⟨diagGL fun i => torusCharacter s (t.geckWeightFin ht i), by
          simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using
            t.geckTorusMatrix_mem_geckPoints ht A s⟩ =
      ⟨t.geckTorusMatrix ht fun j => (s (sigma⁻¹ j)) ^ p ^ k,
        t.geckTorusMatrix_mem_geckPoints ht A _⟩ := by
  rw [geckTwistedFrobenius_apply, geckFrobenius_geckTorusMatrix, geckPoints_mk_geckTorusMatrix,
    geckGraphAutPoints_geckTorusMatrix]
  exact Subtype.ext (congrArg (t.geckTorusMatrix ht) (funext fun j => Pi.pow_apply s (p ^ k) _))

end

end TauCeti.DynkinType
