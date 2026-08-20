/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Height
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm

/-!
# The height degree of pinned integral weights

The pinned rational root system of a valid Dynkin type has the simple roots as a basis of its
weight space. Summing the coordinates in this basis gives a rational-valued degree on integral
weights. This file packages that functional as `TauCeti.DynkinType.weightDegree` and identifies
its value on the weights of Geck's defining representation.

On the coordinate indexed by a root `alpha`, `TauCeti.DynkinType.geckWeight` is the vector of
Cartan pairings of `alpha` against the numbered simple coroots. In the pinned fundamental-weight
coordinates this is the root itself. Its degree is therefore the height of `alpha`; in particular,
it is positive on every positive root and sends each simple-root Cartan row to one. These are the
facts needed to order a finite weight basis so that positive root subgroups act by upper
unitriangular matrices, the triangular input to the Borel component of a pinning.

## Main definitions

* `TauCeti.DynkinType.weightDegree`: the simple-root height functional on integral weights.

## Main results

* `TauCeti.DynkinType.weightDegree_geckWeight_inr`: the degree of a root coordinate is its root
  height.
* `TauCeti.DynkinType.weightDegree_geckWeight_inr_pos`: positive-root coordinates have positive
  degree.
* `TauCeti.DynkinType.weightDegree_cartanMatrix_row`: every simple-root Cartan row has degree one.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Sections 10 and 26.
* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 8.2.

This advances the pinning and Chevalley--Demazure construction targets in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Their pinned ambient group is consumed by milestone L0
of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The simple-root height degree on integral weights of a valid Dynkin type.** An integral
weight is first read in the rational weight space, then evaluated by the linear extension of root
height from the pinned simple-root basis. -/
def weightDegree : (Fin t.rank → ℤ) →+ ℚ :=
  (heightLinearMap (t.rationalRootSystem ht) (t.rationalBase ht)).toAddMonoidHom.comp
    (AddMonoidHom.piMap fun _ ↦ Int.castAddHom ℚ)

/-- The weight degree is obtained by casting an integral weight to the rational weight space and
applying the height functional there. -/
theorem weightDegree_apply (μ : Fin t.rank → ℤ) :
    t.weightDegree ht μ = heightLinearMap (t.rationalRootSystem ht) (t.rationalBase ht)
      (fun i ↦ (μ i : ℚ)) :=
  (rfl)

/-- The integral weight of a root coordinate in Geck's representation, cast to `ℚ`, is the
corresponding root of the pinned rational root system. -/
theorem intCast_geckWeight_inr (k : Fin t.numRoots) :
    (fun i ↦ (t.geckWeight ht (Sum.inr k) i : ℚ)) =
      (t.rationalRootSystem ht).root k := by
  funext i
  rw [geckWeight_inr]
  rw [← eq_intCast (algebraMap ℤ ℚ)]
  rw [(t.rationalRootSystem ht).algebraMap_pairingIn ℤ k (t.simpleSupportEquiv ht i),
    ← RootPairing.root_coroot_eq_pairing, toLinearMap_rationalRootSystem,
    coe_simpleSupportEquiv]
  have hcoroot : (t.rationalRootSystem ht).coroot (t.simpleIndex ht i) = Pi.single i 1 := by
    ext j
    by_cases hij : i = j <;> simp [hij]
  rw [hcoroot, dotProduct_single, mul_one]

/-- The degree of a root coordinate in Geck's defining representation is the height of that root
relative to the pinned base. -/
@[simp]
theorem weightDegree_geckWeight_inr (k : Fin t.numRoots) :
    t.weightDegree ht (t.geckWeight ht (Sum.inr k)) =
      ((t.rationalBase ht).height k : ℚ) := by
  rw [weightDegree_apply, intCast_geckWeight_inr, heightLinearMap_root]

/-- A positive-root coordinate in Geck's defining representation has positive degree. -/
theorem weightDegree_geckWeight_inr_pos {k : Fin t.numRoots}
    (hk : k ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    0 < t.weightDegree ht (t.geckWeight ht (Sum.inr k)) := by
  rw [weightDegree_geckWeight_inr]
  exact_mod_cast lt_of_lt_of_le Int.zero_lt_one
    (one_le_height_of_mem_posRoots (t.rationalRootSystem ht) (t.rationalBase ht) hk)

/-- A Cartan-support coordinate in Geck's defining representation has weight zero, hence degree
zero. -/
@[simp]
theorem weightDegree_geckWeight_inl (x : (t.rationalBase ht).support) :
    t.weightDegree ht (t.geckWeight ht (Sum.inl x)) = 0 := by
  have hzero : t.geckWeight ht (Sum.inl x) = 0 := by
    funext i
    exact geckWeight_inl t ht x i
  rw [hzero, map_zero]

/-- **Every simple-root Cartan row has degree one.** This is the positive-degree input for each
numbered raising generator of the pinned Lie algebra. -/
@[simp]
theorem weightDegree_cartanMatrix_row (i : Fin t.rank) :
    t.weightDegree ht (fun j ↦ t.cartanMatrix i j) = 1 := by
  have hweight : (fun j ↦ t.cartanMatrix i j) =
      t.geckWeight ht (Sum.inr (t.simpleIndex ht i)) := by
    funext j
    rw [geckWeight_inr, coe_simpleSupportEquiv, pairingIn_rationalRootSystem,
      pairingIn_simpleIndex]
  have hi := (t.simpleSupportEquiv ht i).property
  rw [coe_simpleSupportEquiv] at hi
  rw [hweight, weightDegree_geckWeight_inr,
    (t.rationalBase ht).height_one_of_mem_support hi]
  simp

/-- Every negative simple-root Cartan row has degree minus one. -/
@[simp]
theorem weightDegree_neg_cartanMatrix_row (i : Fin t.rank) :
    t.weightDegree ht (fun j ↦ -t.cartanMatrix i j) = -1 := by
  rw [← Pi.neg_def, map_neg, weightDegree_cartanMatrix_row]

end

end TauCeti.DynkinType
