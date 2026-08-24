/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Coordinate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme

/-!
# The pinned ambient groups of finite groups of Lie type

For every valid Lie-type index this file evaluates the pinned simply connected
Chevalley--Demazure group scheme of its underlying Dynkin type -- the Geck carrier of
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/GeckLattice/GroupScheme.lean` -- at the
algebraic closure of the index's prime field. The result is the carrier to which the Steinberg
endomorphisms and the fixed-point construction of the later CFSG milestones are applied.

The construction is a composition of named upstream data, never a choice from an existence
theorem: `ValidLieTypeIndex.dynkinType` names the diagram, `DynkinType.simplyConnectedRootDatum`
names its simply connected root datum, the Geck construction turns that datum into an explicit
group scheme cut out by a defining Hopf ideal inside `GLₙ`, and the points over
`ValidLieTypeIndex.Closure` are its matrices satisfying that ideal.

## Main definitions

* `TauCeti.ValidLieTypeIndex.AmbientGroup`: the algebraic-closure-valued points of the pinned
  Chevalley--Demazure group of the index.
* `TauCeti.ValidLieTypeIndex.simpleRootSubgroup`: the numbered simple root subgroup map
  `x_i : Closure → AmbientGroup` read off the pinning.
* `TauCeti.ValidLieTypeIndex.frobeniusPow`, `.frobenius`, `.primeFrobenius`: the entrywise
  Frobenius endomorphisms of the ambient points; `frobenius` raises by the field order and is the
  untwisted Steinberg factor of milestone L1, while `primeFrobenius` is the square of the
  exceptional isogeny consumed by L2.

## Main results

* `TauCeti.ValidLieTypeIndex.simpleRootSubgroup_add`: each simple root subgroup is a homomorphism
  from the additive group of the closure.
* `TauCeti.ValidLieTypeIndex.frobenius_simpleRootSubgroup`:
  `Frob_q (x_i(t)) = x_i(t ^ q)` for `q = d.fieldOrder`, the equation pinning the untwisted
  branch of the Steinberg map.

## Roadmap

This is milestone `L0` of `TauCetiRoadmap/CFSGStatement/README.md`: the actual body of
`ValidLieTypeIndex.AmbientGroup`, its `Group` instance, and `ValidLieTypeIndex.simpleRootSubgroup`,
together with the field Frobenius whose simple-root equation opens milestone `L1`. It consumes,
rather than restates, Layer 6 of the root-systems roadmap (`DynkinType.simplyConnectedRootDatum`)
and Layer 9 of the reductive-groups roadmap (the Geck carrier, its points, root subgroups, and
Frobenius on Hopf-ideal points). Milestones `L1` through `L4` compose their Steinberg endomorphisms
with these maps; `L3` takes fixed points of them.
-/

public section

namespace TauCeti.ValidLieTypeIndex

variable (d : ValidLieTypeIndex)

noncomputable section

/-- **The ambient group of a valid Lie-type index**: the algebraic-closure-valued points of the
pinned simply connected Chevalley--Demazure group scheme of its Dynkin type, as a subgroup of
`GLₙ(d.Closure)` cut out by the defining Hopf ideal of the Geck carrier.

The carrier traces back to explicit data at every step: the index names its Dynkin type, the root
datum is `DynkinType.simplyConnectedRootDatum`, and the points are the matrices killing the
defining ideal of the resulting group scheme. By `DynkinType.geckPoints_def` these are exactly the
`d.Closure`-valued points `DynkinType.geckPoints` of the Geck carrier; they are written here in
the Hopf-ideal form because that is the form in which the Frobenius endomorphisms below and the
fixed-point constructions of milestone L3 consume them. -/
abbrev AmbientGroup : Type :=
  ↥(GeneralLinear.hopfIdealPointsSubgroup (d.dynkinType.geckDim d.dynkinType_valid)
      (d.dynkinType.geckDefiningIdeal d.dynkinType_valid) d.Closure)

instance instGroupAmbientGroup (d : ValidLieTypeIndex) : Group d.AmbientGroup :=
  inferInstanceAs (Group ↥(GeneralLinear.hopfIdealPointsSubgroup
    (d.dynkinType.geckDim d.dynkinType_valid)
    (d.dynkinType.geckDefiningIdeal d.dynkinType_valid) d.Closure))

/-! ### The numbered simple root subgroups -/

/-- The numbered simple root subgroup `x_i` of the pinning, where `i` runs over the
Bourbaki-numbered simple roots of the underlying diagram. This is the positive simple root subgroup
of the Geck carrier, evaluated on the parameter `t`. -/
noncomputable def simpleRootSubgroup (i : Fin d.rank) (t : d.Closure) : d.AmbientGroup :=
  ⟨d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid (Sum.inl i)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm (Multiplicative.ofAdd t)),
    (DynkinType.geckPoints_def d.dynkinType d.dynkinType_valid d.Closure) ▸
      d.dynkinType.geckRootSubgroupMatrix_mem_geckPoints d.dynkinType_valid d.Closure
        (Sum.inl i)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm
          (Multiplicative.ofAdd t))⟩

/-- The value of the simple root subgroup map at `t`, as a matrix. -/
@[simp]
theorem coe_simpleRootSubgroup (i : Fin d.rank) (t : d.Closure) :
    ((d.simpleRootSubgroup i t : d.AmbientGroup) :
      Matrix.GeneralLinearGroup (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) =
      d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid (Sum.inl i)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm
          (Multiplicative.ofAdd t)) := by
  simp only [simpleRootSubgroup]

/-- The parameter of the simple root subgroup map composes additively: the points of `𝔾ₐ` over
the closure form the additive monoid `(Closure, +)`, so the inverse point equivalence sends the
product of the parameters to the parameters of the sum. -/
theorem gaPointParam_add (s t : d.Closure) :
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm
        (Multiplicative.ofAdd (s + t)) =
      (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm
          (Multiplicative.ofAdd s) *
        (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm
          (Multiplicative.ofAdd t) :=
  map_mul (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm
    (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

/-- Each simple root subgroup is a homomorphism from the additive group of the closure: the
parameters compose additively because the root-subgroup map is a monoid homomorphism on the
points of `𝔾ₐ`. -/
theorem simpleRootSubgroup_add (i : Fin d.rank) (s t : d.Closure) :
    d.simpleRootSubgroup i (s + t) = d.simpleRootSubgroup i s * d.simpleRootSubgroup i t := by
  refine Subtype.ext ?_
  simp only [simpleRootSubgroup, Subgroup.coe_mul]
  exact (congrArg (d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid (Sum.inl i))
    (gaPointParam_add _ s t)).trans (map_mul _ _ _)

/-! ### The field Frobenius on the ambient points -/

/-- The entrywise Frobenius endomorphism of the ambient group: each entry of a representing
matrix is raised to the `d.characteristic ^ k`-th power. This is the restriction along
`geckPoints_def` of the Frobenius endomorphism of the Hopf-ideal point group, and every later
Steinberg endomorphism is built from its field-order case. -/
noncomputable def frobeniusPow (k : ℕ) : d.AmbientGroup →* d.AmbientGroup :=
  GeneralLinear.iterateFrobeniusHopfIdealPoints (d.dynkinType.geckDim d.dynkinType_valid)
    d.characteristic k (d.dynkinType.geckDefiningIdeal d.dynkinType_valid) d.Closure

/-- The ambient Frobenius acts by the entrywise Frobenius on the representing matrices. -/
@[simp]
theorem coe_frobeniusPow (k : ℕ) (g : d.AmbientGroup) :
    ((d.frobeniusPow k g : d.AmbientGroup) :
      Matrix.GeneralLinearGroup (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius d.Closure d.characteristic k) g :=
  GeneralLinear.coe_iterateFrobeniusHopfIdealPoints
    (n := d.dynkinType.geckDim d.dynkinType_valid) (p := d.characteristic) (k := k)
    (I := d.dynkinType.geckDefiningIdeal d.dynkinType_valid) (A := d.Closure)
    ⟨(g : Matrix.GeneralLinearGroup (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure),
      g.2⟩

/-- Post-composing the parameter point of a root subgroup with the Frobenius of the value algebra
multiplies the parameter by the same power: the two ways of moving Frobenius across `x_i(t)`
agree. -/
theorem gaPointParam_iterateFrobenius (k : ℕ) (t : d.Closure) :
    AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ)
        (iterateFrobenius d.Closure d.characteristic k).toIntAlgHom
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm
          (Multiplicative.ofAdd t)) =
      (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm
        (Multiplicative.ofAdd (t ^ d.characteristic ^ k)) :=
  (AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply
    (R := ℤ) (A := d.Closure) (B := d.Closure)
    (iterateFrobenius d.Closure d.characteristic k).toIntAlgHom
    (Multiplicative.ofAdd t)).trans (by congr 1)

/-- The matrix-valued root subgroup of the carrier is natural in the value ring: post-composing
the parameter point with a ring homomorphism applies it to the parameter. -/
theorem map_geckRootSubgroupMatrix (φ : d.Closure →+* d.Closure) (i : Fin d.rank ⊕ Fin d.rank)
    (u : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] d.Closure)) :
    Matrix.GeneralLinearGroup.map φ
        (d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid i u) =
      d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid i
        (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ.toIntAlgHom u) :=
  UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix _ _ _ _ _ _ _ _ _ _

/-- **The defining equation of the Frobenius on the simple root subgroups**:
`Frob (x_i(t)) = x_i(t ^ q)` with `q = d.characteristic ^ k`.

Naturality of the matrix-valued root subgroup in the value ring moves the entrywise Frobenius
across `x_i`, and the parameter transforms by the same ring endomorphism. -/
theorem frobeniusPow_simpleRootSubgroup (k : ℕ) (i : Fin d.rank) (t : d.Closure) :
    d.frobeniusPow k (d.simpleRootSubgroup i t) =
      d.simpleRootSubgroup i (t ^ d.characteristic ^ k) := by
  refine Subtype.ext ?_
  have h1 := coe_frobeniusPow (d := d) k (d.simpleRootSubgroup i t)
  simp only [simpleRootSubgroup] at h1 ⊢
  rw [h1, map_geckRootSubgroupMatrix]
  exact congrArg _ (gaPointParam_iterateFrobenius d k t)

/-- **The `q`-power Frobenius induced on the ambient points**, for `q = d.fieldOrder`: the
untwisted Steinberg factor of milestone L1. On the Suzuki--Ree families its square-root role is
played by the exceptional isogeny consumed by L2 instead. -/
noncomputable def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  d.frobeniusPow d.fieldExponent

/-- The defining equation `Frob_q (x_i(t)) = x_i(t ^ q)` of the field-order Frobenius on the
numbered simple root subgroups. -/
theorem frobenius_simpleRootSubgroup (i : Fin d.rank) (t : d.Closure) :
    d.frobenius (d.simpleRootSubgroup i t) = d.simpleRootSubgroup i (t ^ d.fieldOrder) := by
  rw [frobenius, frobeniusPow_simpleRootSubgroup, fieldOrder_eq_characteristic_pow]

/-- The characteristic-power Frobenius, the square of the exceptional isogeny that the
reductive-groups roadmap targets and milestone L2 consumes. -/
noncomputable def primeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  d.frobeniusPow 1

/-- The defining equation `Frob_p (x_i(t)) = x_i(t ^ p)` of the prime Frobenius on the numbered
simple root subgroups. -/
theorem primeFrobenius_simpleRootSubgroup (i : Fin d.rank) (t : d.Closure) :
    d.primeFrobenius (d.simpleRootSubgroup i t) =
      d.simpleRootSubgroup i (t ^ d.characteristic) := by
  rw [primeFrobenius, frobeniusPow_simpleRootSubgroup, pow_one]

end

end TauCeti.ValidLieTypeIndex
