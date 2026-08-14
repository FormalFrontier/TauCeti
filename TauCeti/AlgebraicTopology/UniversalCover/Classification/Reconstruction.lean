/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
public import TauCeti.Topology.Covering.Category
public import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# Reconstructing a connected cover from a fundamental-group action

Let `A` be a `π₁(X, x₀)`-set and choose `a : A`. The stabilizer of `a` is a subgroup of the
fundamental group, so the universal-cover quotient by that stabilizer is a connected covering
space of `X`. Its fibre over `x₀` is equivariantly equivalent to the orbit of `a`, hence to `A`
itself when the action is transitive.

This is the object-level reconstruction in the classification of connected covers by transitive
fundamental-group actions. The construction deliberately reuses the cover attached to a subgroup
and orbit-stabilizer: no second topology on a reconstructed total space is introduced. A later
step can extend the equivariant equivalence on the base fibre to a natural isomorphism of
fundamental-groupoid actions and assemble the categorical equivalence.

## Main declarations

* `TauCeti.UniversalCover.stabilizerCover`: the connected covering space obtained by
  quotienting the universal cover by the stabilizer of a point in a fundamental-group action.
* `TauCeti.UniversalCover.stabilizerCoverBasepointFiber`: the distinguished point of its fibre
  over `x₀`.
* `TauCeti.UniversalCover.stabilizerCoverFiberEquivOrbit`: the fibre of that cover over `x₀` is
  equivalent to the orbit of `a`, and
  `TauCeti.UniversalCover.stabilizerCoverFiberEquivOrbit_apply_monodromy` shows this equivalence
  intertwines covering-space monodromy with the given fundamental-group action.
* `TauCeti.UniversalCover.transitiveActionFiberEquiv` and
  `TauCeti.UniversalCover.transitiveActionFiberEquiv_apply_monodromy`: for a transitive action
  the same fibre is equivariantly equivalent to the whole `π₁(X, x₀)`-set.

## References

This is the reconstruction step in the alternative transitive-action formulation of Stage 2,
item 8 of `TauCetiRoadmap/UniversalCovers/README.md`. It is the standard stabilizer construction
for the equivalence between connected covering spaces and transitive fundamental-group sets; see
Hatcher, *Algebraic Topology*, Section 1.3. The proof uses Mathlib's orbit-stabilizer equivalence
and Tau Ceti's universal-cover quotient associated to a subgroup.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u v

variable {X : Type u} [TopologicalSpace X]

namespace TauCeti.UniversalCover

variable (x0 : X) {A : Type v} [MulAction (FundamentalGroup X x0) A]
  [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-- The connected covering space attached to a point `a` of a `π₁(X, x₀)`-set: it is the
universal cover modulo the stabilizer of `a`.

Its fibre over `x₀` is the orbit of `a`, so for a transitive action it is the cover
reconstructed from the action. -/
def stabilizerCover (a : A) : ConnectedCoveringSpace (TopCat.of X) :=
  ConnectedCoveringSpace.mk
    (TopCat.ofHom
      ⟨subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a),
        continuous_subgroupQuotientProj x0 _⟩)
    (isCoveringMap_subgroupQuotientProj x0 _)

/-- The total space of the cover reconstructed from `a` is the quotient of the universal cover
by the stabilizer of `a`. -/
@[simp]
theorem stabilizerCover_coe (a : A) :
    (stabilizerCover x0 a : TopCat) =
      TopCat.of (SubgroupQuotient x0
        (MulAction.stabilizer (FundamentalGroup X x0) a)) := by
  rw [stabilizerCover]
  exact ConnectedCoveringSpace.mk_coe _ _

/-- The projection of the cover reconstructed from `a` is the descended endpoint projection. -/
theorem stabilizerCover_proj (a : A) :
    (stabilizerCover x0 a).proj =
      eqToHom (stabilizerCover_coe x0 a) ≫
        TopCat.ofHom
          ⟨subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a),
            continuous_subgroupQuotientProj x0 _⟩ := by
  simpa only [stabilizerCover] using
    ConnectedCoveringSpace.mk_proj
      (TopCat.ofHom
        ⟨subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a),
          continuous_subgroupQuotientProj x0 _⟩)
      (isCoveringMap_subgroupQuotientProj x0 _)

/-- The distinguished point of the fibre over `x₀` of the cover reconstructed from `a`: the
class of the constant path at the basepoint. -/
def stabilizerCoverBasepointFiber (a : A) : ⇑(stabilizerCover x0 a).proj ⁻¹' {x0} :=
  SubgroupQuotient.basepointFiber x0 (MulAction.stabilizer (FundamentalGroup X x0) a)

/-! ### The fibre as an orbit

The equivalence and its equivariance are first proved for the underlying quotient projection,
which carries the instances the orbit-stabilizer API needs; the bundled cover of the API is
definitionally that projection. -/

/-- The fibre–coset identification of a subgroup quotient sends the monodromy translate of the
distinguished point of the fibre to the coset of the loop class. -/
private theorem fiberEquivQuotientRange_monodromy_basepointFiber
    (H : Subgroup (FundamentalGroup X x0)) (g : FundamentalGroup X x0) :
    TauCeti.IsCoveringMap.fiberEquivQuotientRange (isCoveringMap_subgroupQuotientProj x0 H)
        (SubgroupQuotient.basepointFiber x0 H)
        ((isCoveringMap_subgroupQuotientProj x0 H).monodromy g
          (SubgroupQuotient.basepointFiber x0 H)) =
      QuotientGroup.mk g := by
  apply (TauCeti.IsCoveringMap.fiberEquivQuotientRange
    (isCoveringMap_subgroupQuotientProj x0 H) (SubgroupQuotient.basepointFiber x0 H)).symm.injective
  rw [Equiv.symm_apply_apply]
  exact (TauCeti.IsCoveringMap.fiberEquivQuotientRange_symm_apply_mk _ _ g).symm

/-- The subgroup that the subgroup quotient recovers at the distinguished point of its fibre is
`H` itself. This is `range_mapOfEq_subgroupQuotientProj`, phrased with the data appearing in the
codomain of `fiberEquivQuotientRange` so that the two compose. -/
private theorem range_mapOfEq_basepointFiber (H : Subgroup (FundamentalGroup X x0)) :
    (FundamentalGroup.mapOfEq
      ⟨subgroupQuotientProj x0 H, (isCoveringMap_subgroupQuotientProj x0 H).continuous⟩
      (SubgroupQuotient.basepointFiber x0 H).2).range = H :=
  range_mapOfEq_subgroupQuotientProj x0 H

/-- Raw-projection form of `stabilizerCoverFiberEquivOrbit`. -/
private def fiberEquivOrbitAux (a : A) :
    subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a) ⁻¹' {x0} ≃
      MulAction.orbit (FundamentalGroup X x0) a :=
  (TauCeti.IsCoveringMap.fiberEquivQuotientRange
        (isCoveringMap_subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a))
        (SubgroupQuotient.basepointFiber x0
          (MulAction.stabilizer (FundamentalGroup X x0) a))).trans <|
    (Subgroup.quotientEquivOfEq (range_mapOfEq_basepointFiber x0
        (MulAction.stabilizer (FundamentalGroup X x0) a))).trans
      (MulAction.orbitEquivQuotientStabilizer (FundamentalGroup X x0) a).symm

/-- Raw-projection form of `stabilizerCoverFiberEquivOrbit_apply_monodromy_basepoint`. -/
private theorem fiberEquivOrbitAux_apply_monodromy_basepoint (a : A)
    (g : FundamentalGroup X x0) :
    (fiberEquivOrbitAux x0 a
        ((isCoveringMap_subgroupQuotientProj x0
          (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy g
          (SubgroupQuotient.basepointFiber x0
            (MulAction.stabilizer (FundamentalGroup X x0) a))) : A) =
      g • a := by
  -- the fibre–coset identification sends the translate to the coset of `g`, and transporting
  -- along the equality of subgroups leaves that coset alone,
  simp only [fiberEquivOrbitAux, Equiv.trans_apply,
    fiberEquivQuotientRange_monodromy_basepointFiber, Subgroup.quotientEquivOfEq_mk]
  -- so orbit-stabilizer sends it to the translate of `a` by `g`.
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply (FundamentalGroup X x0) a g

/-- Raw-projection form of `stabilizerCoverFiberEquivOrbit_apply_monodromy`. -/
private theorem fiberEquivOrbitAux_apply_monodromy (a : A) (g : FundamentalGroup X x0)
    (e : subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a) ⁻¹' {x0}) :
    fiberEquivOrbitAux x0 a
        ((isCoveringMap_subgroupQuotientProj x0
          (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy g e) =
      g • fiberEquivOrbitAux x0 a e := by
  -- the quotient is path connected, so every point of the fibre is a monodromy translate of the
  -- distinguished point,
  obtain ⟨d, rfl⟩ := TauCeti.IsCoveringMap.exists_monodromy_eq
    (isCoveringMap_subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a))
    (SubgroupQuotient.basepointFiber x0 (MulAction.stabilizer (FundamentalGroup X x0) a)) e
  rw [← (isCoveringMap_subgroupQuotientProj x0
    (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy_trans_apply d g]
  -- Fundamental-group multiplication reverses path concatenation, so `d.trans g = g * d`.
  change fiberEquivOrbitAux x0 a
      ((isCoveringMap_subgroupQuotientProj x0
        (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy (g * d)
        (SubgroupQuotient.basepointFiber x0
          (MulAction.stabilizer (FundamentalGroup X x0) a))) =
    g • fiberEquivOrbitAux x0 a
      ((isCoveringMap_subgroupQuotientProj x0
        (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy d
        (SubgroupQuotient.basepointFiber x0
          (MulAction.stabilizer (FundamentalGroup X x0) a)))
  -- and both sides are then computed by the basepoint case.
  refine Subtype.ext ?_
  rw [MulAction.orbit.coe_smul, fiberEquivOrbitAux_apply_monodromy_basepoint,
    fiberEquivOrbitAux_apply_monodromy_basepoint, mul_smul]

/-- The fibre over `x₀` of the cover reconstructed from `a` is equivalent to the orbit of `a`.

Under this equivalence the distinguished point of the fibre corresponds to `a`; the equivariance
statements are `stabilizerCoverFiberEquivOrbit_apply_monodromy_basepoint` and
`stabilizerCoverFiberEquivOrbit_apply_monodromy`. -/
def stabilizerCoverFiberEquivOrbit (a : A) :
    ⇑(stabilizerCover x0 a).proj ⁻¹' {x0} ≃ MulAction.orbit (FundamentalGroup X x0) a :=
  fiberEquivOrbitAux x0 a

/-- The fibre equivalence sends the monodromy translate of the distinguished point of the fibre
to the corresponding translate of `a`. -/
@[simp]
theorem stabilizerCoverFiberEquivOrbit_apply_monodromy_basepoint (a : A)
    (g : FundamentalGroup X x0) :
    (stabilizerCoverFiberEquivOrbit x0 a
        ((stabilizerCover x0 a).isCoveringMap_proj.monodromy g
          (stabilizerCoverBasepointFiber x0 a)) : A) =
      g • a :=
  fiberEquivOrbitAux_apply_monodromy_basepoint x0 a g

/-- The fibre equivalence is equivariant: monodromy of the reconstructed cover agrees with the
given action of the fundamental group on the orbit of `a`. -/
theorem stabilizerCoverFiberEquivOrbit_apply_monodromy (a : A) (g : FundamentalGroup X x0)
    (e : ⇑(stabilizerCover x0 a).proj ⁻¹' {x0}) :
    stabilizerCoverFiberEquivOrbit x0 a
        ((stabilizerCover x0 a).isCoveringMap_proj.monodromy g e) =
      g • stabilizerCoverFiberEquivOrbit x0 a e :=
  fiberEquivOrbitAux_apply_monodromy x0 a g e

/-! ### Transitive actions -/

/-- For a transitive action, the fibre over `x₀` of the cover reconstructed from `a` is
equivalent to the whole `π₁(X, x₀)`-set, the orbit of `a` being everything. -/
def transitiveActionFiberEquiv [MulAction.IsPretransitive (FundamentalGroup X x0) A] (a : A) :
    ⇑(stabilizerCover x0 a).proj ⁻¹' {x0} ≃ A :=
  (stabilizerCoverFiberEquivOrbit x0 a).trans <|
    Equiv.subtypeUnivEquiv fun b : A =>
      (MulAction.orbit_eq_univ (FundamentalGroup X x0) a).symm ▸ Set.mem_univ b

/-- The fibre equivalence of a transitive action sends the monodromy translate of the
distinguished point of the fibre to the corresponding translate of `a`. -/
@[simp]
theorem transitiveActionFiberEquiv_apply_monodromy_basepoint
    [MulAction.IsPretransitive (FundamentalGroup X x0) A] (a : A)
    (g : FundamentalGroup X x0) :
    transitiveActionFiberEquiv x0 a
        ((stabilizerCover x0 a).isCoveringMap_proj.monodromy g
          (stabilizerCoverBasepointFiber x0 a)) =
      g • a := by
  simpa only [transitiveActionFiberEquiv, Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply] using
    stabilizerCoverFiberEquivOrbit_apply_monodromy_basepoint x0 a g

/-- The fibre equivalence of a transitive action is equivariant: monodromy of the reconstructed
cover agrees with the given action of the fundamental group on `A`. -/
theorem transitiveActionFiberEquiv_apply_monodromy
    [MulAction.IsPretransitive (FundamentalGroup X x0) A] (a : A) (g : FundamentalGroup X x0)
    (e : ⇑(stabilizerCover x0 a).proj ⁻¹' {x0}) :
    transitiveActionFiberEquiv x0 a
        ((stabilizerCover x0 a).isCoveringMap_proj.monodromy g e) =
      g • transitiveActionFiberEquiv x0 a e := by
  simp only [transitiveActionFiberEquiv, Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply]
  exact (congrArg Subtype.val (stabilizerCoverFiberEquivOrbit_apply_monodromy x0 a g e)).trans
    MulAction.orbit.coe_smul

end TauCeti.UniversalCover
