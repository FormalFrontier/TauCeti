/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
public import TauCeti.Topology.Homotopy.Monodromy.Basic
import TauCeti.Topology.Homotopy.Monodromy.Functoriality

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
  subgroupCover x0 (MulAction.stabilizer (FundamentalGroup X x0) a)

/-- The stabilizer cover is the subgroup cover associated to the stabilizer of `a`. -/
theorem stabilizerCover_eq_subgroupCover (a : A) :
    stabilizerCover x0 a =
      subgroupCover x0 (MulAction.stabilizer (FundamentalGroup X x0) a) :=
  (rfl)

/-- The projection of the stabilizer cover is the projection of its subgroup cover, after
transporting along the characteristic equality of covers. -/
@[simp]
theorem stabilizerCover_proj (a : A) :
    (stabilizerCover x0 a).proj =
      eqToHom (congrArg (fun p : ConnectedCoveringSpace (TopCat.of X) => (p : TopCat))
        (stabilizerCover_eq_subgroupCover x0 a)) ≫
        (subgroupCover x0 (MulAction.stabilizer (FundamentalGroup X x0) a)).proj :=
  (rfl)

/-- Transport from the fibre of the stabilizer cover to the fibre of the corresponding subgroup
cover. -/
def stabilizerCoverFiberEquivSubgroupCover (a : A) :
    ⇑(stabilizerCover x0 a).proj ⁻¹' {x0} ≃
      ⇑(subgroupCover x0 (MulAction.stabilizer (FundamentalGroup X x0) a)).proj ⁻¹' {x0} :=
  Equiv.cast <| congrArg
    (fun p : ConnectedCoveringSpace (TopCat.of X) =>
      p.isCoveringMap_proj.monodromyFunctor.obj (FundamentalGroupoid.mk x0))
    (stabilizerCover_eq_subgroupCover x0 a)

/-- The distinguished point of the fibre over `x₀` of the cover reconstructed from `a`: the
class of the constant path at the basepoint. -/
def stabilizerCoverBasepointFiber (a : A) : ⇑(stabilizerCover x0 a).proj ⁻¹' {x0} :=
  (stabilizerCoverFiberEquivSubgroupCover x0 a).symm <|
    subgroupCoverBasepointFiber x0 (MulAction.stabilizer (FundamentalGroup X x0) a)

/-- Fibre transport identifies the distinguished point of the stabilizer cover with that of its
subgroup cover. -/
@[simp]
theorem stabilizerCoverFiberEquivSubgroupCover_basepoint (a : A) :
    stabilizerCoverFiberEquivSubgroupCover x0 a (stabilizerCoverBasepointFiber x0 a) =
      subgroupCoverBasepointFiber x0 (MulAction.stabilizer (FundamentalGroup X x0) a) :=
  Equiv.apply_symm_apply _ _

omit [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] in
/-- Fibre transport to an equal connected cover commutes with monodromy. -/
private theorem fiberCast_apply_monodromy (p q : ConnectedCoveringSpace (TopCat.of X))
    (h : p = q) (g : FundamentalGroup X x0) (e : ⇑p.proj ⁻¹' {x0}) :
    Equiv.cast (congrArg
        (fun r : ConnectedCoveringSpace (TopCat.of X) =>
          r.isCoveringMap_proj.monodromyFunctor.obj (FundamentalGroupoid.mk x0)) h)
        (p.isCoveringMap_proj.monodromy g e) =
      q.isCoveringMap_proj.monodromy g
        (Equiv.cast (congrArg
          (fun r : ConnectedCoveringSpace (TopCat.of X) =>
            r.isCoveringMap_proj.monodromyFunctor.obj (FundamentalGroupoid.mk x0)) h) e) := by
  subst q
  rfl

/-- Fibre transport from the stabilizer cover to its subgroup cover commutes with monodromy. -/
@[simp]
theorem stabilizerCoverFiberEquivSubgroupCover_apply_monodromy (a : A)
    (g : FundamentalGroup X x0) (e : ⇑(stabilizerCover x0 a).proj ⁻¹' {x0}) :
    stabilizerCoverFiberEquivSubgroupCover x0 a
        ((stabilizerCover x0 a).isCoveringMap_proj.monodromy g e) =
      (subgroupCover x0
        (MulAction.stabilizer (FundamentalGroup X x0) a)).isCoveringMap_proj.monodromy g
        (stabilizerCoverFiberEquivSubgroupCover x0 a e) :=
  fiberCast_apply_monodromy x0 _ _ (stabilizerCover_eq_subgroupCover x0 a) g e

/-! ### The fibre as an orbit

The equivalence and its equivariance are first proved for the underlying quotient projection,
which carries the instances the orbit-stabilizer API needs, and are then transported to the
bundled cover along the fibre transport above. -/

/-- Raw-projection form of `stabilizerCoverFiberEquivOrbit`. -/
private def fiberEquivOrbitAux (a : A) :
    subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a) ⁻¹' {x0} ≃
      MulAction.orbit (FundamentalGroup X x0) a :=
  (TauCeti.IsCoveringMap.fiberEquivQuotientRange
        (isCoveringMap_subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a))
        (SubgroupQuotient.basepointFiber x0
          (MulAction.stabilizer (FundamentalGroup X x0) a))).trans <|
    (Subgroup.quotientEquivOfEq (by
        -- the recovered subgroup is the stabilizer by `range_mapOfEq_subgroupQuotientProj`, which
        -- is stated at the distinguished point rather than at the point of the fibre carrying it
        rw [show SubgroupQuotient.basepointFiber x0
              (MulAction.stabilizer (FundamentalGroup X x0) a) =
            ⟨SubgroupQuotient.basepoint x0 (MulAction.stabilizer (FundamentalGroup X x0) a), by
              simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
                subgroupQuotientProj_basepoint x0 _⟩ from
          Subtype.ext (SubgroupQuotient.basepointFiber_coe x0 _)]
        exact range_mapOfEq_subgroupQuotientProj x0 _)).trans
      (MulAction.orbitEquivQuotientStabilizer (FundamentalGroup X x0) a).symm

/-- The raw fibre equivalence sends a monodromy translate of the quotient basepoint to the
corresponding translate of `a`. -/
private theorem fiberEquivOrbitAux_apply_monodromy_basepoint (a : A)
    (g : FundamentalGroup X x0) :
    (fiberEquivOrbitAux x0 a
        ((isCoveringMap_subgroupQuotientProj x0
          (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy g
          (SubgroupQuotient.basepointFiber x0
            (MulAction.stabilizer (FundamentalGroup X x0) a))) : A) =
      g • a := by
  -- the monodromy translate of the distinguished point is the fibre–coset identification of the
  -- coset of `g`,
  rw [← TauCeti.IsCoveringMap.fiberEquivQuotientRange_symm_apply_mk
    (isCoveringMap_subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a))
    (SubgroupQuotient.basepointFiber x0 (MulAction.stabilizer (FundamentalGroup X x0) a)) g]
  -- transporting along the equality of subgroups leaves that coset alone,
  simp only [fiberEquivOrbitAux, Equiv.trans_apply, Equiv.apply_symm_apply,
    Subgroup.quotientEquivOfEq_mk]
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
  -- so the iterated translate is the translate by a product, fundamental-group multiplication
  -- reversing path concatenation,
  have hmul : (isCoveringMap_subgroupQuotientProj x0
        (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy g
      ((isCoveringMap_subgroupQuotientProj x0
        (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy d
        (SubgroupQuotient.basepointFiber x0
          (MulAction.stabilizer (FundamentalGroup X x0) a))) =
      (isCoveringMap_subgroupQuotientProj x0
        (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy (g * d)
        (SubgroupQuotient.basepointFiber x0
          (MulAction.stabilizer (FundamentalGroup X x0) a)) := by
    rw [FundamentalGroup.mul_def, IsCoveringMap.monodromy_trans_apply]
  rw [hmul]
  -- and both sides are then computed by the basepoint case.
  refine Subtype.ext ?_
  rw [MulAction.orbit.coe_smul, fiberEquivOrbitAux_apply_monodromy_basepoint,
    fiberEquivOrbitAux_apply_monodromy_basepoint, mul_smul]

/-- The fibre over `x₀` of the cover reconstructed from `a` is equivalent to the orbit of `a`.

Under this equivalence the distinguished point of the fibre corresponds to `a`, by
`stabilizerCoverFiberEquivOrbit_apply_basepoint`; the equivariance statement is
`stabilizerCoverFiberEquivOrbit_apply_monodromy`. -/
def stabilizerCoverFiberEquivOrbit (a : A) :
    ⇑(stabilizerCover x0 a).proj ⁻¹' {x0} ≃ MulAction.orbit (FundamentalGroup X x0) a :=
  (stabilizerCoverFiberEquivSubgroupCover x0 a).trans <|
    (subgroupCoverFiberEquivSubgroupQuotient x0
      (MulAction.stabilizer (FundamentalGroup X x0) a)).trans (fiberEquivOrbitAux x0 a)

/-- The fibre equivalence sends the distinguished point of the fibre to `a`. -/
@[simp]
theorem stabilizerCoverFiberEquivOrbit_apply_basepoint (a : A) :
    stabilizerCoverFiberEquivOrbit x0 a (stabilizerCoverBasepointFiber x0 a) =
      ⟨a, MulAction.mem_orbit_self a⟩ := by
  refine Subtype.ext ?_
  simp only [stabilizerCoverFiberEquivOrbit, Equiv.trans_apply]
  rw [stabilizerCoverFiberEquivSubgroupCover_basepoint,
    subgroupCoverFiberEquivSubgroupQuotient_basepoint]
  -- the distinguished point is its own translate by the identity loop class
  have h := fiberEquivOrbitAux_apply_monodromy_basepoint x0 a 1
  rwa [one_smul, FundamentalGroup.one_def,
    (isCoveringMap_subgroupQuotientProj x0
      (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy_refl, id_eq] at h

/-- The fibre equivalence is equivariant: monodromy of the reconstructed cover agrees with the
given action of the fundamental group on the orbit of `a`. -/
@[simp]
theorem stabilizerCoverFiberEquivOrbit_apply_monodromy (a : A) (g : FundamentalGroup X x0)
    (e : ⇑(stabilizerCover x0 a).proj ⁻¹' {x0}) :
    stabilizerCoverFiberEquivOrbit x0 a
        ((stabilizerCover x0 a).isCoveringMap_proj.monodromy g e) =
      g • stabilizerCoverFiberEquivOrbit x0 a e := by
  simp only [stabilizerCoverFiberEquivOrbit, Equiv.trans_apply]
  rw [stabilizerCoverFiberEquivSubgroupCover_apply_monodromy]
  rw [subgroupCoverFiberEquivSubgroupQuotient_apply_monodromy]
  exact fiberEquivOrbitAux_apply_monodromy x0 a g
    (subgroupCoverFiberEquivSubgroupQuotient x0
      (MulAction.stabilizer (FundamentalGroup X x0) a)
      (stabilizerCoverFiberEquivSubgroupCover x0 a e))

/-! ### Transitive actions -/

/-- For a transitive action, the fibre over `x₀` of the cover reconstructed from `a` is
equivalent to the whole `π₁(X, x₀)`-set, the orbit of `a` being everything.

Under this equivalence the distinguished point of the fibre corresponds to `a`, by
`transitiveActionFiberEquiv_apply_basepoint`. -/
def transitiveActionFiberEquiv [MulAction.IsPretransitive (FundamentalGroup X x0) A] (a : A) :
    ⇑(stabilizerCover x0 a).proj ⁻¹' {x0} ≃ A :=
  (stabilizerCoverFiberEquivOrbit x0 a).trans <|
    Equiv.subtypeUnivEquiv fun b : A =>
      (MulAction.orbit_eq_univ (FundamentalGroup X x0) a).symm ▸ Set.mem_univ b

/-- The fibre equivalence of a transitive action sends the distinguished point of the fibre
to `a`. -/
@[simp]
theorem transitiveActionFiberEquiv_apply_basepoint
    [MulAction.IsPretransitive (FundamentalGroup X x0) A] (a : A) :
    transitiveActionFiberEquiv x0 a (stabilizerCoverBasepointFiber x0 a) = a := by
  simpa only [transitiveActionFiberEquiv, Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply] using
    congrArg Subtype.val (stabilizerCoverFiberEquivOrbit_apply_basepoint x0 a)

/-- The fibre equivalence of a transitive action is equivariant: monodromy of the reconstructed
cover agrees with the given action of the fundamental group on `A`. -/
@[simp]
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
