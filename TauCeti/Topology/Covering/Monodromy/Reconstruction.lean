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
# Reconstructing a connected cover from a transitive fundamental-group action

Let `A` be a transitive set for `π₁(X, x₀)`, and choose `a : A`. The stabilizer of `a` is a
subgroup of the fundamental group, so the universal-cover quotient by that stabilizer is a
connected covering space of `X`. Its fibre over `x₀` is equivariantly equivalent to `A`.

This is the object-level reconstruction in the classification of connected covers by transitive
fundamental-group actions. The construction deliberately reuses the cover attached to a subgroup
and orbit-stabilizer: no second topology on a reconstructed total space is introduced. A later
step can extend the equivariant equivalence on the base fibre to a natural isomorphism of
fundamental-groupoid actions and assemble the categorical equivalence.

## Main declarations

* `TauCeti.UniversalCover.SubgroupQuotient.basepointFiber`: the distinguished point of a
  subgroup quotient, bundled in the fibre over the basepoint.
* `TauCeti.UniversalCover.stabilizerCover`: the connected covering space obtained by
  quotienting the universal cover by the stabilizer of a point in a fundamental-group action.
* `TauCeti.UniversalCover.transitiveActionFiberEquiv`: the fibre of the cover obtained by
  quotienting by the stabilizer of `a` is equivalent to its transitive `π₁`-set.
* `TauCeti.UniversalCover.transitiveActionFiberEquiv_monodromy`: this equivalence intertwines
  covering-space monodromy with the given fundamental-group action.

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

namespace SubgroupQuotient

/-- The distinguished point of a subgroup quotient, regarded as a point of the fibre over the
basepoint. -/
def basepointFiber
    (H : Subgroup (FundamentalGroup X x0)) :
    (subgroupQuotientProj x0 H) ⁻¹' {x0} :=
  ⟨SubgroupQuotient.basepoint x0 H, by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      subgroupQuotientProj_basepoint x0 H⟩

/-- The underlying quotient point of `basepointFiber` is the distinguished point. -/
@[simp]
theorem basepointFiber_coe (H : Subgroup (FundamentalGroup X x0)) :
    (basepointFiber x0 H : SubgroupQuotient x0 H) = basepoint x0 H :=
  (rfl)

end SubgroupQuotient

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The connected covering space attached to a point `a` of a `π₁(X, x₀)`-set: it is the
universal cover modulo the stabilizer of `a`.

When the action is transitive, its fibre is the whole action; without transitivity, it represents
the orbit of `a`. -/
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

/-- The fibre over `x₀` of the universal-cover quotient by the stabilizer of `a` is equivalent
to the transitive fundamental-group set containing `a`.

Under this equivalence the distinguished quotient point corresponds to `a`; the stronger
equivariance statement is `transitiveActionFiberEquiv_monodromy`. -/
def transitiveActionFiberEquiv [MulAction.IsPretransitive (FundamentalGroup X x0) A]
    (a : A) :
    (subgroupQuotientProj x0 (MulAction.stabilizer (FundamentalGroup X x0) a)) ⁻¹' {x0} ≃ A :=
  let G := FundamentalGroup X x0
  let H := MulAction.stabilizer G a
  let p := subgroupQuotientProj x0 H
  let hp := isCoveringMap_subgroupQuotientProj x0 H
  let e0 : p ⁻¹' {x0} := SubgroupQuotient.basepointFiber x0 H
  let hRange :
      (FundamentalGroup.mapOfEq ⟨p, continuous_subgroupQuotientProj x0 H⟩ e0.2).range = H :=
    range_mapOfEq_subgroupQuotientProj x0 H
  (TauCeti.IsCoveringMap.fiberEquivQuotientRange hp e0).trans <|
    (Subgroup.quotientEquivOfEq hRange).trans <|
      (MulAction.orbitEquivQuotientStabilizer G a).symm.trans <|
        Equiv.subtypeUnivEquiv
          (fun b : A => (MulAction.orbit_eq_univ G a).symm ▸ Set.mem_univ b)

/-- The fibre equivalence sends the monodromy translate of the distinguished quotient point to
the corresponding translate of `a`. -/
@[simp]
theorem transitiveActionFiberEquiv_monodromy_basepoint
    [MulAction.IsPretransitive (FundamentalGroup X x0) A]
    (a : A) (g : FundamentalGroup X x0) :
    transitiveActionFiberEquiv x0 a
        ((isCoveringMap_subgroupQuotientProj x0
          (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy g
          (SubgroupQuotient.basepointFiber x0
            (MulAction.stabilizer (FundamentalGroup X x0) a))) =
      g • a := by
  let G := FundamentalGroup X x0
  let H := MulAction.stabilizer G a
  let p := subgroupQuotientProj x0 H
  let hp := isCoveringMap_subgroupQuotientProj x0 H
  let e0 : p ⁻¹' {x0} := SubgroupQuotient.basepointFiber x0 H
  let c := TauCeti.IsCoveringMap.fiberEquivQuotientRange hp e0
  have hc : c (hp.monodromy g e0) = QuotientGroup.mk g := by
    apply c.symm.injective
    rw [c.symm_apply_apply]
    exact (TauCeti.IsCoveringMap.fiberEquivQuotientRange_symm_apply_mk hp e0 g).symm
  simp only [transitiveActionFiberEquiv, G, H, e0, c, Equiv.trans_apply, hc,
    Equiv.subtypeUnivEquiv_apply]
  rfl

/-- The fibre equivalence is equivariant: monodromy on the stabilizer quotient agrees with the
given action of the fundamental group on `A`. -/
theorem transitiveActionFiberEquiv_monodromy
    [MulAction.IsPretransitive (FundamentalGroup X x0) A]
    (a : A) (g : FundamentalGroup X x0)
    (e : (subgroupQuotientProj x0
      (MulAction.stabilizer (FundamentalGroup X x0) a)) ⁻¹' {x0}) :
    transitiveActionFiberEquiv x0 a
        ((isCoveringMap_subgroupQuotientProj x0
          (MulAction.stabilizer (FundamentalGroup X x0) a)).monodromy g e) =
      g • transitiveActionFiberEquiv x0 a e := by
  let G := FundamentalGroup X x0
  let H := MulAction.stabilizer G a
  let p := subgroupQuotientProj x0 H
  let hp := isCoveringMap_subgroupQuotientProj x0 H
  let e0 : p ⁻¹' {x0} := SubgroupQuotient.basepointFiber x0 H
  let c := TauCeti.IsCoveringMap.fiberEquivQuotientRange hp e0
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (c e)
  have he : e = hp.monodromy d e0 := by
    apply c.injective
    calc
      c e = QuotientGroup.mk d := hd.symm
      _ = c (hp.monodromy d e0) := by
        apply c.symm.injective
        rw [c.symm_apply_apply]
        exact TauCeti.IsCoveringMap.fiberEquivQuotientRange_symm_apply_mk hp e0 d
  subst e
  rw [← hp.monodromy_trans_apply d g]
  -- Fundamental-group multiplication reverses path concatenation, so `d.trans g = g * d`.
  change transitiveActionFiberEquiv x0 a (hp.monodromy (g * d) e0) =
    g • transitiveActionFiberEquiv x0 a (hp.monodromy d e0)
  rw [transitiveActionFiberEquiv_monodromy_basepoint,
    transitiveActionFiberEquiv_monodromy_basepoint, mul_smul]

end TauCeti.UniversalCover
