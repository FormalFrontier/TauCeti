/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Rescale
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic

/-!
# Gauge independence of the additive preprojective algebra

The additive preprojective relator of a finite quiver `Q` is `ρ = ∑_a (a a* - a* a)`, one signed
commutator for each arrow `a` of `Q`. The choice of sign is a choice of orientation: an arrow and
its formal reverse enter `ρ` with opposite signs, and reversing the orientation of `a` exchanges
the two. The basic preprojective module records the whole family of *gauged* relators

```text
ρ_ε = ∑_a ε_a (a a* - a* a),
```

one for each labelling `ε` of the arrows of `Q` by scalars; this file proves that whenever two
labellings differ by a labelling by units the resulting quotients are isomorphic `k`-algebras. A
labelling `ε`
with values in `{1, -1}` records the sign with which each edge of the doubled quiver enters the
relator, so what is proved here is independence of the presented algebra under a change of those
signs, for one fixed quiver `Q` and hence one fixed doubled quiver. The isomorphism is the explicit
arrow rescaling `TauCeti.PathAlgebra.rescale`, which fixes every vertex idempotent and multiplies
each arrow of `Q` by the unit relating the two labellings; nothing is proved by declaring the
defining sum to be orientation-free. Comparing `TauCeti.preprojectiveAlgebra k Q` with the
preprojective algebra of a *reoriented* quiver `Q'` is a different statement, which this file does
not state and does not prove; see the implementation notes.

The relator is genuinely a sum over the *oriented edges* of the doubled quiver against an
antisymmetric labelling: `TauCeti.gaugedPreprojectiveRelator_eq_sum_backtracks` rewrites
`ρ_ε` as the paired contributions of `a` and `a*` for each original arrow `a`, whenever `ε`
negates under reversal. The `-` sign in `ρ_ε` is exactly the antisymmetry of the labelling.

## Main definitions

* `TauCeti.gaugedPreprojectiveRelator`: the gauged relator `ρ_ε`.
* `TauCeti.gaugedPreprojectiveIdeal`, `TauCeti.gaugedPreprojectiveAlgebra`,
  `TauCeti.gaugedPreprojectiveMk` and `TauCeti.gaugedPreprojectiveLift`: the quotient it presents,
  with its quotient map and universal property.
* `TauCeti.doubledLabelling`: the labelling of the doubled quiver carrying a labelling of `Q` on
  the arrows of `Q` and `1` on their formal reverses. Rescaling by it is the gauge transformation.

## Main results

* `TauCeti.gaugedPreprojectiveRelator_one`: at the constant labelling `1` the gauged relator is the
  preprojective relator, so the gauged algebras extend `TauCeti.preprojectiveAlgebra`.
* `TauCeti.rescale_gaugedPreprojectiveRelator`: rescaling the arrows of `Q` by `u` and fixing their
  reverses carries `ρ_ε` to `ρ_{uε}`.
* `TauCeti.gaugedPreprojectiveAlgebraEquiv`: **gauge independence**, two labellings differing by
  units present isomorphic algebras.
* `TauCeti.preprojectiveAlgebraEquivGauged`: every unit-valued gauge presents the preprojective
  algebra itself.
* `TauCeti.gaugedPreprojectiveRelator_eq_sum_backtracks`: the gauged relator pairs the two
  oriented-edge backtracks over each original arrow, for antisymmetric `ε`.

## Implementation notes

Reversing the orientation of an arrow of `Q` is here a change of the labelling `ε`, not a change of
the quiver: the results below establish gauge independence for the labellings of one fixed quiver
and hence in one fixed doubled path algebra. The reorientation form of orientation independence,
which compares `Q` with an explicit `Reorient Q σ`, is proved in
`TauCeti.RepresentationTheory.Quiver.Preprojective.Orientation`; it consumes the gauge
isomorphism below after identifying the two doubled path algebras.

## References

This is the gauge clause of Layer 4 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks
to reverse a chosen arrow by an algebra isomorphism rescaling one of the exchanged arrows by `-1`,
and then to generalize from signs to an antisymmetric sign function on oriented edges and prove
independence under the explicit gauge change. This file proves that gauge clause; the cross-quiver
clause preceding it is proved in
`TauCeti.RepresentationTheory.Quiver.Preprojective.Orientation`. See Crawley-Boevey, *Quiver
algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-! ### The gauged relator as an oriented-edge sum -/

section Relator

variable (k : Type w) {Q : Type u} [Ring k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **The gauged relator is a sum over the oriented edges of the doubled quiver.** For a labelling
`ε` which negates under reversal, the right-hand side pairs the two doubled arrows over each arrow
`a` of `Q`: `a` and its formal reverse `a*` contribute `ε_a (a a*)` and `-ε_a (a* a)`.
The subtraction in `ρ_ε` is the antisymmetry of `ε`. -/
theorem gaugedPreprojectiveRelator_eq_sum_backtracks
    (ε : ∀ ⦃x y : Symmetrify Q⦄, (x ⟶ y) → k)
    (hε : ∀ ⦃i j : Q⦄ (a : i ⟶ j),
      ε (Quiver.reverse (Symmetrify.of.map a)) = -ε (Symmetrify.of.map a)) :
    gaugedPreprojectiveRelator k (fun _ _ a => ε (Symmetrify.of.map a))
      = ∑ i : Q, ∑ j : Q, ∑ a : (i ⟶ j),
          (ε (Symmetrify.of.map a) • headBacktrackElem k a
            + ε (Quiver.reverse (Symmetrify.of.map a)) • tailBacktrackElem k a) := by
  simp only [gaugedPreprojectiveRelator_def, hε, neg_smul, ← sub_eq_add_neg, smul_sub]

end Relator

/-! ### The gauge transformation -/

section Gauge

variable (k : Type w) {Q : Type u} [Quiver.{v + 1} Q]

section Labelling

variable [One k]

/-- The **gauge labelling** of the doubled quiver attached to a labelling `u` of the arrows of `Q`:
it carries `u` on the arrows of `Q` and `1` on their formal reverses. Rescaling by it multiplies
both backtracks of an arrow `a` by `u a`. -/
def doubledLabelling (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) : ∀ ⦃x y : Symmetrify Q⦄, (x ⟶ y) → k :=
  fun _ _ b => Sum.elim (fun a => u a) (fun _ => 1) b

variable {k}

/-- The gauge labelling on an arrow of `Q` is the given label. -/
theorem doubledLabelling_of (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {i j : Q} (a : i ⟶ j) :
    doubledLabelling k u (Symmetrify.of.map a) = u a := by
  rw [doubledLabelling]
  rfl

/-- The gauge labelling on the formal reverse of an arrow of `Q` is one. -/
theorem doubledLabelling_reverse_of (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {i j : Q} (a : i ⟶ j) :
    doubledLabelling k u (Quiver.reverse (Symmetrify.of.map a)) = 1 := by
  rw [doubledLabelling]
  rfl

end Labelling

section LabellingMul

variable [Monoid k]

/-- Pointwise multiplication of labels on the original arrows becomes pointwise multiplication
of their gauge labellings on the doubled quiver. -/
theorem doubledLabelling_mul (u u' : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) ⦃x y : Symmetrify Q⦄ (b : x ⟶ y) :
    doubledLabelling k (fun _ _ a => u a * u' a) b
      = doubledLabelling k u b * doubledLabelling k u' b := by
  cases b <;> simp [doubledLabelling]

end LabellingMul

section RescaleBacktracks

variable [CommSemiring k] [Finite Q]

private theorem rescale_doubledLabelling_ofArrow_mul_ofArrow
    (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {x y z : Symmetrify Q} (a : y ⟶ z) (b : x ⟶ y) :
    rescale (doubledLabelling k u) (ofArrow a * ofArrow b)
      = (doubledLabelling k u a * doubledLabelling k u b) • (ofArrow a * ofArrow b) := by
  rw [map_mul, rescale_ofArrow, rescale_ofArrow, smul_mul_smul]

/-- Rescaling by a gauge labelling multiplies the head backtrack of `a` by the label of `a`. -/
@[simp]
theorem rescale_doubledLabelling_headBacktrackElem (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {i j : Q}
    (a : i ⟶ j) :
    rescale (doubledLabelling k u) (headBacktrackElem k a) = u a • headBacktrackElem k a := by
  rw [← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem,
    rescale_doubledLabelling_ofArrow_mul_ofArrow, doubledLabelling_of,
    doubledLabelling_reverse_of, mul_one, ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem]

/-- Rescaling by a gauge labelling multiplies the tail backtrack of `a` by the label of `a`. -/
@[simp]
theorem rescale_doubledLabelling_tailBacktrackElem (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {i j : Q}
    (a : i ⟶ j) :
    rescale (doubledLabelling k u) (tailBacktrackElem k a) = u a • tailBacktrackElem k a := by
  rw [← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem,
    rescale_doubledLabelling_ofArrow_mul_ofArrow, doubledLabelling_of,
    doubledLabelling_reverse_of, one_mul, ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem]

end RescaleBacktracks

section RescaleRelator

variable [CommRing k]

/-- **The gauge transformation acts on the gauged relators**: rescaling the arrows of `Q` by `u`
and fixing their formal reverses carries `ρ_ε` to `ρ_{uε}`. -/
theorem rescale_gaugedPreprojectiveRelator [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]
    (u ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) :
    rescale (doubledLabelling k u) (gaugedPreprojectiveRelator k ε)
      = gaugedPreprojectiveRelator k (fun _ _ a => u a * ε a) := by
  simp only [gaugedPreprojectiveRelator_def, map_sum, map_smul, map_sub,
    rescale_doubledLabelling_headBacktrackElem, rescale_doubledLabelling_tailBacktrackElem,
    ← smul_sub, smul_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun a _ => by rw [mul_comm]

end RescaleRelator

section RescaleComposition

variable [CommSemiring k] [Finite Q]

/-- Two gauge rescalings whose labellings are pointwise inverse compose to the identity. -/
theorem rescale_doubledLabelling_comp (u u' : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), u a * u' a = 1) :
    (rescale (doubledLabelling k u)).comp (rescale (doubledLabelling k u'))
      = AlgHom.id k (pathAlgebra k (Symmetrify Q)) := by
  rw [rescale_comp_rescale, ← rescale_one]
  apply rescale_congr
  intro _ _ b
  rw [← doubledLabelling_mul]
  cases b with
  | inl a => simpa [doubledLabelling] using h a
  | inr a => simp [doubledLabelling]

/-- Two gauge rescalings whose labellings are pointwise inverse undo one another. -/
theorem rescale_doubledLabelling_rescale_doubledLabelling (u u' : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), u a * u' a = 1) (z : pathAlgebra k (Symmetrify Q)) :
    rescale (doubledLabelling k u) (rescale (doubledLabelling k u') z) = z := by
  rw [← AlgHom.comp_apply, rescale_doubledLabelling_comp k u u' h, AlgHom.id_apply]

end RescaleComposition

end Gauge

/-! ### Gauge independence -/

section Independence

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **Gauge independence of the preprojective algebra.** Two labellings of the arrows of `Q` which
differ by a labelling `u` by units present isomorphic algebras: the isomorphism is the arrow
rescaling by `u`, which fixes every vertex idempotent and multiplies each arrow of `Q` by `u`,
leaving its formal reverse alone. Taking `u` to be `-1` on one arrow and `1` on the others flips
the sign with which that arrow enters the relator, which is what reversing its orientation
produces once the two doubled quivers are identified; that identification is not carried out here,
so this is a statement about two labellings of the one quiver `Q`, not about two quivers. See the
implementation notes. -/
noncomputable def gaugedPreprojectiveAlgebraEquiv (ε ε' : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → kˣ)
    (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), ε' a = ((u a : kˣ) : k) * ε a) :
    gaugedPreprojectiveAlgebra k ε ≃ₐ[k] gaugedPreprojectiveAlgebra k ε' :=
  AlgEquiv.ofAlgHom
    (gaugedPreprojectiveLift k ε
      ((gaugedPreprojectiveMk k ε').comp
        (rescale (doubledLabelling k fun _ _ a => ((u a : kˣ) : k))))
      (by
        rw [AlgHom.comp_apply, rescale_gaugedPreprojectiveRelator,
          gaugedPreprojectiveRelator_congr k (ε := fun _ _ a => ((u a : kˣ) : k) * ε a) (ε' := ε')
            (fun _ _ a => (h a).symm),
          gaugedPreprojectiveMk_gaugedPreprojectiveRelator]))
    (gaugedPreprojectiveLift k ε'
      ((gaugedPreprojectiveMk k ε).comp
        (rescale (doubledLabelling k fun _ _ a => (((u a)⁻¹ : kˣ) : k))))
      (by
        rw [AlgHom.comp_apply, rescale_gaugedPreprojectiveRelator,
          gaugedPreprojectiveRelator_congr k (ε := fun _ _ a => (((u a)⁻¹ : kˣ) : k) * ε' a)
            (ε' := ε) (fun _ _ a => by rw [h a, ← mul_assoc, Units.inv_mul, one_mul]),
          gaugedPreprojectiveMk_gaugedPreprojectiveRelator]))
    (AlgHom.ext fun y => by
      obtain ⟨x, rfl⟩ := gaugedPreprojectiveMk_surjective k ε' y
      simp only [AlgHom.comp_apply, gaugedPreprojectiveLift_gaugedPreprojectiveMk, AlgHom.id_apply,
        rescale_doubledLabelling_rescale_doubledLabelling k _ _ (fun _ _ a => Units.mul_inv (u a))])
    (AlgHom.ext fun y => by
      obtain ⟨x, rfl⟩ := gaugedPreprojectiveMk_surjective k ε y
      simp only [AlgHom.comp_apply, gaugedPreprojectiveLift_gaugedPreprojectiveMk, AlgHom.id_apply,
        rescale_doubledLabelling_rescale_doubledLabelling k _ _ (fun _ _ a => Units.inv_mul (u a))])

/-- **The gauge isomorphism is the arrow rescaling**: on an arbitrary quotient representative,
it applies the path-algebra rescaling and then the target quotient map. -/
@[simp]
theorem gaugedPreprojectiveAlgebraEquiv_gaugedPreprojectiveMk (ε ε' : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → kˣ)
    (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), ε' a = ((u a : kˣ) : k) * ε a)
    (x : pathAlgebra k (Symmetrify Q)) :
    gaugedPreprojectiveAlgebraEquiv k ε ε' u h (gaugedPreprojectiveMk k ε x)
      = gaugedPreprojectiveMk k ε'
          (rescale (doubledLabelling k fun _ _ a => ((u a : kˣ) : k)) x) := by
  rw [gaugedPreprojectiveAlgebraEquiv, ← AlgEquiv.coe_toAlgHom, AlgEquiv.toAlgHom_ofAlgHom,
    gaugedPreprojectiveLift_gaugedPreprojectiveMk, AlgHom.comp_apply]

/-- The inverse gauge isomorphism is rescaling by the pointwise inverse units. -/
@[simp]
theorem gaugedPreprojectiveAlgebraEquiv_symm_gaugedPreprojectiveMk
    (ε ε' : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → kˣ)
    (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), ε' a = ((u a : kˣ) : k) * ε a)
    (x : pathAlgebra k (Symmetrify Q)) :
    (gaugedPreprojectiveAlgebraEquiv k ε ε' u h).symm (gaugedPreprojectiveMk k ε' x)
      = gaugedPreprojectiveMk k ε
          (rescale (doubledLabelling k fun _ _ a => (((u a)⁻¹ : kˣ) : k)) x) := by
  apply (gaugedPreprojectiveAlgebraEquiv k ε ε' u h).injective
  rw [AlgEquiv.apply_symm_apply, gaugedPreprojectiveAlgebraEquiv_gaugedPreprojectiveMk,
    rescale_doubledLabelling_rescale_doubledLabelling k _ _
      (fun _ _ a => Units.mul_inv (u a))]

/-- The canonical identification of the original presentation with the constant gauge `1`. -/
noncomputable def preprojectiveAlgebraEquivGaugedOne :
    preprojectiveAlgebra k Q ≃ₐ[k]
      gaugedPreprojectiveAlgebra (Q := Q) k (fun _ _ _ => 1) :=
  Ideal.quotientEquivAlgOfEq k <| congrArg TwoSidedIdeal.asIdeal <| by
    rw [preprojectiveIdeal_eq_span, gaugedPreprojectiveIdeal_eq_span,
      gaugedPreprojectiveRelator_one]

/-- The constant-gauge identification preserves the quotient generators. -/
@[simp]
theorem preprojectiveAlgebraEquivGaugedOne_preprojectiveMk
    (x : pathAlgebra k (Symmetrify Q)) :
    preprojectiveAlgebraEquivGaugedOne (Q := Q) k (preprojectiveMk k Q x)
      = gaugedPreprojectiveMk k (fun _ _ _ => 1) x := by
  rw [preprojectiveAlgebraEquivGaugedOne, preprojectiveMk_apply,
    gaugedPreprojectiveMk_apply, Ideal.quotientEquivAlgOfEq_mk]

/-- The inverse constant-gauge identification preserves the quotient generators. -/
@[simp]
theorem preprojectiveAlgebraEquivGaugedOne_symm_gaugedPreprojectiveMk
    (x : pathAlgebra k (Symmetrify Q)) :
    (preprojectiveAlgebraEquivGaugedOne (Q := Q) k).symm
        (gaugedPreprojectiveMk k (fun _ _ _ => 1) x) = preprojectiveMk k Q x := by
  rw [AlgEquiv.symm_apply_eq, preprojectiveAlgebraEquivGaugedOne_preprojectiveMk]

/-- **Every unit-valued gauge presents the preprojective algebra.** In particular a labelling of
the arrows of `Q` by signs presents `Π_k(Q)` for every choice of signs. -/
noncomputable def preprojectiveAlgebraEquivGauged (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → kˣ) (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), ε a = ((u a : kˣ) : k)) :
    preprojectiveAlgebra k Q ≃ₐ[k] gaugedPreprojectiveAlgebra k ε :=
  (preprojectiveAlgebraEquivGaugedOne (Q := Q) k).trans <|
    gaugedPreprojectiveAlgebraEquiv k (fun _ _ _ => 1) ε u fun _ _ a => by rw [h a, mul_one]

/-- The isomorphism onto a unit-valued gauge applies arrow rescaling to an arbitrary quotient
representative and then takes its class in the gauged quotient. -/
@[simp]
theorem preprojectiveAlgebraEquivGauged_preprojectiveMk (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → kˣ) (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), ε a = ((u a : kˣ) : k))
    (x : pathAlgebra k (Symmetrify Q)) :
    preprojectiveAlgebraEquivGauged k ε u h (preprojectiveMk k Q x)
      = gaugedPreprojectiveMk k ε
          (rescale (doubledLabelling k fun _ _ a => ((u a : kˣ) : k)) x) := by
  rw [preprojectiveAlgebraEquivGauged, AlgEquiv.trans_apply,
    preprojectiveAlgebraEquivGaugedOne_preprojectiveMk,
    gaugedPreprojectiveAlgebraEquiv_gaugedPreprojectiveMk]

/-- The inverse isomorphism from a unit-valued gauge, computed on quotient generators. -/
@[simp]
theorem preprojectiveAlgebraEquivGauged_symm_gaugedPreprojectiveMk
    (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → kˣ)
    (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), ε a = ((u a : kˣ) : k))
    (x : pathAlgebra k (Symmetrify Q)) :
    (preprojectiveAlgebraEquivGauged k ε u h).symm (gaugedPreprojectiveMk k ε x)
      = preprojectiveMk k Q
          (rescale (doubledLabelling k fun _ _ a => (((u a)⁻¹ : kˣ) : k)) x) := by
  apply (preprojectiveAlgebraEquivGauged k ε u h).injective
  rw [AlgEquiv.apply_symm_apply, preprojectiveAlgebraEquivGauged_preprojectiveMk,
    rescale_doubledLabelling_rescale_doubledLabelling k _ _
      (fun _ _ a => Units.mul_inv (u a))]

end Independence

end TauCeti
