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
the two. This file records the whole family of *gauged* relators

```text
ρ_ε = ∑_a ε_a (a a* - a* a),
```

one for each labelling `ε` of the arrows of `Q` by scalars, and proves that whenever two labellings
differ by a labelling by units the resulting quotients are isomorphic `k`-algebras. A labelling `ε`
with values in `{1, -1}` records the sign with which each edge of the doubled quiver enters the
relator, so what is proved here is independence of the presented algebra under a change of those
signs, for one fixed quiver `Q` and hence one fixed doubled quiver. The isomorphism is the explicit
arrow rescaling `TauCeti.PathAlgebra.rescale`, which fixes every vertex idempotent and multiplies
each arrow of `Q` by the unit relating the two labellings; nothing is proved by declaring the
defining sum to be orientation-free. Comparing `TauCeti.preprojectiveAlgebra k Q` with the
preprojective algebra of a *reoriented* quiver `Q'` is a different statement, which this file does
not state and does not prove; see the implementation notes.

The relator is genuinely a sum over the *oriented edges* of the doubled quiver against an
antisymmetric labelling: `TauCeti.gaugedPreprojectiveRelator_eq_sum_doubledBacktrackElem` rewrites
`ρ_ε` as `∑_b ε_b (b b*)`, over all arrows `b` of the doubled quiver, whenever `ε` negates under
reversal. The `-` sign in `ρ_ε` is exactly the antisymmetry of the labelling.

## Main definitions

* `TauCeti.doubledBacktrackElem`: the backtrack `b b*` of an arrow `b` of the doubled quiver.
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
* `TauCeti.gaugedPreprojectiveRelator_eq_sum_doubledBacktrackElem`: the gauged relator is the sum
  of `ε_b (b b*)` over the oriented edges `b` of the doubled quiver, for antisymmetric `ε`.

## Implementation notes

Reversing the orientation of an arrow of `Q` is here a change of the labelling `ε`, not a change of
the quiver: the doubled quiver, and therefore the ambient path algebra, is the same for `Q` and for
any reorientation of its arrows, and only the sign attached to each oriented edge moves.
Comparing the algebras of two *different* quivers with a common underlying graph additionally needs
the path-algebra isomorphism induced by an isomorphism of doubled quivers, which does not exist in
this repository and is not built here. So the cross-quiver form of orientation independence, which
quantifies over two quivers with a common underlying graph, is deliberately left unstated by this
file; every statement below is about the labellings of one fixed quiver.

## References

This is the gauge clause of Layer 4 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks
to reverse a chosen arrow by an algebra isomorphism rescaling one of the exchanged arrows by `-1`,
and then to generalize from signs to an antisymmetric sign function on oriented edges and prove
independence under the explicit gauge change. This file proves that gauge clause; the cross-quiver
clause preceding it is not proved here. See Crawley-Boevey, *Quiver algebras, weighted
projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-! ### Backtracks of the doubled quiver -/

section DoubledBacktrack

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v + 1} Q] [Finite Q]

/-- The **backtrack** `b b*` of an arrow `b` of the doubled quiver: the length-two loop at the head
of `b` which traverses the formal reverse of `b` and then `b`. -/
noncomputable def doubledBacktrackElem {x y : Symmetrify Q} (b : x ⟶ y) :
    pathAlgebra k (Symmetrify Q) :=
  ofArrow b * ofArrow (Quiver.reverse b)

omit [Finite Q] in
/-- Over an arrow of `Q` itself, the doubled backtrack is the head backtrack `a a*`. -/
theorem doubledBacktrackElem_of {i j : Q} (a : i ⟶ j) :
    doubledBacktrackElem k (Symmetrify.of.map a) = headBacktrackElem k a := by
  rw [doubledBacktrackElem, ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem]

omit [Finite Q] in
/-- Over the formal reverse of an arrow of `Q`, the doubled backtrack is the tail backtrack
`a* a`. -/
theorem doubledBacktrackElem_reverse_of {i j : Q} (a : i ⟶ j) :
    doubledBacktrackElem k (Quiver.reverse (Symmetrify.of.map a)) = tailBacktrackElem k a := by
  rw [doubledBacktrackElem, Quiver.reverse_reverse,
    ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem]

end DoubledBacktrack

/-! ### The gauged relator -/

section Relator

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- The **gauged preprojective relator** `ρ_ε = ∑_a ε_a (a a* - a* a)` attached to a labelling `ε`
of the arrows of `Q` by scalars. The constant labelling `1` gives the preprojective relator. -/
noncomputable def gaugedPreprojectiveRelator (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) :
    pathAlgebra k (Symmetrify Q) :=
  ∑ i : Q, ∑ j : Q, ∑ a : (i ⟶ j), ε a • (headBacktrackElem k a - tailBacktrackElem k a)

/-- Pointwise equal labellings give the same gauged relator. -/
theorem gaugedPreprojectiveRelator_congr {ε ε' : ∀ ⦃i j : Q⦄, (i ⟶ j) → k}
    (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), ε a = ε' a) :
    gaugedPreprojectiveRelator k ε = gaugedPreprojectiveRelator k ε' := by
  simp only [gaugedPreprojectiveRelator]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun a _ => by rw [h a]

/-- **The constant gauge `1` is the preprojective relator.** -/
@[simp]
theorem gaugedPreprojectiveRelator_one :
    gaugedPreprojectiveRelator k (fun _ _ _ => (1 : k)) = preprojectiveRelator k Q := by
  rw [gaugedPreprojectiveRelator, preprojectiveRelator_def]
  simp only [one_smul]

/-- **The gauged relator is a sum over the oriented edges of the doubled quiver.** For a labelling
`ε` of the doubled quiver which negates under reversal, `ρ_ε` is `∑_b ε_b (b b*)`, summed over all
arrows `b` of the doubled quiver: the arrow `a` of `Q` and its formal reverse `a*` contribute
`ε_a (a a*)` and `-ε_a (a* a)`. The subtraction in `ρ_ε` is the antisymmetry of `ε`. -/
theorem gaugedPreprojectiveRelator_eq_sum_doubledBacktrackElem
    (ε : ∀ ⦃x y : Symmetrify Q⦄, (x ⟶ y) → k)
    (hε : ∀ ⦃x y : Symmetrify Q⦄ (b : x ⟶ y), ε (Quiver.reverse b) = -ε b) :
    gaugedPreprojectiveRelator k (fun _ _ a => ε (Symmetrify.of.map a))
      = ∑ i : Q, ∑ j : Q, ∑ a : (i ⟶ j),
          (ε (Symmetrify.of.map a) • doubledBacktrackElem k (Symmetrify.of.map a)
            + ε (Quiver.reverse (Symmetrify.of.map a)) •
              doubledBacktrackElem k (Quiver.reverse (Symmetrify.of.map a))) := by
  simp only [gaugedPreprojectiveRelator, doubledBacktrackElem_of, doubledBacktrackElem_reverse_of,
    hε, neg_smul, ← sub_eq_add_neg, smul_sub]

end Relator

/-! ### The gauged relation ideal and its quotient -/

section Algebra

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)] (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)

/-- The two-sided ideal generated by the gauged preprojective relator. -/
noncomputable def gaugedPreprojectiveIdeal : TwoSidedIdeal (pathAlgebra k (Symmetrify Q)) :=
  TwoSidedIdeal.span {gaugedPreprojectiveRelator k ε}

theorem gaugedPreprojectiveRelator_mem_gaugedPreprojectiveIdeal :
    gaugedPreprojectiveRelator k ε ∈ gaugedPreprojectiveIdeal k ε :=
  TwoSidedIdeal.subset_span rfl

/-- At the constant gauge `1` the gauged ideal is the preprojective ideal. -/
theorem gaugedPreprojectiveIdeal_one :
    gaugedPreprojectiveIdeal k (fun _ _ _ => (1 : k)) = preprojectiveIdeal k Q := by
  rw [gaugedPreprojectiveIdeal, preprojectiveIdeal_eq_span, gaugedPreprojectiveRelator_one]

/-- The **gauged preprojective algebra** `Π_k(Q, ε)`: the path algebra of the doubled quiver modulo
the gauged relator. -/
noncomputable abbrev gaugedPreprojectiveAlgebra : Type _ :=
  pathAlgebra k (Symmetrify Q) ⧸ (gaugedPreprojectiveIdeal k ε).asIdeal

/-- The quotient map onto the gauged preprojective algebra. -/
noncomputable def gaugedPreprojectiveMk :
    pathAlgebra k (Symmetrify Q) →ₐ[k] gaugedPreprojectiveAlgebra k ε :=
  Ideal.Quotient.mkₐ k _

theorem gaugedPreprojectiveMk_apply (f : pathAlgebra k (Symmetrify Q)) :
    gaugedPreprojectiveMk k ε f = Ideal.Quotient.mk (gaugedPreprojectiveIdeal k ε).asIdeal f := by
  rw [gaugedPreprojectiveMk, Ideal.Quotient.mkₐ_eq_mk]

theorem gaugedPreprojectiveMk_surjective : Function.Surjective (gaugedPreprojectiveMk k ε) :=
  Ideal.Quotient.mk_surjective

@[simp]
theorem gaugedPreprojectiveMk_eq_zero_iff {f : pathAlgebra k (Symmetrify Q)} :
    gaugedPreprojectiveMk k ε f = 0 ↔ f ∈ gaugedPreprojectiveIdeal k ε := by
  rw [gaugedPreprojectiveMk_apply, Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal]

@[simp]
theorem gaugedPreprojectiveMk_gaugedPreprojectiveRelator :
    gaugedPreprojectiveMk k ε (gaugedPreprojectiveRelator k ε) = 0 :=
  (gaugedPreprojectiveMk_eq_zero_iff k ε).2
    (gaugedPreprojectiveRelator_mem_gaugedPreprojectiveIdeal k ε)

variable {B : Type*} [Ring B] [Algebra k B] (f : pathAlgebra k (Symmetrify Q) →ₐ[k] B)

/-- **The universal property of the gauged preprojective algebra**: an algebra map out of the
doubled path algebra which kills the gauged relator descends to the quotient. -/
noncomputable def gaugedPreprojectiveLift (hf : f (gaugedPreprojectiveRelator k ε) = 0) :
    gaugedPreprojectiveAlgebra k ε →ₐ[k] B :=
  Ideal.Quotient.liftₐ _ f fun _ ha =>
    (TwoSidedIdeal.mem_ker f).1
      (TwoSidedIdeal.span_le.2 (Set.singleton_subset_iff.2 ((TwoSidedIdeal.mem_ker f).2 hf))
        (TwoSidedIdeal.mem_asIdeal.1 ha))

theorem gaugedPreprojectiveLift_comp_gaugedPreprojectiveMk
    (hf : f (gaugedPreprojectiveRelator k ε) = 0) :
    (gaugedPreprojectiveLift k ε f hf).comp (gaugedPreprojectiveMk k ε) = f := by
  rw [gaugedPreprojectiveLift, gaugedPreprojectiveMk, Ideal.Quotient.liftₐ_comp]

@[simp]
theorem gaugedPreprojectiveLift_gaugedPreprojectiveMk
    (hf : f (gaugedPreprojectiveRelator k ε) = 0) (x : pathAlgebra k (Symmetrify Q)) :
    gaugedPreprojectiveLift k ε f hf (gaugedPreprojectiveMk k ε x) = f x :=
  AlgHom.congr_fun (gaugedPreprojectiveLift_comp_gaugedPreprojectiveMk k ε f hf) x

end Algebra

/-! ### The gauge transformation -/

section Gauge

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q]

/-- The **gauge labelling** of the doubled quiver attached to a labelling `u` of the arrows of `Q`:
it carries `u` on the arrows of `Q` and `1` on their formal reverses. Rescaling by it multiplies
both backtracks of an arrow `a` by `u a`. -/
@[expose]
def doubledLabelling (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) : ∀ ⦃x y : Symmetrify Q⦄, (x ⟶ y) → k :=
  fun _ _ b => Sum.elim (fun a => u a) (fun _ => 1) b

variable {k}

/-- The gauge labelling on an arrow of `Q` is the given label. -/
theorem doubledLabelling_of (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {i j : Q} (a : i ⟶ j) :
    doubledLabelling k u (Symmetrify.of.map a) = u a := rfl

/-- The gauge labelling on the formal reverse of an arrow of `Q` is one. -/
theorem doubledLabelling_reverse_of (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {i j : Q} (a : i ⟶ j) :
    doubledLabelling k u (Quiver.reverse (Symmetrify.of.map a)) = 1 := rfl

theorem doubledLabelling_mul (u u' : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) ⦃x y : Symmetrify Q⦄ (b : x ⟶ y) :
    doubledLabelling k (fun _ _ a => u a * u' a) b
      = doubledLabelling k u b * doubledLabelling k u' b := by
  cases b <;> simp [doubledLabelling]

variable (k) [Finite Q]

/-- Rescaling by a gauge labelling multiplies the head backtrack of `a` by the label of `a`. -/
@[simp]
theorem rescale_doubledLabelling_headBacktrackElem (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {i j : Q}
    (a : i ⟶ j) :
    rescale (doubledLabelling k u) (headBacktrackElem k a) = u a • headBacktrackElem k a := by
  rw [← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem, map_mul, rescale_ofArrow, rescale_ofArrow,
    doubledLabelling_of, doubledLabelling_reverse_of, one_smul, smul_mul_assoc,
    ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem]

/-- Rescaling by a gauge labelling multiplies the tail backtrack of `a` by the label of `a`. -/
@[simp]
theorem rescale_doubledLabelling_tailBacktrackElem (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) {i j : Q}
    (a : i ⟶ j) :
    rescale (doubledLabelling k u) (tailBacktrackElem k a) = u a • tailBacktrackElem k a := by
  rw [← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem, map_mul, rescale_ofArrow, rescale_ofArrow,
    doubledLabelling_of, doubledLabelling_reverse_of, one_smul, mul_smul_comm,
    ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem]

/-- **The gauge transformation acts on the gauged relators**: rescaling the arrows of `Q` by `u`
and fixing their formal reverses carries `ρ_ε` to `ρ_{uε}`. -/
theorem rescale_gaugedPreprojectiveRelator [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]
    (u ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k) :
    rescale (doubledLabelling k u) (gaugedPreprojectiveRelator k ε)
      = gaugedPreprojectiveRelator k (fun _ _ a => u a * ε a) := by
  simp only [gaugedPreprojectiveRelator, map_sum, map_smul, map_sub,
    rescale_doubledLabelling_headBacktrackElem, rescale_doubledLabelling_tailBacktrackElem,
    ← smul_sub, smul_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun a _ => by rw [mul_comm]

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

/-- **The gauge isomorphism is the arrow rescaling**: it sends the class of a basis path to the
class of that path scaled by the product of the units on the arrows of `Q` it traverses. -/
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

/-- At the constant gauge `1` the gauged preprojective algebra is the preprojective algebra. -/
noncomputable def preprojectiveAlgebraEquivGaugedOne :
    preprojectiveAlgebra k Q ≃ₐ[k] gaugedPreprojectiveAlgebra (Q := Q) k (fun _ _ _ => (1 : k)) :=
  Ideal.quotientEquivAlgOfEq k
    (congrArg TwoSidedIdeal.asIdeal (gaugedPreprojectiveIdeal_one (Q := Q) k).symm)

@[simp]
theorem preprojectiveAlgebraEquivGaugedOne_preprojectiveMk (x : pathAlgebra k (Symmetrify Q)) :
    preprojectiveAlgebraEquivGaugedOne k (preprojectiveMk k Q x)
      = gaugedPreprojectiveMk (Q := Q) k (fun _ _ _ => (1 : k)) x := by
  rw [preprojectiveAlgebraEquivGaugedOne, preprojectiveMk_apply, Ideal.quotientEquivAlgOfEq_mk,
    gaugedPreprojectiveMk_apply]

/-- **Every unit-valued gauge presents the preprojective algebra.** In particular a labelling of
the arrows of `Q` by signs presents `Π_k(Q)` for every choice of signs. -/
noncomputable def preprojectiveAlgebraEquivGauged (ε : ∀ ⦃i j : Q⦄, (i ⟶ j) → k)
    (u : ∀ ⦃i j : Q⦄, (i ⟶ j) → kˣ) (h : ∀ ⦃i j : Q⦄ (a : i ⟶ j), ε a = ((u a : kˣ) : k)) :
    preprojectiveAlgebra k Q ≃ₐ[k] gaugedPreprojectiveAlgebra k ε :=
  (preprojectiveAlgebraEquivGaugedOne k).trans
    (gaugedPreprojectiveAlgebraEquiv k _ ε u fun _ _ a => by rw [h a, mul_one])

/-- The isomorphism onto a unit-valued gauge, computed on the class of a basis path. -/
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

end Independence

end TauCeti
