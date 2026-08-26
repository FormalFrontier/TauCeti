/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Reorient
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Map
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Gauge

/-!
# Orientation independence of the additive preprojective algebra

The additive preprojective algebra `Π_k(Q)` is built from the *doubled* quiver of `Q`, so it ought
not to depend on which of the two directions of each edge was chosen as the arrow of `Q`. That
independence is not a formality: the defining relator

```text
ρ = ∑_a (a a* - a* a)
```

pairs each arrow with its formal reverse *with a sign*, and turning an arrow around exchanges the
two backtracks, hence negates the corresponding summand. This file proves the independence by
exhibiting the isomorphism which repairs that sign.

Fix a `Bool`-valued labelling `σ` of the arrows of `Q` and let `Reorient Q σ` be the quiver of
`TauCeti.Reorient`, obtained by turning around exactly the arrows labelled `true`. The two doubled
quivers are identified by `TauCeti.reorientSymmetrify`, hence the two doubled path algebras by
`TauCeti.reorientDoubledEquiv`. Under that identification the relator of `Reorient Q σ` becomes the
*gauged* relator `ρ_ε = ∑_a ε_a (a a* - a* a)` of `Q`, with `ε_a = -1` exactly when `σ` turns `a`
around
(`TauCeti.reorientDoubledEquiv_preprojectiveRelator`), and matching the relations one vertex at a
time (`TauCeti.reorientDoubledEquiv_localPreprojectiveRelator`). Composing with the gauge
isomorphism of `TauCeti.RepresentationTheory.Quiver.Preprojective.Gauge`, which rescales the
sign-flipped arrows by `-1` and fixes their formal reverses, gives

```text
Π_k(Reorient Q σ) ≃ₐ[k] Π_k(Q).
```

Turning around a single arrow is the case of a labelling supported on one arrow; an arbitrary `σ`
performs an arbitrary composite of such flips in one step, so the isomorphism above compares `Q`
with the explicit quiver `Reorient Q σ`. Nothing is assumed about the
characteristic of `k`: in characteristic two the sign is invisible, and the same statement is
obtained from the same proof.

## Main definitions

* `TauCeti.reorientSign` and `TauCeti.reorientSignUnit`: the labelling by `-1` on the arrows `σ`
  turns around and by `1` elsewhere, valued in `k` and in `kˣ`.
* `TauCeti.reorientDoubledEquiv`: the isomorphism of doubled path algebras induced by the
  comparison of doubled quivers.
* `TauCeti.reorientPreprojectiveAlgebraEquivGauged`: the reoriented preprojective algebra,
  presented by the signed relator of `Q`.
* `TauCeti.reorientPreprojectiveAlgebraEquiv`: **orientation independence**.

## Main results

* `TauCeti.reorientDoubledEquiv_headBacktrackElem_flip` and
  `TauCeti.reorientDoubledEquiv_tailBacktrackElem_flip`: turning an arrow around exchanges its two
  backtracks. This is the sign.
* `TauCeti.reorientDoubledEquiv_preprojectiveRelator`: the relator of a reorientation is the signed
  relator of `Q`.
* `TauCeti.reorientDoubledEquiv_localPreprojectiveRelator`: the same, vertex by vertex.
* `TauCeti.reorientPreprojectiveAlgebraEquiv_preprojectiveMk`: the isomorphism, computed on an
  arbitrary quotient representative, as the doubled-quiver identification followed by the rescaling
  by `-1` of the turned-around arrows.
* `TauCeti.reorientPreprojectiveAlgebraEquiv_preprojectiveMk_ofArrow_keep` and its three
  companions: the isomorphism, computed on each of the four kinds of generator. An arrow `σ` leaves
  alone and its formal reverse are fixed, a turned-around arrow is carried to a formal reverse, and
  the formal reverse of a turned-around arrow is carried to the negative of an arrow.

## Implementation notes

The counting step is `TauCeti.reorientDoubledEquiv_preprojectiveRelator`. A turned-around arrow
`a : j ⟶ i` of `Q` is an arrow `i ⟶ j` of `Reorient Q σ`, so its contribution to the relator of the
reorientation sits in the `(i, j)` hom set while its contribution to the signed relator of `Q` sits
in the `(j, i)` one. The two agree only after the two vertex summations are exchanged, which is
what the transposition step of the proof does; the equality does *not* hold hom set by hom set.

## References

This is the orientation-independence clause of Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks to turn around a chosen arrow by an
algebra isomorphism rescaling one of the exchanged arrows by `-1`, to check that it sends every
local relation to the corresponding relation, and to compose these maps into independence under
every explicit reorientation `Reorient Q σ`, including in characteristic two. See Crawley-Boevey,
*Quiver algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Sign

variable (k : Type w) {Q : Type u} [One k] [Neg k] [Quiver.{v + 1} Q]

/-- The sign labelling attached to a reorientation: an arrow which `σ` turns around enters the
preprojective relator with the opposite sign, and every other arrow keeps its sign. -/
def reorientSign (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) ⦃i j : Q⦄ (a : i ⟶ j) : k :=
  if σ a then -1 else 1

/-- A turned-around arrow gets the sign `-1`. -/
@[simp]
theorem reorientSign_of_true {σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool} {i j : Q} {a : i ⟶ j} (h : σ a) :
    reorientSign k σ a = -1 := by
  simp [reorientSign, h]

/-- An arrow `σ` leaves alone keeps the sign `1`. -/
@[simp]
theorem reorientSign_of_false {σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool} {i j : Q} {a : i ⟶ j}
    (h : ¬ σ a) : reorientSign k σ a = 1 := by
  simp [reorientSign, h]

end Sign

section SignUnit

variable (k : Type w) {Q : Type u} [Monoid k] [HasDistribNeg k] [Quiver.{v + 1} Q]

/-- The sign labelling, valued in the units of `k`. -/
def reorientSignUnit (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) ⦃i j : Q⦄ (a : i ⟶ j) : kˣ :=
  if σ a then -1 else 1

/-- The sign labelling takes values in `{1, -1}`, so it is its own inverse. -/
@[simp]
theorem reorientSignUnit_inv (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) ⦃i j : Q⦄ (a : i ⟶ j) :
    (reorientSignUnit k σ a)⁻¹ = reorientSignUnit k σ a := by
  rw [reorientSignUnit]
  split <;> simp

/-- The sign labelling is the unit-valued one. -/
theorem reorientSign_eq_coe_reorientSignUnit (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) ⦃i j : Q⦄
    (a : i ⟶ j) : reorientSign k σ a = ((reorientSignUnit k σ a : kˣ) : k) := by
  rw [reorientSign, reorientSignUnit]
  split <;> simp

end SignUnit

/-! ### The induced isomorphism of doubled path algebras -/

section Doubled

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v + 1} Q] [Finite Q]
  (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- **The isomorphism of doubled path algebras attached to a reorientation**: the path algebra of
`Symmetrify (Reorient Q σ)` and the path algebra of `Symmetrify Q` are identified along the
comparison of doubled quivers, which is the identity on vertices. -/
noncomputable def reorientDoubledEquiv :
    pathAlgebra k (Symmetrify (Reorient Q σ)) ≃ₐ[k] pathAlgebra k (Symmetrify Q) :=
  mapAlgEquiv k (reorientSymmetrify σ) (reorientSymmetrifyInv σ)
    (reorientSymmetrify_comp_reorientSymmetrifyInv σ)
    (reorientSymmetrifyInv_comp_reorientSymmetrify σ)

/-- The doubled path-algebra comparison maps a path of two arrows by mapping each arrow. -/
private theorem reorientDoubledEquiv_ofArrowComp {i j l : Symmetrify (Reorient Q σ)} (a : i ⟶ j)
    (b : j ⟶ l) :
    reorientDoubledEquiv k σ (ofPath ⟨i, l, a.toPath.comp b.toPath⟩) =
      ofPath ⟨(reorientSymmetrify σ).obj i, (reorientSymmetrify σ).obj l,
        ((reorientSymmetrify σ).map a).toPath.comp
          ((reorientSymmetrify σ).map b).toPath⟩ := by
  rw [reorientDoubledEquiv, mapAlgEquiv_apply, mapAlgHom_ofPath,
    Prefunctor.mapTotalPath_mk, Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath,
    Prefunctor.mapPath_toPath]

/-- Pushing an arrow of the doubled reoriented quiver along the comparison carries it to the image
arrow. Deliberately not a `simp` lemma, `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already rewriting
its left-hand side. -/
theorem reorientDoubledEquiv_ofArrow {x y : Symmetrify (Reorient Q σ)} (b : x ⟶ y) :
    reorientDoubledEquiv k σ (ofArrow b) = ofArrow ((reorientSymmetrify σ).map b) := by
  rw [reorientDoubledEquiv, mapAlgEquiv_apply, mapAlgHom_ofArrow]

/-- The arrow computation for the doubled path-algebra comparison, with its object map normalized
to the vertices of the reoriented quiver. -/
theorem reorientDoubledEquiv_ofArrow_normalized {x y : Symmetrify (Reorient Q σ)} (b : x ⟶ y) :
    reorientDoubledEquiv k σ (ofArrow b) =
      ofArrow (Quiver.homOfEq ((reorientSymmetrify σ).map b)
        (reorientSymmetrify_obj σ x :
          (reorientSymmetrify σ).obj x = (show Symmetrify Q from x))
        (reorientSymmetrify_obj σ y :
          (reorientSymmetrify σ).obj y = (show Symmetrify Q from y))) := by
  rw [reorientDoubledEquiv_ofArrow]
  exact (ofArrow_homOfEq _ _ _).symm

/-- An arrow which `σ` leaves alone keeps its head backtrack. -/
@[simp]
theorem reorientDoubledEquiv_headBacktrackElem_keep {i j : Q} (a : i ⟶ j) (ha : ¬ σ a) :
    reorientDoubledEquiv k σ (headBacktrackElem k (reorientKeep σ a ha))
      = headBacktrackElem k a := by
  rw [headBacktrackElem_def, headBacktrackElem_def, reorientDoubledEquiv_ofArrowComp,
    reorientSymmetrify_map_of_keep,
    reorientSymmetrify_map_reverse_of_keep]
  rfl

/-- An arrow which `σ` leaves alone keeps its tail backtrack. -/
@[simp]
theorem reorientDoubledEquiv_tailBacktrackElem_keep {i j : Q} (a : i ⟶ j) (ha : ¬ σ a) :
    reorientDoubledEquiv k σ (tailBacktrackElem k (reorientKeep σ a ha))
      = tailBacktrackElem k a := by
  rw [tailBacktrackElem_def, tailBacktrackElem_def, reorientDoubledEquiv_ofArrowComp,
    reorientSymmetrify_map_of_keep,
    reorientSymmetrify_map_reverse_of_keep]
  rfl

/-- Turning an arrow around exchanges its two backtracks: the head backtrack of the turned-around
arrow is the tail backtrack of the original. -/
@[simp]
theorem reorientDoubledEquiv_headBacktrackElem_flip {i j : Q} (a : j ⟶ i) (ha : σ a) :
    reorientDoubledEquiv k σ (headBacktrackElem k (reorientFlip σ a ha))
      = tailBacktrackElem k a := by
  rw [headBacktrackElem_def, tailBacktrackElem_def, reorientDoubledEquiv_ofArrowComp,
    reorientSymmetrify_map_of_flip,
    reorientSymmetrify_map_reverse_of_flip]
  rfl

/-- Turning an arrow around exchanges its two backtracks: the tail backtrack of the turned-around
arrow is the head backtrack of the original. -/
@[simp]
theorem reorientDoubledEquiv_tailBacktrackElem_flip {i j : Q} (a : j ⟶ i) (ha : σ a) :
    reorientDoubledEquiv k σ (tailBacktrackElem k (reorientFlip σ a ha))
      = headBacktrackElem k a := by
  rw [tailBacktrackElem_def, headBacktrackElem_def, reorientDoubledEquiv_ofArrowComp,
    reorientSymmetrify_map_of_flip,
    reorientSymmetrify_map_reverse_of_flip]
  rfl

/-- The comparison of doubled path algebras matches the vertex idempotents. -/
@[simp]
theorem reorientDoubledEquiv_doubledVertexIdempotent (v : Q) :
    reorientDoubledEquiv k σ (doubledVertexIdempotent k (reorientVertex σ v))
      = doubledVertexIdempotent k v := by
  rw [doubledVertexIdempotent_def, doubledVertexIdempotent_def, reorientDoubledEquiv,
    mapAlgEquiv_apply, mapAlgHom_vertexIdempotent]
  rfl

end Doubled

section DoubledSub

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Finite Q]
  (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- An arrow which `σ` leaves alone contributes its own difference of backtracks. -/
theorem reorientDoubledEquiv_sub_keep {i j : Q} (a : i ⟶ j) (ha : ¬ σ a) :
    reorientDoubledEquiv k σ (headBacktrackElem k (reorientKeep σ a ha)
        - tailBacktrackElem k (reorientKeep σ a ha))
      = reorientSign k σ a • (headBacktrackElem k a - tailBacktrackElem k a) := by
  rw [map_sub, reorientDoubledEquiv_headBacktrackElem_keep,
    reorientDoubledEquiv_tailBacktrackElem_keep, reorientSign_of_false k ha, one_smul]

/-- An arrow which `σ` turns around contributes the *negative* of its difference of backtracks:
turning the arrow around exchanges its head and tail backtracks. -/
theorem reorientDoubledEquiv_sub_flip {i j : Q} (a : j ⟶ i) (ha : σ a) :
    reorientDoubledEquiv k σ (headBacktrackElem k (reorientFlip σ a ha)
        - tailBacktrackElem k (reorientFlip σ a ha))
      = reorientSign k σ a • (headBacktrackElem k a - tailBacktrackElem k a) := by
  rw [map_sub, reorientDoubledEquiv_headBacktrackElem_flip,
    reorientDoubledEquiv_tailBacktrackElem_flip, reorientSign_of_true k ha, neg_one_smul,
    neg_sub]

end DoubledSub

/-! ### The relator of a reorientation is a signed relator -/

section Relator

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)] (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- Summing a function of the arrows of `Q` over the hom sets of a reorientation, with the
arrows `σ` turns around contributing to the transposed hom set, recovers the sum over the arrows of
`Q`: transposition is undone by exchanging the two vertex summations. -/
private theorem sum_split_reorient {M : Type*} [AddCommMonoid M] (F : ∀ ⦃i j : Q⦄, (i ⟶ j) → M) :
    (∑ i : Q, ∑ j : Q,
        ((∑ x : {a : i ⟶ j // ¬ σ a}, F x.1) + ∑ y : {a : j ⟶ i // σ a}, F y.1))
      = ∑ i : Q, ∑ j : Q, ∑ a : (i ⟶ j), F a := by
  have hswap : (∑ i : Q, ∑ j : Q, ∑ y : {a : j ⟶ i // σ a}, F y.1)
      = ∑ i : Q, ∑ j : Q, ∑ y : {a : i ⟶ j // σ a}, F y.1 :=
    Finset.sum_comm
  calc (∑ i : Q, ∑ j : Q,
          ((∑ x : {a : i ⟶ j // ¬ σ a}, F x.1) + ∑ y : {a : j ⟶ i // σ a}, F y.1))
      = (∑ i : Q, ∑ j : Q, ∑ x : {a : i ⟶ j // ¬ σ a}, F x.1)
          + ∑ i : Q, ∑ j : Q, ∑ y : {a : j ⟶ i // σ a}, F y.1 := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ i : Q, ∑ j : Q, ∑ x : {a : i ⟶ j // ¬ σ a}, F x.1)
          + ∑ i : Q, ∑ j : Q, ∑ y : {a : i ⟶ j // σ a}, F y.1 := by rw [hswap]
    _ = ∑ i : Q, ∑ j : Q,
          ((∑ x : {a : i ⟶ j // ¬ σ a}, F x.1) + ∑ y : {a : i ⟶ j // σ a}, F y.1) := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ i : Q, ∑ j : Q, ∑ a : (i ⟶ j), F a :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [add_comm]
          exact Fintype.sum_subtype_add_sum_subtype _ _

/-- **The preprojective relator of a reorientation is the signed relator of the original
quiver.** Under the identification of the two doubled path algebras, the relator
`∑_a (a a* - a* a)` of `Reorient Q σ` becomes `∑_a ε_a (a a* - a* a)`, where `ε` is `-1` exactly on
the arrows `σ` turns around. -/
theorem reorientDoubledEquiv_preprojectiveRelator :
    reorientDoubledEquiv k σ (preprojectiveRelator k (Reorient Q σ))
      = gaugedPreprojectiveRelator k (reorientSign k σ) := by
  have h1 : reorientDoubledEquiv k σ (preprojectiveRelator k (Reorient Q σ))
      = ∑ i : Q, ∑ j : Q, ∑ α : (reorientVertex σ i ⟶ reorientVertex σ j),
          reorientDoubledEquiv k σ (headBacktrackElem k α - tailBacktrackElem k α) := by
    rw [preprojectiveRelator_def]
    simp only [map_sum]
    exact sum_reorientVertex σ _
  have h2 : ∀ i j : Q, ∑ α : (reorientVertex σ i ⟶ reorientVertex σ j),
      reorientDoubledEquiv k σ (headBacktrackElem k α - tailBacktrackElem k α)
      = (∑ x : {a : i ⟶ j // ¬ σ a},
            reorientSign k σ x.1 • (headBacktrackElem k x.1 - tailBacktrackElem k x.1))
        + ∑ y : {a : j ⟶ i // σ a},
            reorientSign k σ y.1 • (headBacktrackElem k y.1 - tailBacktrackElem k y.1) := by
    intro i j
    rw [sum_reorientHom]
    exact congrArg₂ _ (Finset.sum_congr rfl fun x _ => reorientDoubledEquiv_sub_keep k σ x.1 x.2)
      (Finset.sum_congr rfl fun y _ => reorientDoubledEquiv_sub_flip k σ y.1 y.2)
  rw [h1, gaugedPreprojectiveRelator_def]
  simp only [h2]
  exact sum_split_reorient σ
    (fun _ _ a => reorientSign k σ a • (headBacktrackElem k a - tailBacktrackElem k a))

/-- **The local relations of a reorientation are the local signed relations.** The corner of the
relator at a vertex `v` of `Reorient Q σ` is carried to the corner at `v` of the signed relator, so
the identification matches the relations one vertex at a time and not merely their sum. -/
theorem reorientDoubledEquiv_localPreprojectiveRelator (v : Q) :
    reorientDoubledEquiv k σ (localPreprojectiveRelator k (reorientVertex σ v))
      = doubledVertexIdempotent k v * gaugedPreprojectiveRelator k (reorientSign k σ)
          * doubledVertexIdempotent k v := by
  rw [← preprojectiveRelator_vertexCorner_eq_localPreprojectiveRelator, map_mul, map_mul,
    reorientDoubledEquiv_doubledVertexIdempotent, reorientDoubledEquiv_preprojectiveRelator]

end Relator

/-! ### Orientation independence -/

section Independence

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)] (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- The preprojective algebra of a reorientation, presented by the signed relator of the original
quiver. -/
noncomputable def reorientPreprojectiveAlgebraEquivGauged :
    preprojectiveAlgebra k (Reorient Q σ) ≃ₐ[k]
      gaugedPreprojectiveAlgebra k (reorientSign k σ) :=
  AlgEquiv.ofAlgHom
    (preprojectiveLift ((gaugedPreprojectiveMk k (reorientSign k σ)).comp
        (reorientDoubledEquiv k σ).toAlgHom)
      (by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
          reorientDoubledEquiv_preprojectiveRelator,
          gaugedPreprojectiveMk_gaugedPreprojectiveRelator]))
    (gaugedPreprojectiveLift k (reorientSign k σ)
      ((preprojectiveMk k (Reorient Q σ)).comp (reorientDoubledEquiv k σ).symm.toAlgHom)
      (by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
          ← reorientDoubledEquiv_preprojectiveRelator, AlgEquiv.symm_apply_apply,
          preprojectiveMk_preprojectiveRelator]))
    (AlgHom.ext fun y => by
      obtain ⟨x, rfl⟩ := gaugedPreprojectiveMk_surjective k (reorientSign k σ) y
      simp)
    (AlgHom.ext fun y => by
      obtain ⟨x, rfl⟩ := preprojectiveMk_surjective k (Reorient Q σ) y
      simp)

/-- **Orientation independence of the additive preprojective algebra.** Turning around any set of
arrows of `Q` gives an isomorphic preprojective algebra: the doubled quivers are identified, and
the resulting change of sign in the relator is undone by rescaling the turned-around arrows by
`-1`. No hypothesis on the characteristic is needed. -/
noncomputable def reorientPreprojectiveAlgebraEquiv :
    preprojectiveAlgebra k (Reorient Q σ) ≃ₐ[k] preprojectiveAlgebra k Q :=
  (reorientPreprojectiveAlgebraEquivGauged k σ).trans
    (preprojectiveAlgebraEquivGauged k (reorientSign k σ) (reorientSignUnit k σ)
      (reorientSign_eq_coe_reorientSignUnit k σ)).symm

/-- The presentation of the reoriented algebra by the signed relator, computed on an arbitrary
quotient representative. -/
@[simp]
theorem reorientPreprojectiveAlgebraEquivGauged_preprojectiveMk
    (x : pathAlgebra k (Symmetrify (Reorient Q σ))) :
    reorientPreprojectiveAlgebraEquivGauged k σ (preprojectiveMk k (Reorient Q σ) x)
      = gaugedPreprojectiveMk k (reorientSign k σ) (reorientDoubledEquiv k σ x) := by
  rw [reorientPreprojectiveAlgebraEquivGauged, ← AlgEquiv.coe_toAlgHom,
    AlgEquiv.toAlgHom_ofAlgHom, preprojectiveLift_preprojectiveMk, AlgHom.comp_apply]
  rfl

/-- **The orientation-independence isomorphism, computed on generators**: it identifies the two
doubled path algebras and then rescales, by `-1`, exactly the arrows `σ` turns around, leaving
every formal reverse alone. This is the explicit map the roadmap asks for, in the form which makes
the sign visible. -/
@[simp]
theorem reorientPreprojectiveAlgebraEquiv_preprojectiveMk
    (x : pathAlgebra k (Symmetrify (Reorient Q σ))) :
    reorientPreprojectiveAlgebraEquiv k σ (preprojectiveMk k (Reorient Q σ) x)
      = preprojectiveMk k Q (rescale (doubledLabelling k fun _ _ a => reorientSign k σ a)
          (reorientDoubledEquiv k σ x)) := by
  rw [reorientPreprojectiveAlgebraEquiv, AlgEquiv.trans_apply,
    reorientPreprojectiveAlgebraEquivGauged_preprojectiveMk,
    preprojectiveAlgebraEquivGauged_symm_gaugedPreprojectiveMk]
  simp only [reorientSignUnit_inv, ← reorientSign_eq_coe_reorientSignUnit]

/-! The four equations below compute the isomorphism on the generators of the reoriented algebra,
which are the arrows of `Symmetrify (Reorient Q σ)`. They are deliberately not `simp` lemmas,
`TauCeti.PathAlgebra.ofArrow_eq_ofPath` and `Quiver.Symmetrify.of_map` already rewriting their
left-hand sides. Each proof computes the image through
`TauCeti.reorientDoubledEquiv_ofArrow_normalized`, so the object map is rewritten explicitly rather
than discharged by definitional equality. -/

/-- **The isomorphism fixes an arrow which `σ` leaves alone.** -/
theorem reorientPreprojectiveAlgebraEquiv_preprojectiveMk_ofArrow_keep {i j : Q} (a : i ⟶ j)
    (ha : ¬ σ a) :
    reorientPreprojectiveAlgebraEquiv k σ
        (preprojectiveMk k (Reorient Q σ) (ofArrow (Symmetrify.of.map (reorientKeep σ a ha))))
      = preprojectiveMk k Q (ofArrow (Symmetrify.of.map a)) := by
  have h : reorientDoubledEquiv k σ (ofArrow (Symmetrify.of.map (reorientKeep σ a ha)))
      = ofArrow (Symmetrify.of.map a) := by
    rw [reorientDoubledEquiv_ofArrow_normalized]
    rw [reorientSymmetrify_map_of_keep]
    exact ofArrow_homOfEq _ _ _
  rw [reorientPreprojectiveAlgebraEquiv_preprojectiveMk, h, rescale_ofArrow, doubledLabelling_of,
    reorientSign_of_false k ha, one_smul]

/-- **The isomorphism fixes the formal reverse of an arrow which `σ` leaves alone.** -/
theorem reorientPreprojectiveAlgebraEquiv_preprojectiveMk_ofArrow_reverse_keep {i j : Q}
    (a : i ⟶ j) (ha : ¬ σ a) :
    reorientPreprojectiveAlgebraEquiv k σ (preprojectiveMk k (Reorient Q σ)
        (ofArrow (Quiver.reverse (Symmetrify.of.map (reorientKeep σ a ha)))))
      = preprojectiveMk k Q (ofArrow (Quiver.reverse (Symmetrify.of.map a))) := by
  have h : reorientDoubledEquiv k σ
        (ofArrow (Quiver.reverse (Symmetrify.of.map (reorientKeep σ a ha))))
      = ofArrow (Quiver.reverse (Symmetrify.of.map a)) := by
    rw [reorientDoubledEquiv_ofArrow_normalized]
    rw [reorientSymmetrify_map_reverse_of_keep]
    exact ofArrow_homOfEq _ _ _
  rw [reorientPreprojectiveAlgebraEquiv_preprojectiveMk, h, rescale_ofArrow,
    doubledLabelling_reverse_of, one_smul]

/-- **The isomorphism exchanges a turned-around arrow with a formal reverse**, without a sign: the
arrow of `Reorient Q σ` carried by a turned-around arrow `a` of `Q` goes to the formal reverse
of `a`. -/
theorem reorientPreprojectiveAlgebraEquiv_preprojectiveMk_ofArrow_flip {i j : Q} (a : j ⟶ i)
    (ha : σ a) :
    reorientPreprojectiveAlgebraEquiv k σ
        (preprojectiveMk k (Reorient Q σ) (ofArrow (Symmetrify.of.map (reorientFlip σ a ha))))
      = preprojectiveMk k Q (ofArrow (Quiver.reverse (Symmetrify.of.map a))) := by
  have h : reorientDoubledEquiv k σ (ofArrow (Symmetrify.of.map (reorientFlip σ a ha)))
      = ofArrow (Quiver.reverse (Symmetrify.of.map a)) := by
    rw [reorientDoubledEquiv_ofArrow_normalized]
    rw [reorientSymmetrify_map_of_flip]
    exact ofArrow_homOfEq _ _ _
  rw [reorientPreprojectiveAlgebraEquiv_preprojectiveMk, h, rescale_ofArrow,
    doubledLabelling_reverse_of, one_smul]

/-- **The isomorphism negates the formal reverse of a turned-around arrow.** This is the one
generator carrying the sign which repairs the change of orientation; every other generator above is
carried to a generator on the nose. -/
theorem reorientPreprojectiveAlgebraEquiv_preprojectiveMk_ofArrow_reverse_flip {i j : Q}
    (a : j ⟶ i) (ha : σ a) :
    reorientPreprojectiveAlgebraEquiv k σ (preprojectiveMk k (Reorient Q σ)
        (ofArrow (Quiver.reverse (Symmetrify.of.map (reorientFlip σ a ha)))))
      = -preprojectiveMk k Q (ofArrow (Symmetrify.of.map a)) := by
  have h : reorientDoubledEquiv k σ
        (ofArrow (Quiver.reverse (Symmetrify.of.map (reorientFlip σ a ha))))
      = ofArrow (Symmetrify.of.map a) := by
    rw [reorientDoubledEquiv_ofArrow_normalized]
    rw [reorientSymmetrify_map_reverse_of_flip]
    exact ofArrow_homOfEq _ _ _
  rw [reorientPreprojectiveAlgebraEquiv_preprojectiveMk, h, rescale_ofArrow, doubledLabelling_of,
    reorientSign_of_true k ha, neg_one_smul, map_neg]

end Independence

end TauCeti
