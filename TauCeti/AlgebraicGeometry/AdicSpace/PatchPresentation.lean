/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum
import TauCeti.Topology.Spectral.PatchCriterion

/-!
# The patch presentation of the valuation spectrum

Following Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), proof of Proposition 4.7: the map
sending a point of `Spv A` to the boolean table of its relation embeds `Spv A` into the
compact product `(A × A) → Bool`, with closed image; the basic opens of `Spv A` are clopen
for the induced compact topology. This is the presentation that the patch criterion for
spectral spaces consumes to prove `Spv A` spectral.

## Main definitions

* `TauCeti.ValuationSpectrum.toPatch` : The relation table `Spv A → (A × A) → Bool`.
* `TauCeti.ValuationSpectrum.patchTopology` : The compact witness topology on `Spv A`
  induced from the product.

## Main results

* `TauCeti.ValuationSpectrum.isClosedEmbedding_toPatch` : The table is a closed embedding
  of the witness topology into the product.
* `TauCeti.ValuationSpectrum.compactSpace_patchTopology` : The witness topology is compact.
* `TauCeti.ValuationSpectrum.isClopen_patchTopology_basicOpen` : Basic opens are clopen for
  the witness topology.
-/

public section

namespace TauCeti.ValuationSpectrum

open TopologicalSpace Set Topology

variable {A : Type*} [CommRing A]

open scoped Classical in
/-- The relation table of a point of `Spv A`: the boolean function recording, for each pair
`(f, s)`, whether `v(f) ≤ v(s)`. -/
noncomputable def toPatch (v : Spv A) : A × A → Bool :=
  fun p ↦ decide (v.toValuativeRel.vle p.1 p.2)

open scoped Classical in
/-- A coordinate of the relation table is `true` exactly when the relation holds there. -/
@[simp]
lemma toPatch_eq_true_iff (v : Spv A) (p : A × A) :
    toPatch v p = true ↔ v.toValuativeRel.vle p.1 p.2 := by
  simp [toPatch]

/-- The relation table determines the point: `toPatch` is injective. -/
lemma toPatch_injective : Function.Injective (toPatch (A := A)) := fun _ _ h ↦
  ext' fun x y ↦ decide_eq_decide.mp (congrFun h (x, y))

/-- The compact witness topology on `Spv A`: the topology induced from the product
`(A × A) → Bool` of discrete factors along the relation table. -/
@[instance_reducible]
noncomputable def patchTopology (A : Type*) [CommRing A] : TopologicalSpace (Spv A) :=
  TopologicalSpace.induced toPatch inferInstance

omit [CommRing A] in
/-- Coordinate conditions on tables are closed. -/
private lemma isClosed_coord (p : A × A) (b : Bool) :
    IsClosed {g : A × A → Bool | g p = b} :=
  ((isClopen_discrete {b}).preimage (continuous_apply p)).isClosed

open scoped Classical in
/-- The range of the relation table is exactly the set of tables satisfying the
`ValuativeRel` axioms pointwise. -/
lemma range_toPatch_eq :
    Set.range (toPatch (A := A)) =
      {g : A × A → Bool |
        (∀ x y : A, g (x, y) = true ∨ g (y, x) = true) ∧
        (∀ x y z : A, g (x, y) = true → g (y, z) = true → g (x, z) = true) ∧
        (∀ x y z : A, g (x, z) = true → g (y, z) = true → g (x + y, z) = true) ∧
        (∀ x y z : A, g (x, y) = true → g (x * z, y * z) = true) ∧
        (∀ x y z : A, g (z, 0) = false → g (x * z, y * z) = true → g (x, y) = true) ∧
        (g (1, 0) = false) ∧
        (∀ x y : A, g (x * y, y * x) = true)} := by
  ext g
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨fun x y ↦ ?_, fun x y z hxy hyz ↦ ?_, fun x y z hxz hyz ↦ ?_,
      fun x y z hxy ↦ ?_, fun x y z hz hxz ↦ ?_, ?_, fun x y ↦ ?_⟩ <;>
      simp only [toPatch, decide_eq_true_iff, decide_eq_false_iff_not] at *
    · exact v.toValuativeRel.vle_total x y
    · exact v.toValuativeRel.vle_trans hxy hyz
    · exact v.toValuativeRel.vle_add hxz hyz
    · exact v.toValuativeRel.mul_vle_mul_left hxy z
    · exact v.toValuativeRel.vle_mul_cancel hz hxz
    · exact v.toValuativeRel.not_vle_one_zero
    · exact v.toValuativeRel.vle_mul_comm
  · rintro ⟨htot, htrans, hadd, hmul, hcancel, hone, hcomm⟩
    refine ⟨⟨{ vle := fun x y ↦ g (x, y) = true
               vle_total := htot
               vle_trans := fun h1 h2 ↦ htrans _ _ _ h1 h2
               vle_add := fun h1 h2 ↦ hadd _ _ _ h1 h2
               mul_vle_mul_left := fun h z ↦ hmul _ _ z h
               vle_mul_cancel := fun h0 h ↦ hcancel _ _ _ (by simpa using h0) h
               not_vle_one_zero := by simp [hone]
               vle_mul_comm := hcomm _ _ }⟩, ?_⟩
    funext p
    cases hgp : g p <;> simp only [toPatch, decide_eq_true_eq, decide_eq_false_iff_not]
    · exact fun h ↦ by
        have h' : g (p.1, p.2) = true := h
        simp [hgp] at h'
    · exact hgp

omit [CommRing A] in
/-- Implication clauses with a coordinate antecedent are closed when the consequent set is. -/
private lemma isClosed_setOf_coord_imp {P : (A × A → Bool) → Prop} (p : A × A) (b : Bool)
    (hP : IsClosed {g : A × A → Bool | P g}) :
    IsClosed {g : A × A → Bool | g p = b → P g} := by
  have h : {g : A × A → Bool | g p = b → P g} = {g | g p = !b} ∪ {g | P g} := by
    ext g
    cases hgp : g p <;> cases b <;> simp [hgp]
  rw [h]
  exact (isClosed_coord p (!b)).union hP

/-- The range of the relation table is closed: each axiom of `ValuativeRel` is a closed
condition on tables. -/
lemma isClosed_range_toPatch : IsClosed (Set.range (toPatch (A := A))) := by
  rw [range_toPatch_eq]
  simp only [Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_
    (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))))
  · simp only [Set.ofPred_forall]
    refine isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
    rw [Set.ofPred_or]
    exact (isClosed_coord (x, y) true).union (isClosed_coord (y, x) true)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun z ↦
      isClosed_setOf_coord_imp (x, y) true
        (isClosed_setOf_coord_imp (y, z) true (isClosed_coord (x, z) true))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun z ↦
      isClosed_setOf_coord_imp (x, z) true
        (isClosed_setOf_coord_imp (y, z) true (isClosed_coord (x + y, z) true))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun z ↦
      isClosed_setOf_coord_imp (x, y) true (isClosed_coord (x * z, y * z) true)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun z ↦
      isClosed_setOf_coord_imp (z, 0) false
        (isClosed_setOf_coord_imp (x * z, y * z) true (isClosed_coord (x, y) true))
  · exact isClosed_coord (1, 0) false
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_coord (x * y, y * x) true

/-- The relation table is a closed embedding of the patch topology into the product. -/
lemma isClosedEmbedding_toPatch :
    @Topology.IsClosedEmbedding (Spv A) (A × A → Bool) (patchTopology A) _ toPatch :=
  @Topology.IsClosedEmbedding.mk (Spv A) (A × A → Bool) (patchTopology A) _ toPatch
    toPatch_injective.isEmbedding_induced isClosed_range_toPatch

/-- The patch topology is compact: the table embeds `Spv A` as a closed subspace of a
compact product. -/
lemma compactSpace_patchTopology : @CompactSpace (Spv A) (patchTopology A) :=
  @Topology.IsClosedEmbedding.compactSpace (Spv A) (A × A → Bool) (patchTopology A) _ _
    toPatch isClosedEmbedding_toPatch

open scoped Classical in
/-- A basic open is the table preimage of a two-coordinate condition. -/
lemma basicOpen_eq_toPatch_preimage (f s : A) :
    basicOpen f s
      = toPatch ⁻¹' {g : A × A → Bool | g (f, s) = true ∧ g (s, 0) = false} := by
  ext v
  simp [mem_basicOpen_iff, toPatch]

/-- Basic opens are clopen for the patch topology. -/
lemma isClopen_patchTopology_basicOpen (f s : A) :
    @IsClopen (Spv A) (patchTopology A) (basicOpen f s) := by
  rw [basicOpen_eq_toPatch_preimage]
  have hcl : IsClopen {g : A × A → Bool | g (f, s) = true ∧ g (s, 0) = false} := by
    refine IsClopen.inter ?_ ?_
    · exact (isClopen_discrete {true}).preimage (continuous_apply (f, s))
    · exact (isClopen_discrete {false}).preimage (continuous_apply (s, 0))
  exact ⟨@IsClosed.preimage (Spv A) _ (patchTopology A) _ toPatch continuous_induced_dom _
      hcl.isClosed,
    @IsOpen.preimage (Spv A) _ (patchTopology A) _ toPatch continuous_induced_dom _
      hcl.isOpen⟩

/-- **Spectrality of the valuation spectrum** (Wedhorn, *Adic Spaces*, Theorem 4.9, via
Propositions 4.7 and 3.31): the spectral topology of `Spv A` is generated by the basic
opens, which are clopen for the compact patch topology, and is T0 — so `Spv A` is
spectral by the patch criterion. -/
instance : SpectralSpace (Spv A) :=
  spectralSpace_of_isClopen_generateFrom instTopologicalSpace_eq_generateFrom
    compactSpace_patchTopology
    (fun _ hU ↦ by
      obtain ⟨f, s, rfl⟩ := hU
      exact isClopen_patchTopology_basicOpen f s)

end TauCeti.ValuationSpectrum
