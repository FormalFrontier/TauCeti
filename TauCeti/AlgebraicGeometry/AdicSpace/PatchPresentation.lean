/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum
public import TauCeti.Topology.Spectral.ProConstructible
import TauCeti.Topology.Spectral.PatchCriterion

/-!
# The patch presentation of the valuation spectrum

Following Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), proof of Proposition 4.7: the map
sending a point of `Spv A` to the boolean table of its relation embeds `Spv A` into the
compact product `(A × A) → Bool`, with closed image; the basic opens of `Spv A` are clopen
for the induced compact topology. This is the presentation that the patch criterion for
spectral spaces consumes to prove `Spv A` spectral.

It also settles quasi-compactness of the generating family of `Spv A`, by instantiating the patch
criterion's `isCompact_of_isClosed_generateFrom` at `patchTopology A`: the mechanism lives once,
in `TauCeti/Topology/Spectral/PatchCriterion.lean`, and is specialised here. That is the part of
Wedhorn's Theorem 4.9 which says the family consists of quasi-compact opens, as opposed to merely
generating the topology. It says nothing about Lemma 7.5(1), whose family lives in `Spv (A, I)`:
these statements do not transfer to the traces along the inclusion. That side is proved separately
in `SpvOfIdeal/Spectral.lean`, by the same criterion applied to the witness topology coinduced
along `r_I`. Nor is the *basis* property proved here — only quasi-compactness of the individual
members.

The quasi-compactness of the basic opens also yields, by stability of pro-constructibility
under intersections, that the sub-unit locus `{v | ∀ a ∈ S, v(a) ≤ 1}` is pro-constructible in
`Spv A`. Like everything above this is a statement about `Spv A` itself, subject to the same
non-transfer caveat: the `Spv (A, IA)` analogue that Theorem 7.35 consumes is proved on that
side (`isProConstructible_val_preimage_setOfPred_forall_vle_one`), not by restriction.

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
* `TauCeti.ValuationSpectrum.isCompact_of_isClosed_patchTopology` : a patch-closed subset is
  quasi-compact, with `TauCeti.ValuationSpectrum.isCompact_basicOpen` and
  `TauCeti.ValuationSpectrum.isCompact_basicOpenFinset` its two instances.
* `TauCeti.ValuationSpectrum.isProConstructible_setOfPred_forall_vle_one` : the locus
  `v ≤ 1` on a set of ring elements is pro-constructible **in `Spv A`** — the `Spv A`-level
  shape of the sub-unit condition of `Spa (A, A⁺)`; the `Spv (A, IA)` statement that Wedhorn's
  Theorem 7.35 consumes is `isProConstructible_val_preimage_setOfPred_forall_vle_one`
  (`SpvOfIdeal/Spectral.lean`), proved there since the inclusion is not spectral.

## Provenance

The corresponding development in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, project `projects/AdicSpaces/`, reaches spectrality
through `isSpectralSpace_of_qcKolmogorov_oc_basis` and `Spv.isSpectralSpace`, which return a
`CompactSpace ∧ T0Space ∧ QuasiSober` conjunction; it has no counterpart to an isolated
quasi-compactness statement about a single rational subset. Nothing was copied.
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

/-- `Spv(A)(T/s)` is clopen for the patch topology: a finite intersection of patch-clopen basic
opens. This is the input the patch criterion consumes. -/
lemma isClopen_patchTopology_basicOpenFinset (T : Finset A) (s : A) :
    @IsClopen (Spv A) (patchTopology A) (basicOpenFinset T s) := by
  rw [basicOpenFinset_eq_biInter]
  exact @Set.Finite.isClopen_biInter _ (patchTopology A) _ _ (T.finite_toSet.insert s) _
    fun t _ ↦ isClopen_patchTopology_basicOpen t s

/-! ### Quasi-compactness of the rational subsets -/

/-- The basic opens are patch-clopen — the hypothesis the patch criterion's quasi-compactness
lemmas take, packaged once for the two instantiations below. -/
private lemma isClopen_patchTopology_of_mem_basicOpens :
    ∀ U ∈ {U : Set (Spv A) | ∃ f s : A, U = basicOpen f s},
      @IsClopen (Spv A) (patchTopology A) U := by
  rintro _ ⟨f, s, rfl⟩
  exact isClopen_patchTopology_basicOpen f s

/-- Any patch-closed subset of `Spv A` is quasi-compact — the patch criterion's
`isCompact_of_isClosed_generateFrom`, instantiated at the patch presentation. -/
lemma isCompact_of_isClosed_patchTopology {U : Set (Spv A)}
    (hU : @IsClosed (Spv A) (patchTopology A) U) : IsCompact U :=
  isCompact_of_isClosed_generateFrom (t' := patchTopology A) instTopologicalSpace_eq_generateFrom
    compactSpace_patchTopology isClopen_patchTopology_of_mem_basicOpens hU

/-- A basic open of `Spv A` is quasi-compact. -/
lemma isCompact_basicOpen (f s : A) : IsCompact (basicOpen f s) :=
  isCompact_of_isClosed_patchTopology
    (@IsClopen.isClosed (Spv A) (patchTopology A) _ (isClopen_patchTopology_basicOpen f s))

/-- `Spv(A)(T/s)` is quasi-compact: a finite intersection of patch-clopen basic opens is
patch-clopen. -/
lemma isCompact_basicOpenFinset (T : Finset A) (s : A) : IsCompact (basicOpenFinset T s) :=
  isCompact_of_isClosed_patchTopology
    (@IsClopen.isClosed (Spv A) (patchTopology A) _ (isClopen_patchTopology_basicOpenFinset T s))

/-! ### The sub-unit locus is pro-constructible -/

/-- **The locus `v ≤ 1` on a set of ring elements is pro-constructible in `Spv A`.**

At `S = A⁺` this is the `Spv A`-level shape of the sub-unit condition cutting `Spa (A, A⁺)`
out of `Cont A` (`spa_def`). Wedhorn's Theorem 7.35 consumes the corresponding statement in
`Spv (A, IA)`, which does not follow from this one by restriction — the inclusion
`Spv(A,I) → Spv A` is not spectral — and is instead proved from the rational family as
`isProConstructible_val_preimage_setOfPred_forall_vle_one` in `SpvOfIdeal/Spectral.lean`. -/
theorem isProConstructible_setOfPred_forall_vle_one (S : Set A) :
    IsProConstructible {v : Spv A | ∀ a ∈ S, v.toValuativeRel.vle a 1} := by
  have h : {v : Spv A | ∀ a ∈ S, v.toValuativeRel.vle a 1} = ⋂ a ∈ S, basicOpen a 1 := by
    ext v
    simp
  rw [h]
  exact IsProConstructible.biInter fun a _ ↦
    IsCompact.isProConstructible (isCompact_basicOpen a 1) (isOpen_basicOpen a 1)

end TauCeti.ValuationSpectrum
