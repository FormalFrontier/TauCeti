/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.BlockRepresentation
public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RingTheory.Semisimple.Wedderburn.Blocks

/-!
# The Wedderburn blocks of `k[G]` classify its irreducible representations

A Wedderburn presentation `e : k[G] ≃ₐ[k] Π i, Matₙᵢ(k)` of a finite group algebra over an
algebraically closed field carries an irreducible representation on each block, and distinct blocks
carry inequivalent ones (`TauCeti/RepresentationTheory/CharacterTable/BlockRepresentation.lean`).
This file supplies the missing half, that the list is **complete**: every finite-dimensional
irreducible representation of `G` over `k` is equivalent to a block representation. The block index
is therefore a faithful index of the irreducible representations up to equivalence, and everything
read off a presentation — first of all the multiset of degrees `nᵢ` — is an invariant of `G`.

Completeness is not a new argument: a family of pairwise inequivalent irreducibles indexed by as
many indices as `G` has conjugacy classes already exhausts the irreducibles
(`TauCeti.ClassFunction.exists_nonempty_equiv`), and a presentation has exactly that many blocks
(`TauCeti.card_eq_card_conjClasses_of_algEquiv_pi_matrix`). What was missing was the assembly, and
the invariance statements it unlocks.

## Main results

* `TauCeti.exists_nonempty_equiv_blockRepresentation`: **every irreducible representation of `G` is
  equivalent to a block representation**, so the blocks are a complete irredundant list.
* `TauCeti.exists_degree_eq_finrank`: the dimension of an irreducible representation is the degree
  of the block it matches, and `TauCeti.exists_isIrreducible_finrank_eq` is the converse, that each
  degree is realized.
* `TauCeti.exists_equiv_blockRepresentation`: **two Wedderburn presentations of `k[G]` differ by a
  permutation of the blocks**, matching degrees and block representations.
* `TauCeti.natCard_degree_fiber_eq`: **the multiset of degrees does not depend on the
  presentation**, in the form that each degree occurs equally often in the two.
* `TauCeti.nonempty_equiv_index_simpleSubmoduleClasses`: the block index is in bijection with the
  isomorphism classes of simple `k[G]`-modules.

## Implementation notes

The degree multiset is compared through the cardinalities of the fibres of the degree function,
`Nat.card {i // d i = n}`, rather than through `Multiset.map d Finset.univ.val`: the index types
carry `Finite` rather than `Fintype`, and the fibre form needs no decidability or enumeration and
says the same thing.

The `[∀ i, NeZero (d i)]` hypotheses are essential throughout, exactly as in
`IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`, which produces them: a block of size
zero is the trivial ring, carries no representation, and could be inserted into any presentation
without changing the product, so without positivity neither the block count nor the degree multiset
would be an invariant.

Only the *representation*-level dictionary is new here. The module-level one, that the blocks of a
presentation of any semisimple ring are in bijection with the isomorphism classes of its simple
modules, is `TauCeti.nonempty_equiv_simpleSubmoduleClasses_of_ringEquiv_pi`; its group-algebra case
is recorded below as a corollary, since the two dictionaries are what
`TauCeti/RepresentationTheory/CharacterTable/Wedderburn.lean` names as the statements needed before
its block count may be called the count of irreducible representations.

## References

This implements the block ⇆ irreducible-representation dictionary of Layer 2.5, and the invariance
of the Wedderburn data behind the count of Layer 2, of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
See J.-P. Serre, *Linear Representations of Finite Groups*, Section 6.4, or C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, Section 26.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u v w w'

section Complete

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type w} [Finite ι] {d : ι → ℕ} [∀ i, NeZero (d i)]
  (e : k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)

omit [IsAlgClosed k] [Invertible (Nat.card G : k)] in
include e in
/-- The `Nat.card` spelling of `TauCeti.card_eq_card_conjClasses_of_algEquiv_pi_matrix`, which is
the shape `TauCeti.ClassFunction.exists_nonempty_equiv` asks for. -/
private theorem natCard_eq_card_conjClasses : Nat.card ι = Nat.card (ConjClasses G) := by
  let _ := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card]
  exact card_eq_card_conjClasses_of_algEquiv_pi_matrix e

/-- **The Wedderburn blocks are a complete list of the irreducible representations.** Every
finite-dimensional irreducible representation of `G` over an algebraically closed field whose
characteristic does not divide `|G|` is equivalent to the representation carried by one of the
blocks of any Wedderburn presentation of `k[G]`.

Together with `TauCeti.isIrreducible_blockRepresentation` and
`TauCeti.isEmpty_equiv_blockRepresentation` this makes the block index a faithful index of the
irreducible representations up to equivalence. -/
theorem exists_nonempty_equiv_blockRepresentation {W : Type w'} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (σ : Representation k G W) [σ.IsIrreducible] :
    ∃ i, Nonempty (σ.Equiv (blockRepresentation e i)) := by
  have : ∀ i, (blockRepresentation e i).IsIrreducible := fun i =>
    isIrreducible_blockRepresentation e i
  exact ClassFunction.exists_nonempty_equiv (blockRepresentation e)
    (fun _ _ hij => isEmpty_equiv_blockRepresentation e hij) (natCard_eq_card_conjClasses e) σ

include e in
/-- **The dimension of an irreducible representation is one of the Wedderburn degrees.** -/
theorem exists_degree_eq_finrank {W : Type w'} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (σ : Representation k G W) [σ.IsIrreducible] :
    ∃ i, d i = Module.finrank k W := by
  obtain ⟨i, ⟨φ⟩⟩ := exists_nonempty_equiv_blockRepresentation e σ
  refine ⟨i, ?_⟩
  rw [φ.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]

omit [Finite G] [IsAlgClosed k] [Invertible (Nat.card G : k)] [Finite ι] in
include e in
/-- **Every Wedderburn degree is the dimension of an irreducible representation**, namely of the
representation carried by that block. This is the converse of
`TauCeti.exists_degree_eq_finrank`. -/
theorem exists_isIrreducible_finrank_eq (i : ι) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (σ : Representation k G W),
      σ.IsIrreducible ∧ Module.finrank k W = d i :=
  ⟨Fin (d i) → k, inferInstance, inferInstance, blockRepresentation e i,
    isIrreducible_blockRepresentation e i, Module.finrank_fin_fun k⟩

omit [IsAlgClosed k] in
include e in
/-- **The block index is in bijection with the isomorphism classes of simple `k[G]`-modules.** This
is the group-algebra case of `TauCeti.nonempty_equiv_simpleSubmoduleClasses_of_ringEquiv_pi`, the
module-level companion of `TauCeti.exists_nonempty_equiv_blockRepresentation`. -/
theorem nonempty_equiv_index_simpleSubmoduleClasses :
    Nonempty (ι ≃ SimpleSubmoduleClasses k[G] k[G]) := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  have : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  exact nonempty_equiv_simpleSubmoduleClasses_of_ringEquiv_pi e.toRingEquiv

end Complete

section Uniqueness

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]
  {ι : Type w} [Finite ι] {d : ι → ℕ} [∀ i, NeZero (d i)]
  {ι' : Type w'} [Finite ι'] {d' : ι' → ℕ} [∀ j, NeZero (d' j)]
  (e : k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)
  (e' : k[G] ≃ₐ[k] Π j, Matrix (Fin (d' j)) (Fin (d' j)) k)

/-- **Two Wedderburn presentations of `k[G]` differ by a permutation of their blocks.** The
permutation matches the degrees and the representations the blocks carry, so every invariant read
off a presentation is an invariant of `G`.

The bijection is not canonical — nothing orders the blocks — so it is produced existentially. -/
theorem exists_equiv_blockRepresentation :
    ∃ σ : ι ≃ ι', ∀ i, d i = d' (σ i) ∧
      Nonempty ((blockRepresentation e i).Equiv (blockRepresentation e' (σ i))) := by
  have : ∀ i, (blockRepresentation e i).IsIrreducible := fun i =>
    isIrreducible_blockRepresentation e i
  -- Match each block of `e` with the block of `e'` carrying an equivalent representation.
  choose f hf using fun i =>
    exists_nonempty_equiv_blockRepresentation e' (blockRepresentation e i)
  -- Distinct blocks of `e` carry inequivalent representations, so the matching is injective.
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hφ := hf i
    rw [hij] at hφ
    obtain ⟨φ⟩ := hφ
    obtain ⟨ψ⟩ := hf j
    exact (isEmpty_equiv_blockRepresentation e hne).elim (φ.trans ψ.symm)
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite ι'
  -- Both index sets have as many members as `G` has conjugacy classes, so it is a bijection.
  have hcard : Fintype.card ι = Fintype.card ι' := by
    rw [card_eq_card_conjClasses_of_algEquiv_pi_matrix e,
      card_eq_card_conjClasses_of_algEquiv_pi_matrix e']
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  refine ⟨Equiv.ofBijective f hbij, fun i => ⟨?_, hf i⟩⟩
  obtain ⟨φ⟩ := hf i
  have hrank := φ.toLinearEquiv.finrank_eq
  rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at hrank

include e e' in
/-- **The block count does not depend on the presentation.** -/
theorem natCard_index_eq : Nat.card ι = Nat.card ι' := by
  obtain ⟨σ, -⟩ := exists_equiv_blockRepresentation e e'
  exact Nat.card_congr σ

include e e' in
/-- **The multiset of Wedderburn degrees does not depend on the presentation**: every degree occurs
equally often in the two. Together with `TauCeti.exists_degree_eq_finrank` and
`TauCeti.exists_isIrreducible_finrank_eq` this says that the degrees list the dimensions of the
irreducible representations of `G`, one dimension for each equivalence class. -/
theorem natCard_degree_fiber_eq (n : ℕ) :
    Nat.card {i // d i = n} = Nat.card {j // d' j = n} := by
  obtain ⟨σ, hσ⟩ := exists_equiv_blockRepresentation e e'
  exact Nat.card_congr (Equiv.subtypeEquiv σ fun i => by rw [(hσ i).1])

end Uniqueness

end TauCeti
