/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Maschke
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.CharacterTable.SimpleModuleCount
public import TauCeti.RepresentationTheory.Simple.FDRepClasses
public import TauCeti.RepresentationTheory.Symmetric.Partitions
public import TauCeti.RepresentationTheory.Symmetric.Specht.Distinctness

/-!
# The Specht modules classify the irreducible rational representations of `Sₙ`

The Specht modules `S^μ` are irreducible over `ℚ`
(`TauCeti.isIrreducible_spechtModule`) and pairwise non-isomorphic
(`TauCeti.spechtModule_iso_iff`). This file proves that there are no others: `μ ↦ S^μ` is a
**bijection** from the partitions of `n` to the isomorphism classes of simple
`ℚ[Sₙ]`-modules, so every irreducible rational representation of the symmetric group is a Specht
module.

Only counting is left to do. The partitions of `n` index the conjugacy classes of `Sₙ`
(`TauCeti.partitionEquivConjClasses`), and over any field with `k[G]` semisimple the isomorphism
classes of simple `k[G]`-modules are at most as many as the conjugacy classes
(`TauCeti.card_simpleSubmoduleClasses_le_card_conjClasses`). An injection from a finite set into a
set of no greater size is a bijection.

Working over `ℚ` rather than over `ℂ` costs nothing here, because the counting bound is not a
splitting-field statement: it bounds the simple modules over *any* field by the conjugacy classes,
and the Specht modules already saturate the bound over `ℚ`. In particular the classification does
not go through absolute irreducibility. The separate statement `End_{ℚ[Sₙ]} S^μ ≅ ℚ` is proved in
`TauCeti.RepresentationTheory.Symmetric.Specht.AbsoluteIrreducibility`; it is the input a
corresponding classification over `ℂ` will need.

The classification is stated in each of the three languages a consumer may already be working in:
the isomorphism classes of simple `ℚ[Sₙ]`-modules, the irreducible representations, and the simple
objects of `FDRep ℚ Sₙ`. Each language has a `∃!` form, since the partition attached to a simple
module or irreducible representation is what the classification is usually quoted as producing;
the module and `FDRep` languages additionally have explicit bijections. The comparison of those
two bijections is
`TauCeti.coe_simpleFDRepClassesEquivSimpleModuleClasses`: the bijection between the two targets that
the two classifications assemble to is the map sending a simple object to the module it carries, so
the readings agree.

## Main results

* `TauCeti.spechtModuleClass`: the isomorphism class of the simple `ℚ[Sₙ]`-module `S^μ`.
* `TauCeti.partitionEquivSimpleModuleClasses`: **the classification**, `μ ↦ S^μ` as a bijection from
  `Nat.Partition n` to the isomorphism classes of simple `ℚ[Sₙ]`-modules.
* `TauCeti.existsUnique_nonempty_linearEquiv_spechtModule`: every simple `ℚ[Sₙ]`-module is
  isomorphic to a Specht module for exactly one partition.
* `TauCeti.existsUnique_nonempty_equiv_spechtModule`: every irreducible rational representation of
  `Sₙ` is equivalent to a Specht module for exactly one partition.
* `TauCeti.partitionEquivSimpleFDRepClasses`: **the classification in `FDRep ℚ Sₙ`**, `μ ↦ S^μ` as a
  bijection from `Nat.Partition n` to the isomorphism classes of simple objects, with
  `TauCeti.existsUnique_nonempty_iso_spechtModule` its `∃!` form.
* `TauCeti.coe_simpleFDRepClassesEquivSimpleModuleClasses`: the two classifications agree.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Distinctness and completeness".
-/

public section

namespace TauCeti

open scoped MonoidAlgebra

variable {n : ℕ}

/-- The order of a symmetric group is nonzero in `ℚ`, so `ℚ[Sₙ]` is semisimple by Maschke's
theorem. This is what puts the isotypic theory at the disposal of the classification. -/
private instance : NeZero ((Nat.card (Equiv.Perm (Fin n)) : ℚ)) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- **The isomorphism class of the Specht module `S^μ`**, as a simple module over the rational
group algebra of `Sₙ`.

That this is built as `TauCeti.simpleModuleClass` of the module `S^μ` carries is an
implementation detail; use `TauCeti.spechtModuleClass_def` to see it. -/
noncomputable def spechtModuleClass (μ : n.Partition) :
    SimpleSubmoduleClasses ℚ[Equiv.Perm (Fin n)] ℚ[Equiv.Perm (Fin n)] :=
  simpleModuleClass _ (_root_.Representation.asModule (spechtModule μ).ρ)

/-- The defining equation of `TauCeti.spechtModuleClass`: it is the class of the `ℚ[Sₙ]`-module
carried by the Specht module `S^μ`. -/
@[simp]
theorem spechtModuleClass_def (μ : n.Partition) :
    spechtModuleClass μ =
      simpleModuleClass _ (_root_.Representation.asModule (spechtModule μ).ρ) :=
  (rfl)

/-- **Specht modules with distinct shapes carry non-isomorphic modules.** This is
`TauCeti.spechtModule_iso_iff` read through the dictionary between isomorphism of representations
and isomorphism of the `ℚ[Sₙ]`-modules they carry.

This is deliberately not a `simp` lemma: `(spechtModule μ).ρ` is not a simp normal form, because the
`simp` lemma `FDRep.of_ρ'` unfolds it to the composite that `spechtModule` is built from, so `simp`
would never see this left-hand side. The parallel `TauCeti.spechtModule_iso_iff` can carry the tag
because its left-hand side mentions only the `FDRep` object. -/
theorem nonempty_linearEquiv_spechtModule_asModule_iff (μ ν : n.Partition) :
    Nonempty (_root_.Representation.asModule (spechtModule μ).ρ ≃ₗ[ℚ[Equiv.Perm (Fin n)]]
      _root_.Representation.asModule (spechtModule ν).ρ) ↔ μ = ν := by
  refine ⟨fun ⟨f⟩ ↦ (spechtModule_iso_iff μ ν).mp ⟨fdRepIsoOfAsModuleLinearEquiv f⟩, ?_⟩
  rintro rfl
  exact ⟨LinearEquiv.refl _ _⟩

/-- Distinct partitions give distinct isomorphism classes: the irredundancy half of the
classification. -/
theorem spechtModuleClass_injective : Function.Injective (spechtModuleClass (n := n)) := by
  intro μ ν h
  rw [spechtModuleClass_def, spechtModuleClass_def, simpleModuleClass_eq_iff] at h
  exact (nonempty_linearEquiv_spechtModule_asModule_iff μ ν).mp h

/-- **The Specht modules exhaust the simple `ℚ[Sₙ]`-modules.** They are as many as the conjugacy
classes of `Sₙ` and pairwise non-isomorphic, and no field admits more isomorphism classes of simple
modules over the group algebra than the group has conjugacy classes. -/
theorem spechtModuleClass_bijective : Function.Bijective (spechtModuleClass (n := n)) := by
  classical
  have : Finite (SimpleSubmoduleClasses ℚ[Equiv.Perm (Fin n)] ℚ[Equiv.Perm (Fin n)]) :=
    .of_equiv _ (simpleSubmoduleClassesEquiv _ _).symm
  let _ := Fintype.ofFinite (SimpleSubmoduleClasses ℚ[Equiv.Perm (Fin n)] ℚ[Equiv.Perm (Fin n)])
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨spechtModuleClass_injective, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  refine le_antisymm (Nat.card_le_card_of_injective _ spechtModuleClass_injective) ?_
  exact (card_simpleSubmoduleClasses_le_card_conjClasses ℚ (Equiv.Perm (Fin n))).trans
    (Nat.card_congr (partitionEquivConjClasses n).symm).le

/-- **The classification of the irreducible rational representations of the symmetric group.**
Sending a partition of `n` to the isomorphism class of the Specht module `S^μ` is a bijection onto
the isomorphism classes of simple `ℚ[Sₙ]`-modules. -/
noncomputable def partitionEquivSimpleModuleClasses (n : ℕ) :
    n.Partition ≃ SimpleSubmoduleClasses ℚ[Equiv.Perm (Fin n)] ℚ[Equiv.Perm (Fin n)] :=
  Equiv.ofBijective _ spechtModuleClass_bijective

@[simp]
theorem partitionEquivSimpleModuleClasses_apply (μ : n.Partition) :
    partitionEquivSimpleModuleClasses n μ = spechtModuleClass μ :=
  (rfl)

private theorem exists_nonempty_linearEquiv_spechtModule (M : Type*) [AddCommGroup M]
    [Module ℚ[Equiv.Perm (Fin n)] M] [IsSimpleModule ℚ[Equiv.Perm (Fin n)] M] :
    ∃ μ : n.Partition, Nonempty (M ≃ₗ[ℚ[Equiv.Perm (Fin n)]]
      _root_.Representation.asModule (spechtModule μ).ρ) := by
  obtain ⟨μ, hμ⟩ := (spechtModuleClass_bijective (n := n)).surjective
    (simpleModuleClass ℚ[Equiv.Perm (Fin n)] M)
  rw [spechtModuleClass_def] at hμ
  exact ⟨μ, simpleModuleClass_eq_iff.mp hμ.symm⟩

private theorem exists_nonempty_equiv_spechtModule {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    ∃ μ : n.Partition, Nonempty (ρ.Equiv (spechtModule μ).ρ) := by
  obtain ⟨μ, hμ⟩ := exists_nonempty_linearEquiv_spechtModule (n := n) ρ.asModule
  exact ⟨μ, Representation.nonempty_equiv_iff.mpr hμ⟩

/-- **Every simple `ℚ[Sₙ]`-module is a Specht module for exactly one partition.** -/
theorem existsUnique_nonempty_linearEquiv_spechtModule (M : Type*) [AddCommGroup M]
    [Module ℚ[Equiv.Perm (Fin n)] M] [IsSimpleModule ℚ[Equiv.Perm (Fin n)] M] :
    ∃! μ : n.Partition, Nonempty (M ≃ₗ[ℚ[Equiv.Perm (Fin n)]]
      _root_.Representation.asModule (spechtModule μ).ρ) := by
  obtain ⟨μ, hμ⟩ := exists_nonempty_linearEquiv_spechtModule (n := n) M
  exact ⟨μ, hμ, fun ν ⟨f⟩ ↦
    (nonempty_linearEquiv_spechtModule_asModule_iff ν μ).mp ⟨f.symm.trans hμ.some⟩⟩

/-- **Every irreducible rational representation of `Sₙ` is a Specht module for exactly one
partition.** -/
theorem existsUnique_nonempty_equiv_spechtModule {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    ∃! μ : n.Partition, Nonempty (ρ.Equiv (spechtModule μ).ρ) := by
  obtain ⟨μ, hμ⟩ := exists_nonempty_equiv_spechtModule ρ
  refine ⟨μ, hμ, fun ν ⟨φ⟩ ↦ ?_⟩
  exact (nonempty_linearEquiv_spechtModule_asModule_iff ν μ).mp
    (Representation.nonempty_equiv_iff.mp ⟨φ.symm.trans hμ.some⟩)

section Categorical

open CategoryTheory

/-- **The isomorphism class of the Specht module `S^μ` as a simple object of `FDRep ℚ Sₙ`.** The
categorical counterpart of `TauCeti.spechtModuleClass`. -/
noncomputable def spechtModuleFDRepClass (μ : n.Partition) :
    SimpleFDRepClasses ℚ (Equiv.Perm (Fin n)) :=
  SimpleFDRepClasses.mk (spechtModule μ)

@[simp]
theorem spechtModuleFDRepClass_def (μ : n.Partition) :
    spechtModuleFDRepClass μ = SimpleFDRepClasses.mk (spechtModule μ) :=
  (rfl)

/-- **The classification, read in `FDRep ℚ Sₙ`.** Sending a partition of `n` to the isomorphism
class of the Specht module `S^μ` is a bijection onto the isomorphism classes of simple objects of
`FDRep ℚ Sₙ`. -/
theorem spechtModuleFDRepClass_bijective :
    Function.Bijective (spechtModuleFDRepClass (n := n)) := by
  constructor
  · intro μ ν h
    rw [spechtModuleFDRepClass_def, spechtModuleFDRepClass_def,
      SimpleFDRepClasses.mk_eq_mk_iff] at h
    exact (spechtModule_iso_iff μ ν).mp h
  · refine SimpleFDRepClasses.ind (fun X hX ↦ ?_)
    let _ := hX
    have : _root_.Representation.IsIrreducible X.ρ :=
      (FDRep.simple_iff_isIrreducible X).mp hX
    obtain ⟨μ, hμ⟩ := exists_nonempty_equiv_spechtModule X.ρ
    refine ⟨μ, ?_⟩
    rw [spechtModuleFDRepClass_def, SimpleFDRepClasses.mk_eq_mk_iff]
    exact ⟨(nonempty_fdRepIso_iff.mpr hμ).some.symm⟩

/-- **The categorical classification of the irreducible rational representations of the symmetric
group**: `μ ↦ S^μ` is a bijection from the partitions of `n` to the isomorphism classes of simple
objects of `FDRep ℚ Sₙ`. -/
noncomputable def partitionEquivSimpleFDRepClasses (n : ℕ) :
    n.Partition ≃ SimpleFDRepClasses ℚ (Equiv.Perm (Fin n)) :=
  Equiv.ofBijective _ spechtModuleFDRepClass_bijective

@[simp]
theorem partitionEquivSimpleFDRepClasses_apply (μ : n.Partition) :
    partitionEquivSimpleFDRepClasses n μ = spechtModuleFDRepClass μ :=
  (rfl)

/-- **Every simple object of `FDRep ℚ Sₙ` is a Specht module for exactly one partition.** This is
the classification in the language of the categorical representation API. -/
theorem existsUnique_nonempty_iso_spechtModule (X : FDRep ℚ (Equiv.Perm (Fin n))) [Simple X] :
    ∃! μ : n.Partition, Nonempty (X ≅ spechtModule μ) := by
  have : _root_.Representation.IsIrreducible X.ρ := (FDRep.simple_iff_isIrreducible X).mp ‹_›
  obtain ⟨μ, hμ, huniq⟩ := existsUnique_nonempty_equiv_spechtModule X.ρ
  exact ⟨μ, nonempty_fdRepIso_iff.mpr hμ, fun ν hν ↦ huniq ν (nonempty_fdRepIso_iff.mp hν)⟩

/-- The partition a Specht module's class names is the partition it was built from: the `symm`
companion of `TauCeti.partitionEquivSimpleFDRepClasses_apply`. -/
@[simp]
theorem partitionEquivSimpleFDRepClasses_symm_mk_spechtModule (μ : n.Partition) :
    (partitionEquivSimpleFDRepClasses n).symm
      (SimpleFDRepClasses.mk (spechtModule μ)) = μ := by
  rw [← spechtModuleFDRepClass_def, ← partitionEquivSimpleFDRepClasses_apply,
    Equiv.symm_apply_apply]

/-- **The categorical classification and the module classification are the same bijection**, read
across `μ ↦ S^μ`. -/
noncomputable def simpleFDRepClassesEquivSimpleModuleClasses (n : ℕ) :
    SimpleFDRepClasses ℚ (Equiv.Perm (Fin n)) ≃
      SimpleSubmoduleClasses ℚ[Equiv.Perm (Fin n)] ℚ[Equiv.Perm (Fin n)] :=
  (partitionEquivSimpleFDRepClasses n).symm.trans (partitionEquivSimpleModuleClasses n)

/-- **The abstract comparison of the two classifications is the concrete one**: the bijection
`TauCeti.simpleFDRepClassesEquivSimpleModuleClasses`, assembled from the two classification
bijections, is the map sending a simple object of `FDRep ℚ Sₙ` to the isomorphism class of the
`ℚ[Sₙ]`-module it carries. -/
@[simp]
theorem coe_simpleFDRepClassesEquivSimpleModuleClasses :
    ⇑(simpleFDRepClassesEquivSimpleModuleClasses n) =
      SimpleFDRepClasses.toSimpleSubmoduleClasses := by
  funext c
  induction c using SimpleFDRepClasses.ind with
  | _ X hX =>
    let _ := hX
    -- Name the partition of `X`, so that both sides are evaluated at a Specht module.
    obtain ⟨μ, hμ, -⟩ := existsUnique_nonempty_iso_spechtModule X
    rw [(SimpleFDRepClasses.mk_eq_mk_iff X (spechtModule μ)).mpr hμ]
    rw [SimpleFDRepClasses.toSimpleSubmoduleClasses_mk]
    simp [-SimpleFDRepClasses.mk_eq_toSkeleton, simpleFDRepClassesEquivSimpleModuleClasses]

end Categorical

end TauCeti
