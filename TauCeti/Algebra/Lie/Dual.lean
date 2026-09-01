/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Lie.Schur

public section

/-!
# The dual of a finite-dimensional irreducible Lie module

The dual `M* = Module.Dual R M` of a Lie module carries the contragredient action
`⁅x, f⁆ m = - f ⁅x, m⁆` (Mathlib's `Module.Dual.instLieRingModule`). This file records the two
facts about it that a self-duality statement needs.

The first is that irreducibility passes to the dual in finite dimensions. If `N ≤ M*` is stable
under the action then so is the set of vectors every functional in `N` kills, because `⁅x, f⁆`
again lies in `N`. A nonzero `N` has a proper annihilator, hence a zero one, and in finite
dimensions that forces `N = ⊤`.

The second is that an invariant bilinear form on `M` is the same datum as a morphism `M → M*`. A
bilinear form on `M` *is* a linear map `M → M*`, and Mathlib's
`LinearMap.BilinForm.lieInvariant_iff` says that invariance is exactly membership of the maximal
trivial submodule, which `LieModule.maxTrivLinearMapEquivLieModuleHom` identifies with the morphism
space. Both directions of that dictionary are named here, so that a caller holding a particular form
or morphism can transport it. For an irreducible `M` Schur's lemma then upgrades a nonzero morphism
to an equivalence, so carrying a nonzero invariant form and being self-dual are the same condition.

## Main definitions

* `TauCeti.LieModule.lieModuleHomOfLieInvariant` and
  `TauCeti.LieModule.bilinFormOfLieModuleHom`: the two directions of the correspondence between
  invariant bilinear forms on `M` and morphisms `M → M*`, each preserving and reflecting vanishing.

## Main results

* `TauCeti.LieModule.exists_ne_zero_lieInvariant_iff_exists_ne_zero_lieModuleHom`: a nonzero
  invariant bilinear form on `M` is a nonzero morphism `M → M*`, over any commutative ring.
* `TauCeti.LieModule.isIrreducible_dual`: **the dual of a finite-dimensional irreducible Lie module
  is irreducible.**
* `TauCeti.LieModule.exists_ne_zero_lieInvariant_iff_nonempty_lieModuleEquiv_dual`: **a
  finite-dimensional irreducible Lie module carries a nonzero invariant bilinear form exactly when
  it is equivalent to its dual.**

## References

Duality of highest weight modules is the setting in which the highest-weight roadmap
(`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`) states self-duality of `L(λ)`,
the `exists_invariantForm_iff_neg_longest_smul_eq` target of its `Suggested.lean`; nothing in this
file mentions weights, so it is stated for an arbitrary Lie algebra.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.1.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre I, §3.3.
-/

namespace TauCeti.LieModule

open Module (Dual finrank)

universe u v w

/-! ### Annihilators of Lie submodules of the dual -/

section CommRing

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [_root_.LieModule R L M]

/-- The vectors of `M` annihilated by every functional in a Lie submodule `N` of the dual. It is a
Lie submodule because `N` is: if `f m = 0` for every `f ∈ N`, then `f ⁅x, m⁆ = -⁅x, f⁆ m = 0`,
the functional `⁅x, f⁆` again lying in `N`. -/
private def dualCoannihilator (N : LieSubmodule R L (Dual R M)) : LieSubmodule R L M where
  __ := N.toSubmodule.dualCoannihilator
  lie_mem {x m} hm := by
    simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid, Submodule.mem_dualCoannihilator,
      LieSubmodule.mem_toSubmodule] at hm ⊢
    intro f hf
    have h := hm ⁅x, f⁆ (N.lie_mem hf)
    rwa [Module.Dual.lie_apply, neg_eq_zero] at h

@[simp]
private theorem mem_dualCoannihilator {N : LieSubmodule R L (Dual R M)} {m : M} :
    m ∈ dualCoannihilator N ↔ ∀ f ∈ N, f m = 0 := by
  simp [dualCoannihilator, ← LieSubmodule.mem_toSubmodule, Submodule.mem_dualCoannihilator]

@[simp]
private theorem dualCoannihilator_toSubmodule (N : LieSubmodule R L (Dual R M)) :
    (dualCoannihilator N).toSubmodule = N.toSubmodule.dualCoannihilator := by
  ext m
  simp [Submodule.mem_dualCoannihilator]

/-- Only the zero submodule of the dual annihilates all of `M`. -/
private theorem eq_bot_of_dualCoannihilator_eq_top {N : LieSubmodule R L (Dual R M)}
    (h : dualCoannihilator N = ⊤) : N = ⊥ := by
  have hall : ∀ m : M, m ∈ dualCoannihilator N := by simp [h]
  refine eq_bot_iff.mpr fun f hf => ?_
  have hf0 : f = 0 := LinearMap.ext fun m => mem_dualCoannihilator.mp (hall m) f hf
  simp [hf0]

/-! ### Invariant bilinear forms as morphisms to the dual -/

/-- **The morphism `M → M*` attached to an invariant bilinear form.** A bilinear form on `M` *is* a
linear map `M → M*`; invariance says it lies in the maximal trivial submodule
(`LinearMap.BilinForm.lieInvariant_iff`), which `LieModule.maxTrivLinearMapEquivLieModuleHom`
identifies with the space of morphisms. -/
@[expose]
def lieModuleHomOfLieInvariant {Φ : LinearMap.BilinForm R M} (hΦ : Φ.lieInvariant L) :
    M →ₗ⁅R,L⁆ Dual R M :=
  _root_.LieModule.maxTrivLinearMapEquivLieModuleHom
    ⟨Φ, (LinearMap.BilinForm.lieInvariant_iff Φ).mp hΦ⟩

@[simp]
theorem lieModuleHomOfLieInvariant_apply {Φ : LinearMap.BilinForm R M} (hΦ : Φ.lieInvariant L)
    (m : M) : lieModuleHomOfLieInvariant hΦ m = Φ m :=
  rfl

@[simp]
theorem lieModuleHomOfLieInvariant_eq_zero_iff {Φ : LinearMap.BilinForm R M}
    (hΦ : Φ.lieInvariant L) : lieModuleHomOfLieInvariant hΦ = 0 ↔ Φ = 0 := by
  refine ⟨fun h => LinearMap.ext fun m => ?_, fun h => LieModuleHom.ext fun m => ?_⟩
  · simpa using congrArg (fun f => f m) h
  · simp [h]

/-- **The invariant bilinear form attached to a morphism `M → M*`**, inverse to
`TauCeti.LieModule.lieModuleHomOfLieInvariant`. -/
@[expose]
def bilinFormOfLieModuleHom (f : M →ₗ⁅R,L⁆ Dual R M) : LinearMap.BilinForm R M :=
  (_root_.LieModule.maxTrivLinearMapEquivLieModuleHom.symm f : LinearMap.BilinForm R M)

@[simp]
theorem bilinFormOfLieModuleHom_apply (f : M →ₗ⁅R,L⁆ Dual R M) (m : M) :
    bilinFormOfLieModuleHom f m = f m :=
  rfl

theorem lieInvariant_bilinFormOfLieModuleHom (f : M →ₗ⁅R,L⁆ Dual R M) :
    (bilinFormOfLieModuleHom f).lieInvariant L :=
  (LinearMap.BilinForm.lieInvariant_iff _).mpr
    (_root_.LieModule.maxTrivLinearMapEquivLieModuleHom.symm f).2

@[simp]
theorem bilinFormOfLieModuleHom_eq_zero_iff {f : M →ₗ⁅R,L⁆ Dual R M} :
    bilinFormOfLieModuleHom f = 0 ↔ f = 0 := by
  refine ⟨fun h => LieModuleHom.ext fun m => ?_, fun h => LinearMap.ext fun m => ?_⟩
  · simpa using congrArg (fun Φ => Φ m) h
  · simp [h]

/-- **A nonzero invariant bilinear form is a nonzero morphism to the dual.** A bilinear form on `M`
is a linear map `M → M*`, and invariance of the form is exactly equivariance of that map. -/
theorem exists_ne_zero_lieInvariant_iff_exists_ne_zero_lieModuleHom :
    (∃ Φ : LinearMap.BilinForm R M, Φ ≠ 0 ∧ Φ.lieInvariant L) ↔
      ∃ f : M →ₗ⁅R,L⁆ Dual R M, f ≠ 0 :=
  ⟨fun ⟨_, hΦ0, hΦ⟩ => ⟨lieModuleHomOfLieInvariant hΦ, by simpa using hΦ0⟩,
    fun ⟨f, hf0⟩ => ⟨bilinFormOfLieModuleHom f, by simpa using hf0,
      lieInvariant_bilinFormOfLieModuleHom f⟩⟩

end CommRing

/-! ### Irreducibility of the dual -/

section Field

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [_root_.LieModule K L M]
variable [FiniteDimensional K M] [_root_.LieModule.IsIrreducible K L M]

/-- **The dual of a finite-dimensional irreducible Lie module is irreducible.** A nonzero Lie
submodule `N` of `M*` does not annihilate all of `M`, so its annihilator is a proper Lie submodule
of `M` and therefore zero; the dimension count for annihilators in a finite-dimensional space then
makes `N` all of `M*`. -/
theorem isIrreducible_dual : _root_.LieModule.IsIrreducible K L (Dual K M) := by
  have _i : Nontrivial M := _root_.LieModule.nontrivial_of_isIrreducible K L M
  have hpos : 0 < finrank K M := Module.finrank_pos
  have _j : Nontrivial (Dual K M) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rwa [Subspace.dual_finrank_eq])
  refine _root_.LieModule.IsIrreducible.mk fun N hN => ?_
  have hbot : dualCoannihilator N = ⊥ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right fun h =>
      hN (eq_bot_of_dualCoannihilator_eq_top h)
  have hrank : finrank K N.toSubmodule = finrank K (Dual K M) := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (K := K) (V := M) N.toSubmodule
    rw [← dualCoannihilator_toSubmodule, hbot] at h
    simpa [Subspace.dual_finrank_eq] using h
  rw [← LieSubmodule.toSubmodule_eq_top]
  exact Submodule.eq_top_of_finrank_eq hrank

/-! ### Self-duality -/

/-- **A finite-dimensional irreducible Lie module carries a nonzero invariant bilinear form exactly
when it is self-dual.** The form is a morphism `M → M*`, and by Schur's lemma a nonzero morphism
between the irreducible modules `M` and `M*` is an equivalence. -/
theorem exists_ne_zero_lieInvariant_iff_nonempty_lieModuleEquiv_dual :
    (∃ Φ : LinearMap.BilinForm K M, Φ ≠ 0 ∧ Φ.lieInvariant L) ↔
      Nonempty (M ≃ₗ⁅K,L⁆ Dual K M) := by
  have _i := isIrreducible_dual (K := K) (L := L) (M := M)
  rw [exists_ne_zero_lieInvariant_iff_exists_ne_zero_lieModuleHom,
    ← nonempty_lieModuleEquiv_iff_exists_ne_zero]

end Field

end TauCeti.LieModule
