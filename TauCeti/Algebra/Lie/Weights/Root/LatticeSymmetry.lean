/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Root.IntegralLattice

/-!
# Symmetries of the integral root--coroot lattice

The Chevalley--Demazure construction starts from the integral lattice spanned by a normalized
family of root vectors and by the coroots. A symmetry of the pinned Lie algebra does not usually
fix those generators pointwise: it permutes the roots, carries each coroot to the corresponding
coroot, and can change a root vector by a sign. This file proves that these equations preserve the
integral root--coroot span exactly.

The result is first stated at the natural module-theoretic level for an arbitrary family of root
vectors. It is then specialized to the Lie lattice of a Chevalley system, where the restriction is
packaged as an integral Lie algebra automorphism. The characteristic equations say that the
restriction and its inverse are the original ambient automorphism and its inverse on underlying
vectors.

This is the integral descent step used by the graph-automorphism lane of the pinned
Chevalley--Demazure construction. The signs are essential: graph automorphisms need not carry every
non-simple root vector with sign `+1`, while both signs are units over `ℤ` and hence preserve the
lattice.

## Main declarations

* `TauCeti.map_rootCorootSpan_eq_of_map_root_eq_or_eq_neg`: a signed permutation of the root
  vectors, compatible with the coroots, preserves the integral root--coroot span.
* `TauCeti.rootCorootSpanEquiv`: the resulting integral linear automorphism.
* `TauCeti.IsChevalleySystem.chevalleyLieLatticeEquiv`: its restriction to the Chevalley Lie
  lattice as an integral Lie algebra automorphism.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--27.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.1 and 12.2.

This advances the pinning and pinned-isomorphism targets of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Those targets are consumed by milestones L0 and L1 of
`TauCetiRoadmap/CFSGStatement/README.md`, which require the explicit pinned ambient groups and their
graph automorphisms.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

section RootCorootSpan

variable {x : Weight K H L → L} (g : L ≃ₗ[K] L) (σ : Equiv.Perm (Weight K H L))
variable (hroot : ∀ α, g (x α) = x (σ α) ∨ g (x α) = -x (σ α))
variable (hcoroot : ∀ α, g (coroot α : L) = (coroot (σ α) : L))

include σ hroot hcoroot

/-- **A signed permutation of the root vectors which carries coroots along the same root
permutation preserves the integral root--coroot span.**

Both inclusions are recorded: the forward one uses closure under negation, while the reverse one
uses preimages under `σ` and changes the sign of the source vector when necessary. Thus this is an
equality of integral lattices, not only forward stability. -/
theorem map_rootCorootSpan_eq_of_map_root_eq_or_eq_neg :
    (rootCorootSpan x).map (g.restrictScalars ℤ).toLinearMap =
      rootCorootSpan x := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, rootCorootSpan_le_iff]
    constructor
    · intro α
      rw [Submodule.mem_comap]
      rcases hroot α with h | h
      · rw [LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply, h]
        exact rootVector_mem_rootCorootSpan x (σ α)
      · rw [LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply, h]
        exact (rootCorootSpan x).neg_mem (rootVector_mem_rootCorootSpan x (σ α))
    · intro α
      rw [Submodule.mem_comap, LinearEquiv.coe_toLinearMap,
        LinearEquiv.restrictScalars_apply, hcoroot α]
      exact coroot_mem_rootCorootSpan x (σ α)
  · rw [rootCorootSpan_le_iff]
    constructor
    · intro β
      rcases hroot (σ.symm β) with h | h
      · refine ⟨x (σ.symm β), rootVector_mem_rootCorootSpan x _, ?_⟩
        rw [LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply, h,
          σ.apply_symm_apply]
      · refine ⟨-x (σ.symm β), (rootCorootSpan x).neg_mem
          (rootVector_mem_rootCorootSpan x _), ?_⟩
        rw [LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply, map_neg, h,
          σ.apply_symm_apply, neg_neg]
    · intro β
      refine ⟨(coroot (σ.symm β) : L), coroot_mem_rootCorootSpan x _, ?_⟩
      rw [LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply, hcoroot,
        σ.apply_symm_apply]

/-- Membership in the root--coroot span is invariant under a compatible signed root
permutation. This is the form used when an ambient automorphism must be shown to preserve an
admissible lattice. -/
@[simp]
theorem map_mem_rootCorootSpan_iff (z : L) :
    g z ∈ rootCorootSpan x ↔ z ∈ rootCorootSpan x := by
  have hmap := map_rootCorootSpan_eq_of_map_root_eq_or_eq_neg g σ hroot hcoroot
  calc
    g z ∈ rootCorootSpan x ↔
        g z ∈ (rootCorootSpan x).map (g.restrictScalars ℤ).toLinearMap := by rw [hmap]
    _ ↔ (g.restrictScalars ℤ).symm (g z) ∈ rootCorootSpan x :=
      Submodule.mem_map_equiv (rootCorootSpan x)
    _ ↔ z ∈ rootCorootSpan x := by
      change g.symm (g z) ∈ rootCorootSpan x ↔ z ∈ rootCorootSpan x
      rw [g.symm_apply_apply]

/-- The integral linear automorphism of the root--coroot span induced by a compatible signed
permutation of its root vectors and coroots. -/
noncomputable def rootCorootSpanEquiv : rootCorootSpan x ≃ₗ[ℤ] rootCorootSpan x :=
  (g.restrictScalars ℤ).ofSubmodules (rootCorootSpan x) (rootCorootSpan x)
    (map_rootCorootSpan_eq_of_map_root_eq_or_eq_neg g σ hroot hcoroot)

/-- The restricted integral automorphism acts as the ambient automorphism on underlying
vectors. -/
@[simp]
theorem coe_rootCorootSpanEquiv_apply (z : rootCorootSpan x) :
    (rootCorootSpanEquiv g σ hroot hcoroot z : L) = g z := by
  rfl

/-- The inverse restricted integral automorphism acts as the inverse ambient automorphism on
underlying vectors. -/
@[simp]
theorem coe_rootCorootSpanEquiv_symm_apply (z : rootCorootSpan x) :
    ((rootCorootSpanEquiv g σ hroot hcoroot).symm z : L) = g.symm z := by
  apply g.injective
  rw [g.apply_symm_apply, ← coe_rootCorootSpanEquiv_apply g σ hroot hcoroot,
    LinearEquiv.apply_symm_apply]

end RootCorootSpan

namespace IsChevalleySystem

variable [CharZero K] [LieModule.IsTriangularizable K H L]

variable {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)
variable (g : L ≃ₗ⁅K⁆ L) (σ : Equiv.Perm (Weight K H L))
variable (hroot : ∀ α, g (x α) = x (σ α) ∨ g (x α) = -x (σ α))
variable (hcoroot : ∀ α, g (coroot α : L) = (coroot (σ α) : L))

include hx σ hroot hcoroot

/-- The ambient Lie automorphism maps the Chevalley Lie lattice onto itself. -/
theorem map_chevalleyLieLattice_eq :
    hx.chevalleyLieLattice.toSubmodule.map
        (g.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      hx.chevalleyLieLattice.toSubmodule := by
  rw [hx.chevalleyLieLattice_toSubmodule]
  exact map_rootCorootSpan_eq_of_map_root_eq_or_eq_neg g σ hroot hcoroot

/-- Membership in the Chevalley Lie lattice is invariant under the ambient Lie automorphism. -/
@[simp]
theorem map_mem_chevalleyLieLattice_iff (z : L) :
    g z ∈ hx.chevalleyLieLattice ↔ z ∈ hx.chevalleyLieLattice := by
  simp only [hx.mem_chevalleyLieLattice_iff]
  exact map_mem_rootCorootSpan_iff g σ hroot hcoroot z

/-- **A compatible signed root permutation restricts to an integral Lie automorphism of the
Chevalley lattice.** This is the integral automorphism descended from the pinned Lie algebra
symmetry. -/
noncomputable def chevalleyLieLatticeEquiv :
    hx.chevalleyLieLattice ≃ₗ⁅ℤ⁆ hx.chevalleyLieLattice where
  __ := (g.toLinearEquiv.restrictScalars ℤ).ofSubmodules
    hx.chevalleyLieLattice.toSubmodule hx.chevalleyLieLattice.toSubmodule
    (hx.map_chevalleyLieLattice_eq g σ hroot hcoroot)
  map_lie' := by
    intro a b
    apply Subtype.ext
    change g ⁅(a : L), (b : L)⁆ = ⁅g (a : L), g (b : L)⁆
    exact g.map_lie (a : L) (b : L)

/-- The restricted integral Lie automorphism acts as the ambient Lie automorphism on underlying
vectors. -/
@[simp]
theorem coe_chevalleyLieLatticeEquiv_apply (z : hx.chevalleyLieLattice) :
    (hx.chevalleyLieLatticeEquiv g σ hroot hcoroot z : L) = g z := by
  rfl

/-- The inverse restricted integral Lie automorphism acts as the inverse ambient Lie
automorphism on underlying vectors. -/
@[simp]
theorem coe_chevalleyLieLatticeEquiv_symm_apply (z : hx.chevalleyLieLattice) :
    ((hx.chevalleyLieLatticeEquiv g σ hroot hcoroot).symm z : L) = g.symm z := by
  rfl

end IsChevalleySystem

end TauCeti
