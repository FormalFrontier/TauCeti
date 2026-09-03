/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Order.CompactlyGenerated

/-!
# Internal direct sums from explicit equivalences

This file provides reusable infrastructure for direct sums of submodules.  The generic
`DirectSum.piInclusion`, `DirectSum.piSubmodule`, and `DirectSum.piSubmoduleEquiv` declarations
describe their componentwise inclusion and range, while `DirectSum.isInternal_of_lof` gives a
criterion for proving that a family of submodules is an internal direct sum by identifying its
summands with the components of a linear equivalence.  The file also specializes the compactness
bound `TauCeti.finite_ne_bot_of_iSupIndep_of_isCompactElement` to submodules,
`TauCeti.Submodule.finite_ne_bot_of_iSupIndep_of_fg`.
-/

public section

open scoped DirectSum

namespace TauCeti

/-- The canonical inclusion of a direct sum of submodules into the direct sum of their ambient
modules. -/
def DirectSum.piInclusion {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    (⨁ i, N i) →ₗ[R] ⨁ i, M i :=
  DirectSum.lmap fun i ↦ (N i).subtype

/-- The submodule of the direct sum consisting of elements whose components lie in the given
submodules. -/
def DirectSum.piSubmodule {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    Submodule R (⨁ i, M i) :=
  LinearMap.range (TauCeti.DirectSum.piInclusion N)

/-- The componentwise formula for the inclusion of a direct sum of submodules. -/
@[simp]
theorem DirectSum.piInclusion_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, N i) (i : ι) :
    TauCeti.DirectSum.piInclusion N x i = (x i : M i) := by
  rw [TauCeti.DirectSum.piInclusion, DirectSum.lmap_apply, Submodule.coe_subtype]

/-- The inclusion of a generator of a direct sum of submodules. -/
@[simp]
theorem DirectSum.piInclusion_lof {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (i : ι)
    (x : N i)
    [DecidableEq ι] :
    TauCeti.DirectSum.piInclusion N
        (DirectSum.lof R ι (fun i ↦ N i) i x) = DirectSum.lof R ι (fun i ↦ M i) i x := by
  rw [TauCeti.DirectSum.piInclusion, DirectSum.lmap_lof, Submodule.coe_subtype]

private theorem DirectSum.piInclusion_injective {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    Function.Injective (TauCeti.DirectSum.piInclusion N) := by
  rw [TauCeti.DirectSum.piInclusion]
  refine (DirectSum.lmap_injective fun i ↦ (N i).subtype).mpr fun i ↦ ?_
  exact (N i).injective_subtype

/-- The linear equivalence from the direct sum of submodules to `piSubmodule N`. -/
noncomputable def DirectSum.piSubmoduleEquiv {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    (⨁ i, N i) ≃ₗ[R] TauCeti.DirectSum.piSubmodule N :=
  LinearEquiv.ofInjective (TauCeti.DirectSum.piInclusion N)
    (TauCeti.DirectSum.piInclusion_injective N)

/-- The underlying map of `piSubmoduleEquiv` is the canonical inclusion. -/
@[simp]
theorem DirectSum.piSubmoduleEquiv_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, N i) :
    ((TauCeti.DirectSum.piSubmoduleEquiv N x : TauCeti.DirectSum.piSubmodule N) :
      ⨁ i, M i) = TauCeti.DirectSum.piInclusion N x := by
  rw [TauCeti.DirectSum.piSubmoduleEquiv]
  exact LinearEquiv.ofInjective_apply _ x

/-- The inverse of `piSubmoduleEquiv` has the expected componentwise values. -/
@[simp]
theorem DirectSum.piSubmoduleEquiv_symm_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (y : TauCeti.DirectSum.piSubmodule N) (i : ι) :
    ((TauCeti.DirectSum.piSubmoduleEquiv N).symm y i : M i) = (y : ⨁ i, M i) i := by
  have h := TauCeti.DirectSum.piSubmoduleEquiv_apply N
    ((TauCeti.DirectSum.piSubmoduleEquiv N).symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  have hi := congrArg (fun z : ⨁ i, M i ↦ z i) h
  simpa only [TauCeti.DirectSum.piInclusion_apply] using hi.symm

/-- Membership in the direct sum of a family of submodules is componentwise. -/
@[simp]
theorem DirectSum.mem_piSubmodule_iff {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, M i) :
    x ∈ TauCeti.DirectSum.piSubmodule N ↔ ∀ i, x i ∈ N i := by
  rw [TauCeti.DirectSum.piSubmodule, TauCeti.DirectSum.piInclusion, DirectSum.range_lmap]
  simp [Submodule.mem_comap, DirectSum.coeFnLinearMap_apply, Submodule.mem_pi]

/-- An included summand belongs to the direct sum of a family of submodules. -/
theorem DirectSum.lof_mem_piSubmodule {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (i : ι)
    (x : N i)
    [DecidableEq ι] :
    DirectSum.lof R ι M i x ∈ TauCeti.DirectSum.piSubmodule N := by
  refine ⟨DirectSum.lof R ι (fun i ↦ N i) i x, ?_⟩
  exact TauCeti.DirectSum.piInclusion_lof N i x

-- The inverse congruence is definitionally the direct sum of the componentwise inverses; this
-- helper exposes that computation through the `DirectSum.lmap` API.
private theorem DirectSum.congrLinearEquiv_symm_apply {R ι : Type*} {N P : ι → Type*}
    [Semiring R] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    (e : ∀ i, N i ≃ₗ[R] P i) (x : ⨁ i, P i) :
    (DirectSum.congrLinearEquiv e).symm x =
      DirectSum.lmap (fun i ↦ (e i).symm.toLinearMap) x := by
  rfl

-- Mathlib defines `DirectSum.IsInternal A` as bijectivity of the canonical map
-- `DirectSum.coeAddMonoidHom A`; for a family of submodules that canonical map is
-- `DirectSum.coeLinearMap A` (the same function packaged as a `LinearMap`).  Mathlib states no
-- iff lemma for this module-level form, so the equivalence below is a definitional unfolding,
-- the same one Mathlib's own API relies on (e.g. `IsInternal.ofBijective_coeLinearMap_same`).
-- The helper is private and single-purpose, so a Mathlib refactor of either definition will
-- surface exactly here.
private theorem DirectSum.isInternal_iff_bijective_coeLinearMap {R ι M : Type*}
    [Semiring R] [DecidableEq ι] [AddCommMonoid M] [Module R M]
    {A : ι → Submodule R M} :
    DirectSum.IsInternal A ↔ Function.Bijective (DirectSum.coeLinearMap A) :=
  Iff.rfl

/-- The canonical inclusions of a family of submodules form an internal direct sum when they are
identified with the summands of an equivalence. -/
theorem DirectSum.isInternal_of_lof {R ι M : Type*} [Semiring R] [DecidableEq ι]
    [AddCommMonoid M] [Module R M] {A : ι → Submodule R M} {N : ι → Type*}
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (e : ∀ i, N i ≃ₗ[R] A i)
    (E : (⨁ i, N i) ≃ₗ[R] M)
    (hE : ∀ i (x : N i), E (DirectSum.lof R ι (fun i ↦ N i) i x) = (e i x : M)) :
    DirectSum.IsInternal A := by
  let F : (⨁ i, A i) ≃ₗ[R] M :=
    (DirectSum.congrLinearEquiv e).symm.trans E
  have hF : ∀ i (x : A i), F (DirectSum.lof R ι (fun i ↦ A i) i x) = (x : M) := by
    intro i x
    simp only [F, LinearEquiv.trans_apply]
    rw [DirectSum.congrLinearEquiv_symm_apply, DirectSum.lmap_lof]
    simpa using hE i ((e i).symm x)
  have hcoe : DirectSum.coeLinearMap A = F.toLinearMap := by
    apply DirectSum.linearMap_ext R
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
    exact (hF i x).symm
  rw [DirectSum.isInternal_iff_bijective_coeLinearMap, hcoe]
  exact F.bijective

-- The decomposition is spelled as `iSupIndep A` together with a finiteness hypothesis on
-- `⨆ i, A i` rather than as `DirectSum.IsInternal`, which carries a `DecidableEq` hypothesis on
-- the index type that the proof does not need.  Over a semiring an internal decomposition supplies
-- the two hypotheses through `DirectSum.IsInternal.submodule_iSupIndep` and
-- `DirectSum.IsInternal.submodule_iSup_eq_top`; the converse implication, and with it
-- `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, needs `[Ring R]` and
-- `[AddCommGroup M]`.
private theorem Submodule.finite_ne_bot_of_iSupIndep_of_fg_aux
    {R ι M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {A : ι → Submodule R M} (hAi : iSupIndep A) (hAf : (⨆ i, A i).FG) :
    {i | A i ≠ ⊥}.Finite :=
  finite_ne_bot_of_iSupIndep_of_isCompactElement hAi ((Submodule.fg_iff_compact _).mp hAf)

/-- An independent family of submodules spanning a finitely generated submodule has only finitely
many nonzero members. -/
theorem Submodule.finite_ne_bot_of_iSupIndep_of_fg {R ι M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {A : ι → Submodule R M} (hAi : iSupIndep A) (hAf : (⨆ i, A i).FG) :
    {i | A i ≠ ⊥}.Finite :=
  Submodule.finite_ne_bot_of_iSupIndep_of_fg_aux hAi hAf

end TauCeti
