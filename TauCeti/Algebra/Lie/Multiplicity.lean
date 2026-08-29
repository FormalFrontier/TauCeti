/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Lie.Schur
public import TauCeti.Algebra.Lie.Submodule.DirectSum
-- Non-public: `TauCeti.exists_isInternal_isIrreducible` appears only inside proofs, never in the
-- type of an exported declaration.
import TauCeti.Algebra.Lie.Submodule.Decomposition

public section

/-!
# The multiplicity of an irreducible Lie module

The **multiplicity** of a Lie module `S` in a Lie module `M` is
`TauCeti.LieModule.isotypicMultiplicity K L M S = dim_K (S →ₗ⁅K,L⁆ M)`. This file proves that when
`S` is irreducible and `M` is finite-dimensional over an algebraically closed field, this number
counts the summands equivalent to `S` in any decomposition of `M` into irreducible Lie submodules,
and is therefore independent of the decomposition chosen.

## The argument

The morphism space is **additive over a direct sum in its target**: a morphism `S →ₗ⁅K,L⁆ ⨁ i, Pᵢ`
is the same thing as a family of morphisms `S →ₗ⁅K,L⁆ Pᵢ`, one for each `i`
(`TauCeti.LieModule.lieModuleHomDirectSumEquiv`), because the inclusions and the projections of an
external direct sum are morphisms of Lie modules (`DirectSum.lieModuleOf`,
`DirectSum.lieModuleComponent`) and a finite family of components reassembles to the element it
came from. Transporting along `TauCeti.LieSubmodule.directSumEquiv` turns that into additivity over
an *internal* decomposition of `M` by Lie submodules.

The per-summand contribution is Schur's lemma in the dimension form of
`TauCeti/Algebra/Lie/Schur.lean`: for irreducible `S` and `Nᵢ` over an algebraically closed field,
`dim_K (S →ₗ⁅K,L⁆ Nᵢ)` is `1` when `Nᵢ ≃ S` and `0` otherwise. Summing gives the count. Since the
left-hand side never mentions the decomposition, two decompositions of the same module have the
same number of summands equivalent to `S`; this is the uniqueness statement that makes "the
multiplicity of `S` in `M`" well defined.

Nothing here needs complete reducibility: the counting theorem is stated for a decomposition it is
handed. Complete reducibility is what *produces* such a decomposition, through
`TauCeti.exists_isInternal_isIrreducible`, and is used only for the existence statement
`TauCeti.LieModule.exists_isInternal_isIrreducible_and_isotypicMultiplicity_eq_ncard`.

## Main definitions

* `TauCeti.LieModule.lieModuleHomDirectSumEquiv`: **the morphism space is additive over a direct
  sum in its target**, `(S →ₗ⁅R,L⁆ ⨁ i, Pᵢ) ≃ₗ[R] Π i, (S →ₗ⁅R,L⁆ Pᵢ)`.
* `TauCeti.LieModule.isotypicMultiplicity`: the multiplicity `dim_K (S →ₗ⁅K,L⁆ M)`.

## Main results

* `TauCeti.LieModuleHom.sum_apply` and `TauCeti.LieModuleHom.instFiniteDimensional`: the two
  general facts about morphism spaces of Lie modules that the additivity below rests on.
* `TauCeti.LieModule.finrank_lieModuleHom_of_isInternal`: **additivity of the morphism space over a
  decomposition of `M` into Lie submodules.**
* `TauCeti.LieModule.isotypicMultiplicity_eq_ncard_of_isInternal`: **the multiplicity counts the
  summands equivalent to `S`** in a decomposition of `M` into irreducibles.
* `TauCeti.LieModule.ncard_setOf_nonempty_lieModuleEquiv_eq`: **the count is independent of the
  decomposition.**

## Roadmap

This is the `isotypicMultiplicity` target of the decomposition toolkit in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, together with the additivity of
the morphism space over a direct-sum decomposition that `TauCeti/Algebra/Lie/Schur.lean` names as
the missing ingredient of the multiplicity theorem. The multiplicity is stated for an arbitrary
irreducible `S` rather than for the irreducible quotient `L(λ)`, which the roadmap's own signature
uses; the `L(λ)`-indexed form is this statement with `S` instantiated. Two further toolkit items
remain: the finrank of the isotypic component,
`dim (isotypicComponent S M) = isotypicMultiplicity · dim S`, and the packaged decomposition
`M ≃ ⨁ S^{⊕ m}`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.
-/

universe u v w w₁ w₂

namespace TauCeti.LieModuleHom

/-! ### Morphism spaces of Lie modules -/

section

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {ι : Type w₂}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N]

/-- A finite sum of morphisms of Lie modules is evaluated summandwise. -/
theorem sum_apply {s : Finset ι} (F : ι → (M →ₗ⁅R,L⁆ N)) (m : M) :
    (∑ i ∈ s, F i) m = ∑ i ∈ s, F i m := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, _root_.LieModuleHom.add_apply, ih]

variable (R L M N) [LieAlgebra R L] [_root_.LieModule R L N]

-- Only the injectivity of this bundling is used, to transport finite-dimensionality of the
-- ambient space of linear maps to the subspace of Lie module morphisms.
private def toLinearMapₗ : (M →ₗ⁅R,L⁆ N) →ₗ[R] (M →ₗ[R] N) where
  toFun f := (f : M →ₗ[R] N)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem toLinearMapₗ_injective : Function.Injective (toLinearMapₗ R L M N) :=
  fun _ _ h ↦ _root_.LieModuleHom.coe_injective (congrArg (fun k : M →ₗ[R] N ↦ ⇑k) h)

end

/-- The morphism space of two finite-dimensional Lie modules is finite-dimensional: it embeds in
the space of all linear maps between them. -/
instance instFiniteDimensional {K : Type u} {L : Type v} {M : Type w} {N : Type w₁}
    [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [FiniteDimensional K M]
    [AddCommGroup N] [Module K N] [LieRingModule L N] [_root_.LieModule K L N]
    [FiniteDimensional K N] :
    FiniteDimensional K (M →ₗ⁅K,L⁆ N) :=
  Module.Finite.of_injective (toLinearMapₗ K L M N) (toLinearMapₗ_injective K L M N)

end TauCeti.LieModuleHom

namespace TauCeti.LieModule

open Module (finrank)
open scoped DirectSum

/-! ### Additivity of the morphism space over a direct sum -/

section Additivity

variable {R : Type u} {L : Type v} {ι : Type w₂} [DecidableEq ι] [Fintype ι]
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable (R L)
variable (S : Type w) [AddCommGroup S] [Module R S] [LieRingModule L S] [_root_.LieModule R L S]
variable (P : ι → Type w₁) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
  [∀ i, LieRingModule L (P i)] [∀ i, _root_.LieModule R L (P i)]

/-- **The morphism space is additive over a direct sum in its target.** A morphism from `S` into a
finite external direct sum of Lie modules is the family of its components, and conversely a family
of morphisms assembles to one; this is an isomorphism of `R`-modules. -/
def lieModuleHomDirectSumEquiv :
    (S →ₗ⁅R,L⁆ ⨁ i, P i) ≃ₗ[R] Π i, (S →ₗ⁅R,L⁆ P i) where
  toFun f i := (DirectSum.lieModuleComponent R ι L P i).comp f
  map_add' _ _ := by ext i s; simp [DirectSum.lieModuleComponent]
  map_smul' _ _ := by ext i s; simp [DirectSum.lieModuleComponent]
  invFun g := ∑ i, (DirectSum.lieModuleOf R ι L P i).comp (g i)
  left_inv f := by
    refine LieModuleHom.ext fun s ↦ ?_
    rw [LieModuleHom.sum_apply]
    exact DirectSum.sum_univ_of (f s)
  right_inv g := by
    refine funext fun j ↦ LieModuleHom.ext fun s ↦ ?_
    rw [_root_.LieModuleHom.comp_apply, LieModuleHom.sum_apply]
    -- `DirectSum.lieModuleComponent` and `DirectSum.lieModuleOf` have no interface lemmas of their
    -- own; both are transparent for the underlying `DirectSum.of` and evaluation, which is the
    -- form in which the sum collapses to its `j`-th term.
    change (∑ i, DirectSum.of P i (g i s)) j = g j s
    rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single j]
    · simp
    · exact fun b _ hb ↦ DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb)
    · simp

omit [_root_.LieModule R L S] in
@[simp]
theorem lieModuleHomDirectSumEquiv_apply (f : S →ₗ⁅R,L⁆ ⨁ i, P i) (i : ι) (s : S) :
    lieModuleHomDirectSumEquiv R L S P f i s = f s i :=
  (rfl)

omit [_root_.LieModule R L S] in
@[simp]
theorem lieModuleHomDirectSumEquiv_symm_apply (g : Π i, (S →ₗ⁅R,L⁆ P i)) (s : S) :
    (lieModuleHomDirectSumEquiv R L S P).symm g s = ∑ i, DirectSum.of P i (g i s) :=
  LieModuleHom.sum_apply _ s

end Additivity

/-! ### Additivity over an internal decomposition -/

section Internal

variable {K : Type u} {L : Type v} {M : Type w} {ι : Type w₂} [DecidableEq ι] [Fintype ι]
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [_root_.LieModule K L M]
variable [FiniteDimensional K M]
variable (S : Type w₁) [AddCommGroup S] [Module K S] [LieRingModule L S] [_root_.LieModule K L S]
variable [FiniteDimensional K S]

omit [_root_.LieModule K L S] in
/-- **Additivity of the morphism space over a decomposition of the target.** If the Lie submodules
`N i` decompose `M`, the dimension of `S →ₗ⁅K,L⁆ M` is the sum of the dimensions of the
`S →ₗ⁅K,L⁆ N i`. Finite-dimensionality of `S` is what makes each summand's morphism space
finite-dimensional, so that the dimensions really add. -/
theorem finrank_lieModuleHom_of_isInternal (N : ι → LieSubmodule K L M)
    (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule) :
    finrank K (S →ₗ⁅K,L⁆ M) = ∑ i, finrank K (S →ₗ⁅K,L⁆ N i) := by
  have hfin : ∀ i, FiniteDimensional K (N i) := fun i ↦
    FiniteDimensional.of_injective (N i).toSubmodule.subtype Subtype.val_injective
  have hhom : ∀ i, FiniteDimensional K (S →ₗ⁅K,L⁆ (N i : Type w)) := fun i ↦
    have := hfin i; inferInstance
  rw [← (LieModuleEquiv.congrRight (M := S) (LieSubmodule.directSumEquiv N h)).finrank_eq,
    (lieModuleHomDirectSumEquiv K L S fun i ↦ (N i : Type w)).finrank_eq,
    Module.finrank_pi_fintype]

end Internal

/-! ### The multiplicity of an irreducible module -/

section Multiplicity

variable (K : Type u) (L : Type v) (M : Type w) (S : Type w₁)
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [_root_.LieModule K L M]
variable [AddCommGroup S] [Module K S] [LieRingModule L S] [_root_.LieModule K L S]

/-- **The multiplicity of `S` in `M`**, the dimension of the space of morphisms `S →ₗ⁅K,L⁆ M`. For
irreducible `S` over an algebraically closed field this is the number of summands equivalent to `S`
in any decomposition of a finite-dimensional `M` into irreducibles
(`TauCeti.LieModule.isotypicMultiplicity_eq_ncard_of_isInternal`); stating it as the dimension of a
morphism space is what makes it manifestly independent of the decomposition. -/
noncomputable def isotypicMultiplicity : ℕ :=
  finrank K (S →ₗ⁅K,L⁆ M)

omit [_root_.LieModule K L S] in
/-- The multiplicity is the dimension of the morphism space. The definition is not exposed, so
this is how it is unfolded. -/
theorem isotypicMultiplicity_def : isotypicMultiplicity K L M S = finrank K (S →ₗ⁅K,L⁆ M) :=
  (rfl)

variable {K L M S}

/-- **An irreducible module occurs in itself with multiplicity one.** -/
theorem isotypicMultiplicity_self [IsAlgClosed K] [FiniteDimensional K S]
    [_root_.LieModule.IsIrreducible K L S] : isotypicMultiplicity K L S S = 1 :=
  finrank_lieModuleHom_self K L S

section Count

variable {ι : Type w₂} [DecidableEq ι] [Finite ι] [FiniteDimensional K M] [IsAlgClosed K]
variable [FiniteDimensional K S] [_root_.LieModule.IsIrreducible K L S]
variable (N : ι → LieSubmodule K L M) (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
variable (hirr : ∀ i, _root_.LieModule.IsIrreducible K L (N i))

include h hirr

open scoped Classical in
/-- **The multiplicity counts the summands equivalent to `S`.** For a decomposition of a
finite-dimensional module into irreducible Lie submodules over an algebraically closed field, the
multiplicity of an irreducible `S` is the number of indices whose summand is equivalent to `S`:
Schur's lemma makes each such summand contribute `1` to the morphism space and every other summand
contribute `0`. -/
theorem isotypicMultiplicity_eq_ncard_of_isInternal :
    isotypicMultiplicity K L M S = {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}.ncard := by
  have _i : Fintype ι := Fintype.ofFinite ι
  rw [isotypicMultiplicity_def, finrank_lieModuleHom_of_isInternal S N h]
  have hsum : ∀ i : ι,
      finrank K (S →ₗ⁅K,L⁆ N i) = if Nonempty (S ≃ₗ⁅K,L⁆ N i) then 1 else 0 := fun i ↦
    have := hirr i
    finrank_lieModuleHom K L
  rw [Finset.sum_congr rfl fun i _ ↦ hsum i, Finset.sum_boole,
    Set.ncard_eq_toFinset_card' {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}]
  simp

end Count

/-- **The number of summands equivalent to a given irreducible does not depend on the
decomposition.** Both counts compute the same multiplicity, which is defined without reference to
any decomposition. -/
theorem ncard_setOf_nonempty_lieModuleEquiv_eq [FiniteDimensional K M] [IsAlgClosed K]
    [FiniteDimensional K S] [_root_.LieModule.IsIrreducible K L S]
    {ι : Type w₂} [DecidableEq ι] [Finite ι] {ι' : Type w₂} [DecidableEq ι'] [Finite ι']
    (N : ι → LieSubmodule K L M) (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
    (hirr : ∀ i, _root_.LieModule.IsIrreducible K L (N i))
    (N' : ι' → LieSubmodule K L M) (h' : DirectSum.IsInternal fun j ↦ (N' j).toSubmodule)
    (hirr' : ∀ j, _root_.LieModule.IsIrreducible K L (N' j)) :
    {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}.ncard = {j | Nonempty (S ≃ₗ⁅K,L⁆ N' j)}.ncard := by
  rw [← isotypicMultiplicity_eq_ncard_of_isInternal N h hirr,
    isotypicMultiplicity_eq_ncard_of_isInternal N' h' hirr']

/-- **The multiplicity is realized.** Under complete reducibility a finite-dimensional module has a
decomposition into irreducible Lie submodules, and the multiplicity of an irreducible `S` is the
number of its summands equivalent to `S`. -/
theorem exists_isInternal_isIrreducible_and_isotypicMultiplicity_eq_ncard
    [FiniteDimensional K M] [IsAlgClosed K] [FiniteDimensional K S]
    [_root_.LieModule.IsIrreducible K L S] [ComplementedLattice (LieSubmodule K L M)] :
    ∃ (k : ℕ) (N : Fin k → LieSubmodule K L M),
      DirectSum.IsInternal (fun i ↦ (N i).toSubmodule) ∧
        (∀ i, _root_.LieModule.IsIrreducible K L (N i)) ∧
        isotypicMultiplicity K L M S = {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}.ncard := by
  obtain ⟨k, N, hint, hirr⟩ := exists_isInternal_isIrreducible K L M
  exact ⟨k, N, hint, hirr, isotypicMultiplicity_eq_ncard_of_isInternal N hint hirr⟩

end Multiplicity

end TauCeti.LieModule
