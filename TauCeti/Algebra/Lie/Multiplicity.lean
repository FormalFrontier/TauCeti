/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Lie.Schur
public import TauCeti.Algebra.Lie.Submodule.DirectSum

public section

/-!
# The multiplicity of an irreducible Lie module

The **multiplicity** of a Lie module `S` in a Lie module `M` is
`LieModule.isotypicMultiplicity R L M S = dim_R (S →ₗ⁅R,L⁆ M)`. This file proves that when `S` is
irreducible and both `S` and `M` are finite-dimensional over an algebraically closed field, this
number counts the summands equivalent to `S` in any decomposition of `M` into irreducible Lie
submodules, and is therefore independent of the decomposition chosen.

## The argument

The morphism space is **additive over a direct sum in its target**: a morphism `S →ₗ⁅R,L⁆ ⨁ i, Pᵢ`
is the same thing as a family of morphisms `S →ₗ⁅R,L⁆ Pᵢ`, one for each `i`
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
`TauCeti.exists_isInternal_isIrreducible` of `TauCeti/Algebra/Lie/Submodule/Decomposition.lean`,
which a consumer combines with the counting theorem below.

## Implementation notes

The multiplicity joins the Lie isotypy interface of `TauCeti/Algebra/Lie/Isotypic.lean`
(`LieModule.isotypicComponent`, `LieModule.IsIsotypicOfType`), and like that interface it is stated
without the universal enveloping algebra: this layer depends only on Lie submodules and Lie-module
morphisms. The comparison with the ring-level multiplicity theory of
`TauCeti/RingTheory/Semisimple/Multiplicity.lean` is therefore made where the rest of the
enveloping-algebra dictionary lives,
`LieModule.isotypicMultiplicity_eq_natCard_of_linearEquiv_pi` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Multiplicity.lean`, exactly as
`TauCeti/Algebra/Lie/UniversalEnveloping/Isotypic.lean` does for the isotypic component.

## Main definitions

* `TauCeti.LieModule.lieModuleHomDirectSumEquiv`: **the morphism space is additive over a direct
  sum in its target**, `(S →ₗ⁅R,L⁆ ⨁ i, Pᵢ) ≃ₗ[R] Π i, (S →ₗ⁅R,L⁆ Pᵢ)`.
* `LieModule.isotypicMultiplicity`: the multiplicity `dim_R (S →ₗ⁅R,L⁆ M)`.

## Main results

* `TauCeti.LieModule.finrank_lieModuleHom_eq_sum_of_isInternal`: **additivity of the morphism space
  over a decomposition of `M` into Lie submodules.**
* `LieModule.isotypicMultiplicity_eq_of_lieModuleEquiv_left` and
  `LieModule.isotypicMultiplicity_eq_of_lieModuleEquiv_right`: the multiplicity depends only on the
  equivalence classes of `S` and of `M`.
* `LieModule.isotypicMultiplicity_eq_ncard_of_isInternal`: **the multiplicity counts the summands
  equivalent to `S`** in a decomposition of `M` into irreducibles.
* `LieModule.ncard_setOf_nonempty_lieModuleEquiv_eq`: **the count is independent of the
  decomposition.**

## Roadmap

This is the `isotypicMultiplicity` target of the decomposition toolkit in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, together with the additivity of
the morphism space over a direct-sum decomposition that `TauCeti/Algebra/Lie/Schur.lean` names as
the missing ingredient of the multiplicity theorem. The multiplicity is stated for an arbitrary
irreducible `S` rather than for the irreducible quotient `L(λ)`, which the roadmap's own signature
uses; the `L(λ)`-indexed form is this statement with `S` instantiated. Two further toolkit items
remain: the finrank of the isotypic component,
`dim (LieModule.isotypicComponent S M) = isotypicMultiplicity · dim S`, and the packaged
decomposition `M ≃ ⨁ S^{⊕ m}`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.
-/

universe u v w w₁ w₂ w₃

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
  map_add' _ _ := by ext i s; simp
  map_smul' _ _ := by ext i s; simp
  invFun g := ∑ i, (DirectSum.lieModuleOf R ι L P i).comp (g i)
  left_inv f := by
    refine LieModuleHom.ext fun s ↦ ?_
    rw [LieModuleHom.sum_apply]
    simp only [_root_.LieModuleHom.comp_apply, DirectSum.lieModuleOf_apply,
      DirectSum.lieModuleComponent_apply]
    exact _root_.DirectSum.sum_univ_of (f s)
  right_inv g := by
    refine funext fun j ↦ LieModuleHom.ext fun s ↦ ?_
    rw [_root_.LieModuleHom.comp_apply, LieModuleHom.sum_apply]
    simp only [_root_.LieModuleHom.comp_apply, DirectSum.lieModuleOf_apply,
      DirectSum.lieModuleComponent_apply]
    rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single j]
    · simp
    · exact fun b _ hb ↦ _root_.DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb)
    · simp

omit [_root_.LieModule R L S] in
@[simp]
theorem lieModuleHomDirectSumEquiv_apply (f : S →ₗ⁅R,L⁆ ⨁ i, P i) (i : ι) (s : S) :
    lieModuleHomDirectSumEquiv R L S P f i s = f s i := by
  have h : lieModuleHomDirectSumEquiv R L S P f i
      = (DirectSum.lieModuleComponent R ι L P i).comp f := (rfl)
  rw [h]
  simp

omit [_root_.LieModule R L S] in
@[simp]
theorem lieModuleHomDirectSumEquiv_symm_apply (g : Π i, (S →ₗ⁅R,L⁆ P i)) (s : S) :
    (lieModuleHomDirectSumEquiv R L S P).symm g s
      = ∑ i, _root_.DirectSum.of P i (g i s) := by
  have h : (lieModuleHomDirectSumEquiv R L S P).symm g
      = ∑ i, (DirectSum.lieModuleOf R ι L P i).comp (g i) := (rfl)
  rw [h, LieModuleHom.sum_apply]
  simp

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
theorem finrank_lieModuleHom_eq_sum_of_isInternal (N : ι → LieSubmodule K L M)
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

end TauCeti.LieModule

namespace LieModule

open Module (finrank)

/-! ### The multiplicity of an irreducible module -/

section Def

variable (R : Type u) (L : Type v) (M : Type w) (S : Type w₁)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup S] [Module R S] [LieRingModule L S]

/-- **The multiplicity of `S` in `M`**, the dimension of the space of morphisms `S →ₗ⁅R,L⁆ M`. For
an irreducible, finite-dimensional `S` over an algebraically closed field this is the number of
summands equivalent to `S` in any decomposition of a finite-dimensional `M` into irreducibles
(`LieModule.isotypicMultiplicity_eq_ncard_of_isInternal`); stating it as the dimension of a
morphism space is what makes it manifestly independent of the decomposition. -/
noncomputable def isotypicMultiplicity : ℕ :=
  finrank R (S →ₗ⁅R,L⁆ M)

/-- The multiplicity is the dimension of the morphism space. The definition is not exposed, so
this is how it is unfolded. -/
theorem isotypicMultiplicity_def : isotypicMultiplicity R L M S = finrank R (S →ₗ⁅R,L⁆ M) :=
  (rfl)

end Def

/-! ### The multiplicity depends only on the two equivalence classes -/

section Invariance

variable {R : Type u} {L : Type v} {M : Type w} {M' : Type w₂} {S : Type w₁} {S' : Type w₃}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']
variable [AddCommGroup S] [Module R S] [LieRingModule L S]
variable [AddCommGroup S'] [Module R S'] [LieRingModule L S']

/-- **The multiplicity only depends on the equivalence class of the ambient module.**
Postcomposition with an equivalence identifies the two morphism spaces. -/
theorem isotypicMultiplicity_eq_of_lieModuleEquiv_right (e : M ≃ₗ⁅R,L⁆ M') :
    isotypicMultiplicity R L M S = isotypicMultiplicity R L M' S :=
  (TauCeti.LieModuleEquiv.congrRight (M := S) e).finrank_eq

/-- **The multiplicity only depends on the equivalence class of the module being counted.**
Precomposition with an equivalence identifies the two morphism spaces. This is what lets the
multiplicity be read for an irreducible determined only up to equivalence, such as an irreducible
highest-weight quotient. -/
theorem isotypicMultiplicity_eq_of_lieModuleEquiv_left (e : S ≃ₗ⁅R,L⁆ S') :
    isotypicMultiplicity R L M S = isotypicMultiplicity R L M S' :=
  (TauCeti.LieModuleEquiv.congrLeft (P := M) e).finrank_eq

end Invariance

/-! ### The multiplicity as a count of summands -/

section Multiplicity

variable {K : Type u} {L : Type v} {M : Type w} {S : Type w₁}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S]

/-- **An irreducible module occurs in itself with multiplicity one.** -/
@[simp]
theorem isotypicMultiplicity_self [IsAlgClosed K] [FiniteDimensional K S] [IsIrreducible K L S] :
    isotypicMultiplicity K L S S = 1 :=
  TauCeti.LieModule.finrank_lieModuleHom_self K L S

variable [FiniteDimensional K M] [IsAlgClosed K]
variable [FiniteDimensional K S] [IsIrreducible K L S]

section Count

variable {ι : Type w₂} [DecidableEq ι] [Finite ι]
variable (N : ι → LieSubmodule K L M) (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
variable (hirr : ∀ i, IsIrreducible K L (N i))

include h hirr

open scoped Classical in
/-- **The multiplicity counts the summands equivalent to `S`.** For a decomposition of a
finite-dimensional module into irreducible Lie submodules over an algebraically closed field, the
multiplicity of a finite-dimensional irreducible `S` is the number of indices whose summand is
equivalent to `S`: Schur's lemma makes each such summand contribute `1` to the morphism space and
every other summand contribute `0`. -/
theorem isotypicMultiplicity_eq_ncard_of_isInternal :
    isotypicMultiplicity K L M S = {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}.ncard := by
  have _i : Fintype ι := Fintype.ofFinite ι
  rw [isotypicMultiplicity_def,
    TauCeti.LieModule.finrank_lieModuleHom_eq_sum_of_isInternal S N h]
  have hsum : ∀ i : ι,
      finrank K (S →ₗ⁅K,L⁆ N i) = if Nonempty (S ≃ₗ⁅K,L⁆ N i) then 1 else 0 := fun i ↦
    have := hirr i
    TauCeti.LieModule.finrank_lieModuleHom K L
  rw [Finset.sum_congr rfl fun i _ ↦ hsum i, Finset.sum_boole,
    Set.ncard_eq_toFinset_card' {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}]
  simp

end Count

/-- **The number of summands equivalent to a given irreducible does not depend on the
decomposition.** Both counts compute the same multiplicity, which is defined without reference to
any decomposition. -/
theorem ncard_setOf_nonempty_lieModuleEquiv_eq
    {ι : Type w₂} [DecidableEq ι] [Finite ι] {ι' : Type w₃} [DecidableEq ι'] [Finite ι']
    (N : ι → LieSubmodule K L M) (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
    (hirr : ∀ i, IsIrreducible K L (N i))
    (N' : ι' → LieSubmodule K L M) (h' : DirectSum.IsInternal fun j ↦ (N' j).toSubmodule)
    (hirr' : ∀ j, IsIrreducible K L (N' j)) :
    {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}.ncard = {j | Nonempty (S ≃ₗ⁅K,L⁆ N' j)}.ncard := by
  rw [← isotypicMultiplicity_eq_ncard_of_isInternal N h hirr,
    isotypicMultiplicity_eq_ncard_of_isInternal N' h' hirr']

end Multiplicity

end LieModule
