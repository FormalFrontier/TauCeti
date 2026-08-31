/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Schur
public import TauCeti.Algebra.Lie.Submodule.DirectSum

public section

/-!
# The multiplicity of an irreducible Lie module

`LieModule.isotypicMultiplicity R L M S` is the finrank of the space `S →ₗ⁅R,L⁆ M` of morphisms
from a Lie module `S` to a Lie module `M`. This file proves that when `S` is finite-dimensional and
irreducible over an algebraically closed field, this number counts
the summands equivalent to `S` in any *finite* decomposition of `M` into irreducible Lie
submodules, and is therefore independent of which such decomposition is chosen: it is the
**multiplicity** of `S` in `M`.

## The argument

The morphism space is **additive over a direct sum in its target**: a morphism `S →ₗ⁅R,L⁆ ⨁ i, Pᵢ`
is the same thing as a family of morphisms `S →ₗ⁅R,L⁆ Pᵢ`, one for each `i`, which is
`TauCeti.LieModule.lieModuleHomDirectSumEquiv` of `TauCeti/Algebra/Lie/DirectSum.lean`.
Transporting along `DirectSum.lieModuleEquivOfIsInternal` of
`TauCeti/Algebra/Lie/Submodule/DirectSum.lean` turns that into additivity over an *internal*
decomposition of `M` by Lie submodules.

The per-summand contribution is Schur's lemma in the dimension form of
`TauCeti/Algebra/Lie/Schur.lean`: for irreducible `S` and `Nᵢ` over an algebraically closed field,
`dim_K (S →ₗ⁅K,L⁆ Nᵢ)` is `1` when `Nᵢ ≃ S` and `0` otherwise. Summing over the finite index type
gives the count. Since the left-hand side never mentions the decomposition, two finite
decompositions of the same module have the same number of summands equivalent to `S`; this is the
uniqueness statement that makes "the multiplicity of `S` in `M`" well defined.

Nothing here needs complete reducibility: the counting theorem is stated for a finite decomposition
it is handed. Complete reducibility is what *produces* such a decomposition, through
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

* `LieModule.isotypicMultiplicity`: the finrank of `S →ₗ⁅R,L⁆ M`, which the theorems below
  identify with the multiplicity under their field, irreducibility, and decomposition hypotheses.

## Main results

* `LieModule.isotypicMultiplicity_eq_sum_of_isInternal`: **the multiplicity is additive over a
  finite decomposition of `M` into Lie submodules.**
* `LieModule.isotypicMultiplicity_self`: an irreducible module occurs in itself with multiplicity
  one.
* `LieModule.isotypicMultiplicity_eq_of_lieModuleEquiv` and
  `LieModule.isotypicMultiplicity_eq_of_lieModuleEquiv_type`: the multiplicity depends only on the
  equivalence classes of `M` and of `S`.
* `LieModule.isotypicMultiplicity_eq_ncard_of_isInternal`: **the multiplicity counts the summands
  equivalent to `S`** in a finite decomposition of `M` into irreducibles.
* `LieModule.ncard_setOf_nonempty_lieModuleEquiv_eq`: **the count is independent of which finite
  decomposition is taken.**

## Roadmap

This is the `isotypicMultiplicity` target of the decomposition toolkit in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, together with the additivity of
the morphism space over a direct-sum decomposition that `TauCeti/Algebra/Lie/Schur.lean` names as
the missing ingredient of the multiplicity theorem. The multiplicity is stated for an arbitrary
irreducible `S` rather than for the irreducible quotient `L(λ)`, which the roadmap's own signature
uses; the `L(λ)`-indexed form is this statement with `S` instantiated. The finrank of the isotypic
component, `dim (LieModule.isotypicComponent S M) = isotypicMultiplicity · dim S`, is the next item
of that milestone, "Isotypic components and multiplicities, through the enveloping-algebra
dictionary"; it is proved through the dictionary, as
`LieModule.finrank_isotypicComponent` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Multiplicity.lean`. One item of the milestone still
remains, the packaged decomposition `M ≃ ⨁ S^{⊕ m}` as an equivalence of Lie modules. The toolkit's
other two milestones, the copy of `L(λ)` generated by
a highest weight vector with its single-weight isotypy criterion, and the tensor multiplicities
with the minuscule Pieri rule, are untouched here.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.
-/

universe u v w w₁ w₂ w₃

namespace LieModule

open Module (finrank)

/-! ### The multiplicity of an irreducible module -/

section Def

variable (R : Type u) (L : Type v) (M : Type w) (S : Type w₁)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup S] [Module R S] [LieRingModule L S]

/-- **The finrank of the space of morphisms `S →ₗ⁅R,L⁆ M`.** For an irreducible,
finite-dimensional `S` over an algebraically closed field this is the multiplicity of `S` in `M`:
the number of summands equivalent to `S` in any finite decomposition of `M` into
irreducibles (`LieModule.isotypicMultiplicity_eq_ncard_of_isInternal`), and stating it as the
finrank of a morphism space is what makes it manifestly independent of the decomposition. In the
generality of the definition it is not itself a multiplicity: for a finite-dimensional irreducible
`S` over a field and a finite irreducible direct-sum decomposition of `M`, it is the multiplicity
times `dim End_L(S)`, a factor that Schur's lemma makes `1` over an algebraically closed field. -/
noncomputable def isotypicMultiplicity : ℕ :=
  finrank R (S →ₗ⁅R,L⁆ M)

/-- The multiplicity is the finrank of the morphism space. The definition is not exposed, so
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
theorem isotypicMultiplicity_eq_of_lieModuleEquiv (e : M ≃ₗ⁅R,L⁆ M') :
    isotypicMultiplicity R L M S = isotypicMultiplicity R L M' S :=
  (TauCeti.LieModuleEquiv.congrRight (M := S) e).finrank_eq

/-- **The multiplicity only depends on the equivalence class of the module being counted.**
Precomposition with an equivalence identifies the two morphism spaces. This is what lets the
multiplicity be read for an irreducible determined only up to equivalence, such as an irreducible
highest-weight quotient. -/
theorem isotypicMultiplicity_eq_of_lieModuleEquiv_type (e : S ≃ₗ⁅R,L⁆ S') :
    isotypicMultiplicity R L M S = isotypicMultiplicity R L M S' :=
  (TauCeti.LieModuleEquiv.congrLeft (P := M) e).finrank_eq

end Invariance

/-! ### The multiplicity as a count of summands -/

section Multiplicity

variable {K : Type u} {L : Type v} {M : Type w} {S : Type w₁}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S]

section Additivity

variable {ι : Type w₂} [DecidableEq ι] [Fintype ι]

omit [LieModule K L S] in
/-- **Multiplicity is additive over an internal decomposition of its ambient module.** -/
theorem isotypicMultiplicity_eq_sum_of_isInternal (N : ι → LieSubmodule K L M)
    (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
    (hfin : ∀ i, FiniteDimensional K (S →ₗ⁅K,L⁆ N i)) :
    isotypicMultiplicity K L M S = ∑ i, isotypicMultiplicity K L (N i) S := by
  rw [isotypicMultiplicity_def,
    TauCeti.LieModule.finrank_lieModuleHom_eq_sum_of_isInternal S N h hfin]
  simp_rw [isotypicMultiplicity_def]

end Additivity

/-- **An irreducible module occurs in itself with multiplicity one.** -/
@[simp]
theorem isotypicMultiplicity_self [IsAlgClosed K] [FiniteDimensional K S] [IsIrreducible K L S] :
    isotypicMultiplicity K L S S = 1 :=
  TauCeti.LieModule.finrank_lieModuleHom_self K L S

variable [IsAlgClosed K]
variable [FiniteDimensional K S] [IsIrreducible K L S]

section Count

variable {ι : Type w₂} [DecidableEq ι] [Finite ι]
variable (N : ι → LieSubmodule K L M) (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
variable (hirr : ∀ i, IsIrreducible K L (N i))

include h hirr

open scoped Classical in
/-- **The multiplicity counts the summands equivalent to `S`.** For a finite decomposition of a
module into irreducible Lie submodules over an algebraically closed field, the
multiplicity of a finite-dimensional irreducible `S` is the number of indices whose summand is
equivalent to `S`: Schur's lemma makes each such summand contribute `1` to the morphism space and
every other summand contribute `0`. -/
theorem isotypicMultiplicity_eq_ncard_of_isInternal :
    isotypicMultiplicity K L M S = {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}.ncard := by
  have _i : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ i, FiniteDimensional K (S →ₗ⁅K,L⁆ N i) := fun i ↦
    have := hirr i
    TauCeti.LieModule.finiteDimensional_lieModuleHom_of_isIrreducible K L
  rw [isotypicMultiplicity_def,
    TauCeti.LieModule.finrank_lieModuleHom_eq_sum_of_isInternal S N h hfin]
  have hsum : ∀ i : ι,
      finrank K (S →ₗ⁅K,L⁆ N i) = if Nonempty (S ≃ₗ⁅K,L⁆ N i) then 1 else 0 := fun i ↦
    have := hirr i
    TauCeti.LieModule.finrank_lieModuleHom K L
  rw [Finset.sum_congr rfl fun i _ ↦ hsum i, Finset.sum_boole,
    Set.ncard_eq_toFinset_card' {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)}]
  simp

end Count

/-- **The number of summands equivalent to a given irreducible does not depend on which finite
decomposition is taken.** Both counts compute the same multiplicity, which is defined without
reference to any decomposition. -/
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
