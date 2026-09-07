/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `Module.length` and `isotypicComponent` build the invariant defined below, and
-- `WedderburnPresentation` is what the invariance statement is about.
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.RingTheory.Semisimple.Wedderburn.Presentation
-- Non-public: used only inside proofs.  The endomorphism ring of a finite power of a module as a
-- matrix ring is what assembles the canonical presentation, Wedderburn--Artin supplies the
-- semisimplicity of endomorphism rings it rests on, and `TauCeti.wedderburn_blocks_unique` is what
-- compares an arbitrary presentation with it.
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import TauCeti.RingTheory.Semisimple.Wedderburn.Uniqueness

/-!
# The intrinsic data of a Wedderburn block

Artin--Wedderburn presents a semisimple ring `R` as a finite product of matrix rings over division
rings, `R ≃+* ∏ᵢ Matₙᵢ(Dᵢ)`, and `TauCeti.wedderburn_blocks_unique` says that two presentations
differ only by a permutation of the blocks.  That is uniqueness *between* presentations; it does
not say what the surviving data `nᵢ` and `Dᵢ` **are**.  This file answers that: each block is the
block of a simple `R`-module `S`, and then

* its coefficient division ring is the opposite endomorphism ring `(Module.End R S)ᵐᵒᵖ`, which is a
  division ring by Schur's lemma, and
* its matrix size is `TauCeti.blockMultiplicity R S`, the number of copies of `S` in the regular
  module.

Both are defined directly from the isomorphism class of `S`, with no presentation in sight, so
`TauCeti.WedderburnPresentation.exists_equiv_degree_eq_blockMultiplicity` turns "the degrees" and
"the division rings" of a semisimple ring into well-defined objects rather than artefacts of a
chosen decomposition.

## The multiplicity

The `S`-isotypic component of the regular module is `isotypicComponent R R S`, the sum of the left
ideals isomorphic to `S`; over a semisimple ring it is a finite direct sum of copies of `S`, and
`TauCeti.blockMultiplicity R S` is defined as its length, so it is manifestly an invariant of the
isomorphism class of `S` (`TauCeti.blockMultiplicity_eq_of_linearEquiv`).  Taking the length rather
than an exponent read off a chosen decomposition is what makes the definition choice-free;
`TauCeti.blockMultiplicity_eq_of_linearEquiv_fun` recovers the exponent from any decomposition.

## The canonical presentation

Mathlib's `IsSemisimpleRing.exists_ringEquiv_pi_matrix_end_mulOpposite` already presents `R` with
the intrinsic coefficient rings `(Module.End R (S i))ᵐᵒᵖ`, but its existential keeps no link
between a block and the simple module it belongs to, so the size of that block cannot be read off
it afterwards.  `TauCeti.exists_ringEquiv_pi_matrix_end_mulOpposite_blockMultiplicity` repeats that
construction over the isotypic components of the regular module and keeps the link, which is what
identifies each size with the corresponding block multiplicity and shows the simple modules
indexing the blocks to be pairwise non-isomorphic.

## Implementation notes

`blockMultiplicity` takes `ENat.toNat` of a length, so it reads `0` on a module whose isotypic
component has infinite length; over a semisimple ring, where the regular module has finite length,
that never happens and `TauCeti.blockMultiplicity_pos` records the positivity.

Multiplicities are measured here by a length, not by a hom-space dimension as in
`TauCeti/RingTheory/Semisimple/Multiplicity.lean`: that file computes the multiplicity of a simple
module in an arbitrary module of a finite-dimensional algebra over an algebraically closed field,
where Schur's lemma makes `finrank k (S →ₗ[A] M)` the count, while a Wedderburn block is indexed by
a simple module over a bare semisimple ring, with a division ring of endomorphisms that need not be
the base field.

## Main definitions

* `TauCeti.blockMultiplicity`: the multiplicity of a simple module in the regular module.

## Main results

* `TauCeti.blockMultiplicity_eq_of_linearEquiv_fun`: a decomposition of the isotypic component as a
  power of `S` has exactly `blockMultiplicity R S` factors.
* `TauCeti.exists_ringEquiv_pi_matrix_end_mulOpposite_blockMultiplicity`: **the canonical Wedderburn
  presentation**, whose blocks are indexed by pairwise non-isomorphic simple left ideals, with the
  size of a block the multiplicity of its module and its coefficient ring the opposite endomorphism
  ring.
* `TauCeti.WedderburnPresentation.exists_equiv_degree_eq_blockMultiplicity`: **the data of any
  Wedderburn presentation are the intrinsic data.**  After one permutation of its blocks, its
  degrees are the block multiplicities of pairwise non-isomorphic simple left ideals and its
  division rings are their opposite endomorphism rings, so its blocks match the isomorphism classes
  of simple modules one for one.

## References

This implements the Layer 2 targets "the canonical invariants" and "uniqueness / invariance" of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
The assembly of the canonical presentation follows Mathlib's
`IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end` and
`IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`.  See T. Y. Lam, *A First Course in
Noncommutative Rings*, GTM 131, §3, or C. W. Curtis and I. Reiner, *Representation Theory of Finite
Groups and Associative Algebras*, §25.
-/

public section

namespace TauCeti

universe u v w

/-! ### The multiplicity of a simple module in the regular module -/

section BlockMultiplicity

variable (R : Type u) [Ring R] (S : Type v) [AddCommGroup S] [Module R S]

/-- **The block multiplicity of a simple module `S`**: the number of copies of `S` in the regular
module of `R`, defined as the length of the `S`-isotypic component of `R`.

Over a semisimple ring the isotypic component is a finite direct sum of copies of `S`, so this is
the number of summands; taking the length instead makes the definition independent of a chosen
decomposition.  It is the size of the Wedderburn block of `S`. -/
noncomputable def blockMultiplicity : ℕ :=
  (Module.length R (isotypicComponent R R S)).toNat

variable {R S}

/-- **The block multiplicity depends only on the isomorphism class**, since isomorphic modules have
the same isotypic component. -/
theorem blockMultiplicity_eq_of_linearEquiv {S' : Type w} [AddCommGroup S'] [Module R S']
    (e : S ≃ₗ[R] S') : blockMultiplicity R S = blockMultiplicity R S' := by
  rw [blockMultiplicity, blockMultiplicity, LinearEquiv.isotypicComponent_eq (M := R) e]

/-- **A decomposition of the isotypic component of `S` as a power of `S` has exactly
`blockMultiplicity R S` factors**: the length of a finite power of a simple module is the exponent.

This is the characterisation that turns the length back into a count of summands. -/
theorem blockMultiplicity_eq_of_linearEquiv_fun [IsSimpleModule R S] {n : ℕ}
    (e : isotypicComponent R R S ≃ₗ[R] (Fin n → S)) : blockMultiplicity R S = n := by
  rw [blockMultiplicity, e.length_eq]
  simp

/-- **The block multiplicity of a simple module over a semisimple ring is positive**: the module is
isomorphic to a left ideal, whose own isotypic component is nonzero and of finite length. -/
theorem blockMultiplicity_pos [IsSemisimpleRing R] [IsSimpleModule R S] :
    0 < blockMultiplicity R S := by
  obtain ⟨I, ⟨f⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R S
  have : IsSimpleModule R I := .congr f.symm
  have hbot : ⊥ < isotypicComponent R R S := by
    rw [LinearEquiv.isotypicComponent_eq (M := R) f]
    exact bot_lt_isotypicComponent I
  have : Nontrivial (isotypicComponent R R S) := Submodule.nontrivial_iff_ne_bot.mpr hbot.ne'
  refine Nat.pos_of_ne_zero fun h ↦ ?_
  rw [blockMultiplicity, ENat.toNat_eq_zero] at h
  exact h.elim Module.length_pos.ne' Module.length_ne_top

end BlockMultiplicity

/-! ### The canonical Wedderburn presentation -/

variable (R : Type u) [Ring R] [IsSemisimpleRing R]

/-- **The canonical Wedderburn presentation of a semisimple ring.**  The blocks are indexed by
pairwise non-isomorphic simple left ideals `S i`; the coefficient ring of a block is the opposite
endomorphism ring `(Module.End R (S i))ᵐᵒᵖ`, a division ring by Schur's lemma, and its size is the
multiplicity of `S i` in the regular module.

Mathlib's `IsSemisimpleRing.exists_ringEquiv_pi_matrix_end_mulOpposite` produces the same shape but
forgets which block belongs to which simple module, so neither the identification of the sizes with
the multiplicities nor the non-isomorphy of the `S i` can be recovered from it; the construction is
repeated here over the isotypic components of the regular module, where both are visible. -/
theorem exists_ringEquiv_pi_matrix_end_mulOpposite_blockMultiplicity :
    ∃ (n : ℕ) (S : Fin n → Submodule R R) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i, NeZero (d i)) ∧
        (∀ i, d i = blockMultiplicity R (S i)) ∧ (∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) ∧
          Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End R (S i))ᵐᵒᵖ) := by
  classical
  -- Split the regular module into its isotypic components, and each component into copies of a
  -- simple left ideal contained in it.
  choose d pos S hle simple e using fun c : isotypicComponents R R ↦
    (IsIsotypic.isotypicComponents c.2).submodule_linearEquiv_fun
  have hcomp : ∀ c : isotypicComponents R R,
      (c : Submodule R R) = isotypicComponent R R (S c) := fun c ↦
    have := simple c; eq_isotypicComponent_of_le c.2 (hle c)
  have hmult : ∀ c : isotypicComponents R R, d c = blockMultiplicity R (S c) := fun c ↦
    have := simple c
    (blockMultiplicity_eq_of_linearEquiv_fun
      ((LinearEquiv.ofEq _ _ (hcomp c)).symm.trans (e c).some)).symm
  have hne : ∀ c c' : isotypicComponents R R, Nonempty (S c ≃ₗ[R] S c') → c = c' := by
    rintro c c' ⟨f⟩
    exact Subtype.ext
      ((hcomp c).trans ((LinearEquiv.isotypicComponent_eq (M := R) f).trans (hcomp c').symm))
  refine ⟨_, fun i ↦ S ((Finite.equivFin _).symm i), fun i ↦ d ((Finite.equivFin _).symm i),
    fun i ↦ simple _, fun i ↦ pos _, fun i ↦ hmult _,
    fun i j h ↦ (Finite.equivFin _).symm.injective (hne _ _ h), ⟨?_⟩⟩
  -- Assemble the presentation from the two splittings, as Mathlib does: the endomorphism ring of
  -- the regular module is the product of the endomorphism rings of the isotypic components, each
  -- of which is a matrix ring over the endomorphism ring of its simple module, and `R` is the
  -- opposite of the endomorphism ring of its regular module.
  exact (((AlgEquiv.opOp ℕ R).trans <| (AlgEquiv.op <| ((AlgEquiv.moduleEndSelf ℕ).trans <|
    (IsSemisimpleModule.endAlgEquiv ℕ R R).trans <| (AlgEquiv.piCongrRight fun c ↦
      ((e c).some.conjAlgEquiv ℕ).trans (endVecAlgEquivMatrixEnd ..)).trans
        (AlgEquiv.piCongrLeft' ℕ _ (Finite.equivFin _)))).trans <|
    (AlgEquiv.piMulOpposite _ _).trans
      (AlgEquiv.piCongrRight fun _ ↦ AlgEquiv.mopMatrix.symm)) :
    R ≃ₐ[ℕ] _).toRingEquiv

variable {R}

/-- **The data of a Wedderburn presentation are the intrinsic data of the ring.**  After one
permutation of its blocks, the degrees of a presentation are the block multiplicities of pairwise
non-isomorphic simple left ideals and its coefficient division rings are their opposite
endomorphism rings.

Together with `TauCeti.blockMultiplicity_eq_of_linearEquiv` this is what makes "the degrees" and
"the division rings" of a semisimple ring well defined: they are read off the isomorphism classes
of its simple modules, and any presentation exhibits exactly them. -/
theorem WedderburnPresentation.exists_equiv_degree_eq_blockMultiplicity
    (P : WedderburnPresentation.{u, w} R) :
    ∃ (n : ℕ) (S : Fin n → Submodule R R) (σ : Fin P.blockCount ≃ Fin n),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) ∧
        ∀ i, P.degree i = blockMultiplicity R (S (σ i)) ∧
          Nonempty (P.divisionRing i ≃+* (Module.End R (S (σ i)))ᵐᵒᵖ) := by
  classical
  obtain ⟨n, S, d, simple, pos, hmult, hne, ⟨g⟩⟩ :=
    exists_ringEquiv_pi_matrix_end_mulOpposite_blockMultiplicity R
  -- the simplicity of the canonical blocks and the positivity of their sizes are what make their
  -- coefficient rings division rings and their matrix blocks simple, so both are needed as
  -- instances by the comparison below
  have hsimple := simple
  have hdegree := pos
  obtain ⟨σ, hσ⟩ := wedderburn_blocks_unique P.equiv g
  exact ⟨n, S, σ, simple, hne, fun i ↦ ⟨(hσ i).1.trans (hmult _), (hσ i).2⟩⟩

end TauCeti
