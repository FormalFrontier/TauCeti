/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
public import TauCeti.Algebra.Lie.Multiplicity
public import TauCeti.Algebra.Lie.Weights.FormalCharacter
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import TauCeti.Algebra.Lie.HighestWeight.Irreducible
import TauCeti.Algebra.Lie.Submodule.Decomposition

/-!
# The packaged isotypic decomposition `M ≅ ⨁ L(λ)^{m λ}`

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a Cartan subalgebra and `b` a base of its root
system. Weyl's theorem decomposes a finite-dimensional `L`-module `M` into irreducible Lie
submodules, and `LieModule.isotypicMultiplicity` counts how many of them lie in a given
isomorphism class, independently of the decomposition. This file assembles the two into the single
statement a consumer wants:

`M ≃ₗ⁅K,L⁆ ⨁ (λ, k), L(λ)`,

the sum being over pairs of a dominant integral weight `λ` and a counter `k` in
`Fin (m λ)`, where `m λ` is the multiplicity of `L(λ)` in `M`
(`TauCeti.nonempty_lieModuleEquiv_directSum_irreducibleQuotient`). Only finitely many
multiplicities are nonzero, so all but finitely many summands are indexed by the empty type.

The companion statement `LieModule.nonempty_lieModuleEquiv_isotypicComponent` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Multiplicity.lean` decomposes one isotypic component as a
power `S^{⊕ m}` of a single irreducible. It is not what proves the theorem below, since nothing
so far exhibits `M` as the direct sum of its isotypic components; the decomposition into
irreducibles is regrouped directly instead.

## The argument

Each irreducible summand `N i` of a decomposition of `M` carries a highest weight vector of a
dominant integral weight `c i`, and two irreducible modules with highest weight vectors of the same
weight are equivalent, so `N i ≃ L(c i)`
(`TauCeti.exists_isDominantIntegral_nonempty_lieModuleEquiv_irreducibleQuotient`). Regrouping the
decomposition by the label `c` is `DirectSum.nonempty_lieModuleEquiv_sigma_of_isInternal`, and what
it asks for is that the fibre of `c` over `λ` have exactly `m λ` elements. That is
`TauCeti.natCard_eq_isotypicMultiplicity_irreducibleQuotient`, and it splits in two.

For a weight `λ` whose Verma module is nonzero, `L(λ)` is irreducible, and finite-dimensional
because `λ` is dominant integral, so `LieModule.isotypicMultiplicity_eq_ncard_of_isInternal`
counts the summands equivalent to it; those are exactly the summands labelled `λ`, by the
classification of the irreducible highest weight modules.

For a weight `λ` whose Verma module vanishes, `L(λ)` is the zero module
(`TauCeti.subsingleton_irreducibleQuotient_iff`). Both sides are then `0`: the multiplicity of the
zero module is zero, and no summand can be labelled `λ`, an irreducible summand being nonzero.
This case is not vacuous bookkeeping: whether `M(λ) ≠ 0` for every dominant integral `λ`
is exactly the Poincaré--Birkhoff--Witt input that
`TauCeti/Algebra/Lie/HighestWeight/Verma.lean` does not have, and the decomposition below is
stated so as not to need it.

## The decomposition read on characters

Formal characters are additive over an internal decomposition
(`TauCeti.formalCharacter_eq_sum_of_isInternal`), so the same regrouping turns the decomposition
into the character identity `ch M = ∑_λ m_λ · ch L(λ)`, the form in which "decompose `M` into
irreducibles" becomes a computation. The formal character is defined only for a
finite-dimensional module, and `L(λ)` is finite-dimensional at every dominant integral `λ`
(`TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral`); at a non-dominant `λ` it
is infinite-dimensional as soon as `M(λ) ≠ 0`, that being what gives it a highest weight vector
(`TauCeti.finiteDimensional_iff_isDominantIntegral_of_isHighestWeightVector`), and otherwise it is
the zero module, which is finite-dimensional but occurs in nothing. So the sum does not
run over all of `Module.Dual K H`: `TauCeti.irreducibleFormalCharacter` names the character of
`L(λ)` as a function of a weight *bundled with its dominance*, and the sum runs over that subtype.
`TauCeti.irreducibleFormalCharacter_def` unfolds it wherever the finite-dimensionality instance is
already at hand, so the definition itself never needs unfolding.

The missing Poincaré--Birkhoff--Witt input does not make that character an unknown quantity.
`TauCeti.irreducibleFormalCharacter_eq_zero_iff` says it vanishes exactly when `M(λ)` does, so a
weight contributing to a character identity has an irreducible `L(λ)`
(`TauCeti.isIrreducible_irreducibleQuotient_of_irreducibleFormalCharacter_ne_zero`) and a weight
not contributing has the zero module, with the zero multiplicity that a decomposition into
irreducibles gives it. At `λ = 0` the input is available outright, so
`TauCeti.irreducibleFormalCharacter_zero_ne_zero` is unconditional and the character API is not
vacuous.

Restricting the sum to the dominant integral weights loses nothing:
`TauCeti.isotypicMultiplicity_irreducibleQuotient_eq_zero_of_not_isDominantIntegral` says that
`L(λ)` for a non-dominant `λ` has multiplicity zero in every finite-dimensional module, so every
multiplicity the sum omits is zero.

## Main definitions

* `TauCeti.irreducibleFormalCharacter`: the formal character of `L(λ)`, at a dominant integral `λ`.

## Main results

* `TauCeti.natCard_eq_isotypicMultiplicity_irreducibleQuotient`: **the summands of a decomposition
  labelled by a dominant integral `λ` are counted by the multiplicity of `L(λ)`.**
* `TauCeti.nonempty_lieModuleEquiv_directSum_irreducibleQuotient`: **the packaged isotypic
  decomposition** `M ≃ ⨁_λ L(λ)^{m λ}`.
* `TauCeti.isotypicMultiplicity_irreducibleQuotient_eq_zero_of_not_isDominantIntegral`: `L(λ)` of
  a non-dominant weight `λ` has multiplicity zero in every finite-dimensional module.
* `TauCeti.irreducibleFormalCharacter_eq_zero_iff` and
  `TauCeti.isIrreducible_irreducibleQuotient_of_irreducibleFormalCharacter_ne_zero`: the character
  of `L(lam)` vanishes exactly when `M(lam)` does, so **a nonzero character is the character of an
  irreducible module.**
* `TauCeti.irreducibleFormalCharacter_zero_ne_zero`: **the character of `L(0)` is nonzero**, with
  no appeal to Poincaré--Birkhoff--Witt.
* `TauCeti.formalCharacter_eq_finsum_isotypicMultiplicity_smul`: **the character of a
  finite-dimensional module is the multiplicity-weighted sum of the irreducible characters.**

## References

This is the packaged-decomposition item of the milestone "isotypic components and multiplicities,
through the enveloping-algebra dictionary" in the Layer 6 decomposition toolkit of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.3 (complete
  reducibility) and §§20.3, 21.2 (the classification of the finite-dimensional irreducible
  modules).
-/

public section

namespace TauCeti

-- `TauCeti.LieModule` exists in the imports, so the root namespace is named explicitly.
open LieAlgebra _root_.LieModule Module

open scoped DirectSum

universe u v w w₁

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

variable (b : (IsKilling.rootSystem H).Base)

/-! ### The multiplicity counts the summands with a given label -/

section Count

variable {ι : Type w₁} [Finite ι] [DecidableEq ι]
  (N : ι → LieSubmodule K L M) (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
  (hirr : ∀ i, LieModule.IsIrreducible K L (N i)) (c : ι → Dual K H)
  (hc : ∀ i, Nonempty ((N i : Type w) ≃ₗ⁅K,L⁆ irreducibleQuotient b (c i)))

include h hirr hc

/-- **The multiplicity of `L(lam)` counts the summands labelled `lam`.** For a finite
decomposition of `M` into irreducible Lie submodules, each labelled by a weight whose `L` it is a
copy of, and for a dominant integral weight `lam`, the number of indices carrying the label `lam`
is the multiplicity of `L(lam)` in `M`. -/
theorem natCard_eq_isotypicMultiplicity_irreducibleQuotient {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) :
    Nat.card {i // c i = lam}
      = LieModule.isotypicMultiplicity K L M (irreducibleQuotient b lam) := by
  -- Each summand is nonzero, so the Verma module of the weight labelling it is nonzero too.
  have hnontrivial : ∀ i, Nontrivial (irreducibleQuotient b (c i)) := fun i ↦
    have _ := hirr i
    have _ : Nontrivial (N i : Type w) :=
      LieModule.nontrivial_of_isIrreducible (R := K) (L := L) (M := (N i : Type w))
    (hc i).some.symm.toEquiv.nontrivial
  have hcne : ∀ i, vermaGenerator b (c i) ≠ 0 := fun i h0 ↦
    have _ := hnontrivial i
    not_subsingleton _ ((subsingleton_irreducibleQuotient_iff b (c i)).mpr h0)
  by_cases hne : vermaGenerator b lam = 0
  · -- `L(lam)` is the zero module: no summand is labelled `lam`, and its multiplicity vanishes.
    have _ := (subsingleton_irreducibleQuotient_iff b lam).mpr hne
    have _ : IsEmpty {i // c i = lam} := ⟨fun i ↦ hcne i.1 (by rw [i.2]; exact hne)⟩
    rw [Nat.card_of_isEmpty, LieModule.isotypicMultiplicity_eq_zero_of_subsingleton]
  · -- `L(lam)` is an irreducible, finite-dimensional module, so the counting theorem applies.
    have _ := isIrreducible_irreducibleQuotient b lam hne
    have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
    have hset : {i | Nonempty (irreducibleQuotient b lam ≃ₗ⁅K,L⁆ (N i : Type w))}
        = {i | c i = lam} := by
      ext i
      have _ := isIrreducible_irreducibleQuotient b (c i) (hcne i)
      constructor
      · rintro ⟨e⟩
        exact ((nonempty_lieModuleEquiv_iff_eq_of_isHighestWeightVector
          (isHighestWeightVector_irreducibleQuotientGenerator b lam hne)
          (isHighestWeightVector_irreducibleQuotientGenerator b (c i) (hcne i))).mp
            ⟨e.trans (hc i).some⟩).symm
      · exact fun hi ↦ ⟨(hi ▸ (hc i).some).symm⟩
    rw [LieModule.isotypicMultiplicity_eq_ncard_of_isInternal N h hirr, hset]
    -- `Set.ncard` is `Nat.card` of the coercion, and `↥{i | c i = lam}` is `{i // c i = lam}`.
    exact Nat.card_coe_set_eq _

end Count

/-! ### The packaged decomposition -/

/-- **The packaged isotypic decomposition.** A finite-dimensional module over a
Killing-semisimple Lie algebra in characteristic zero over an algebraically closed field is the
direct sum of the modules `L(lam)`, indexed by a dominant integral weight `lam` together with a
counter running over the multiplicity of `L(lam)` in the module.

Only finitely many multiplicities are nonzero, so all but finitely many of the summands are
indexed by `Fin 0`. -/
theorem nonempty_lieModuleEquiv_directSum_irreducibleQuotient [FiniteDimensional K M] :
    Nonempty (M ≃ₗ⁅K,L⁆
      ⨁ q : (Σ lam : {l : Dual K H // IsDominantIntegral b l},
          Fin (LieModule.isotypicMultiplicity K L M (irreducibleQuotient b lam.1))),
        irreducibleQuotient b q.1.1) := by
  classical
  have _ := complementedLattice_lieSubmodule_of_isKilling K L M
  obtain ⟨k, N, hint, hirr⟩ := exists_isInternal_isIrreducible K L M
  choose c hcdom hcequiv using fun i ↦
    have _ := hirr i
    exists_isDominantIntegral_nonempty_lieModuleEquiv_irreducibleQuotient
      (M := (N i : Type w)) b
  refine DirectSum.nonempty_lieModuleEquiv_sigma_of_isInternal
    (S := fun s : {l : Dual K H // IsDominantIntegral b l} ↦ irreducibleQuotient b s.1)
    (m := fun s ↦ LieModule.isotypicMultiplicity K L M (irreducibleQuotient b s.1))
    N hint (fun i ↦ ⟨c i, hcdom i⟩) hcequiv fun s ↦ ?_
  have hiff : ∀ i, ((⟨c i, hcdom i⟩ : {l : Dual K H // IsDominantIntegral b l}) = s)
      ↔ c i = (s : Dual K H) := fun _ ↦ Subtype.ext_iff
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact natCard_eq_isotypicMultiplicity_irreducibleQuotient b N hint hirr c hcequiv s.2

/-! ### The character of the irreducible module of a dominant integral weight -/

/-- **The formal character of the highest weight module `L(lam)`** of a dominant integral weight
`lam`, which `TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral` makes
finite-dimensional. The weight is bundled with its dominance so that the character is a function of
a single argument, and can therefore index a sum.

`L(lam)` is irreducible exactly where it is nonzero, which is exactly where this character is
nonzero (`TauCeti.irreducibleFormalCharacter_eq_zero_iff` and
`TauCeti.isIrreducible_irreducibleQuotient_of_irreducibleFormalCharacter_ne_zero`); at a `lam`
whose Verma module vanishes this is the character `0` of the zero module. -/
noncomputable def irreducibleFormalCharacter
    (lam : {l : Dual K H // IsDominantIntegral b l}) : AddMonoidAlgebra ℤ (Dual K H) :=
  haveI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral lam.2
  formalCharacter K H (irreducibleQuotient b lam.1)

-- This private reduction is required by Lean's module system: an exported theorem cannot unfold
-- the opaque exported definition directly while checking its public signature.
private theorem irreducibleFormalCharacter_def_aux
    (lam : {l : Dual K H // IsDominantIntegral b l})
    [FiniteDimensional K (irreducibleQuotient b lam.1)] :
    irreducibleFormalCharacter b lam = formalCharacter K H (irreducibleQuotient b lam.1) := rfl

/-- **The character of `L(lam)` is the formal character of `L(lam)`.** With the
finite-dimensionality instance in hand, `TauCeti.irreducibleFormalCharacter` needs no unfolding. -/
@[simp]
theorem irreducibleFormalCharacter_def
    (lam : {l : Dual K H // IsDominantIntegral b l})
    [FiniteDimensional K (irreducibleQuotient b lam.1)] :
    irreducibleFormalCharacter b lam = formalCharacter K H (irreducibleQuotient b lam.1) :=
  irreducibleFormalCharacter_def_aux b lam

/-- **The character of `L(lam)` vanishes exactly when `M(lam)` does.** The character records the
dimension of `L(lam)`, and `L(lam)` is the zero module exactly when `M(lam)` is
(`TauCeti.subsingleton_irreducibleQuotient_iff`). -/
@[simp]
theorem irreducibleFormalCharacter_eq_zero_iff
    (lam : {l : Dual K H // IsDominantIntegral b l}) :
    irreducibleFormalCharacter b lam = 0 ↔ vermaGenerator b lam.1 = 0 := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral lam.2
  rw [irreducibleFormalCharacter_def, formalCharacter_eq_zero_iff, Module.finrank_zero_iff,
    subsingleton_irreducibleQuotient_iff]

/-- **A nonzero character is the character of an honest irreducible module.** The character being
nonzero says exactly that `M(lam) ≠ 0`, which is what
`TauCeti.isIrreducible_irreducibleQuotient` asks for; so wherever
`TauCeti.irreducibleFormalCharacter` contributes to an identity, the module it is the character of
is irreducible. -/
theorem isIrreducible_irreducibleQuotient_of_irreducibleFormalCharacter_ne_zero
    {lam : {l : Dual K H // IsDominantIntegral b l}}
    (h : irreducibleFormalCharacter b lam ≠ 0) :
    LieModule.IsIrreducible K L (irreducibleQuotient b lam.1) :=
  isIrreducible_irreducibleQuotient b lam.1 fun h0 ↦
    h ((irreducibleFormalCharacter_eq_zero_iff b lam).mpr h0)

/-- **The character of `L(0)` is nonzero, unconditionally.** The trivial one-dimensional module is
a highest weight module of weight `0`, so `M(0) ≠ 0` with no appeal to
Poincaré--Birkhoff--Witt (`TauCeti.isHighestWeightVector_vermaGenerator_zero`). With
`TauCeti.isIrreducible_irreducibleQuotient_of_irreducibleFormalCharacter_ne_zero` this exhibits a
weight at which `L(lam)` is an honest irreducible with a nonzero character, so no statement about
`TauCeti.irreducibleFormalCharacter` is vacuous. -/
theorem irreducibleFormalCharacter_zero_ne_zero :
    irreducibleFormalCharacter b ⟨0, isDominantIntegral_zero⟩ ≠ 0 := fun h ↦
  (isHighestWeightVector_vermaGenerator_zero b).ne_zero
    ((irreducibleFormalCharacter_eq_zero_iff b _).mp h)

/-! ### The multiplicity-weighted sum of irreducible characters -/

variable {b}

/-- **`L(lam)` of a non-dominant weight has multiplicity zero in every finite-dimensional
module.** A nonzero multiplicity gives a nonzero morphism out of `L(lam)`, which in particular
makes `L(lam)` nonzero, hence irreducible (`TauCeti.isIrreducible_irreducibleQuotient`); that
morphism is then injective, so it would make `L(lam)` finite-dimensional, hence `lam` dominant
integral. -/
theorem isotypicMultiplicity_irreducibleQuotient_eq_zero_of_not_isDominantIntegral
    [FiniteDimensional K M] {lam : Dual K H} (hlam : ¬ IsDominantIntegral b lam) :
    LieModule.isotypicMultiplicity K L M (irreducibleQuotient b lam) = 0 := by
  by_contra hne
  -- a nonzero multiplicity produces a nonzero morphism out of `L(lam)`
  have hsub : ¬ Subsingleton (irreducibleQuotient b lam →ₗ⁅K,L⁆ M) := by
    intro hsub
    refine hne ?_
    rw [LieModule.isotypicMultiplicity_def]
    have := hsub
    exact finrank_zero_of_subsingleton
  obtain ⟨f, hf⟩ : ∃ f : irreducibleQuotient b lam →ₗ⁅K,L⁆ M, f ≠ 0 := by
    rw [not_subsingleton_iff_nontrivial] at hsub
    exact exists_ne 0
  -- so `L(lam)` is nonzero, hence irreducible
  have h0 : vermaGenerator b lam ≠ 0 := fun h0 ↦ by
    have := (subsingleton_irreducibleQuotient_iff b lam).mpr h0
    exact hf (LieModuleHom.ext fun x ↦ by rw [Subsingleton.elim x 0]; simp)
  have := isIrreducible_irreducibleQuotient b lam h0
  -- and the morphism is injective, so `L(lam)` is finite-dimensional and `lam` is dominant
  have hker : f.ker = ⊥ := by
    refine (IsSimpleOrder.eq_bot_or_eq_top f.ker).resolve_right fun htop ↦ hf ?_
    refine LieModuleHom.ext fun x ↦ ?_
    simpa using (htop ▸ LieSubmodule.mem_top x : x ∈ f.ker)
  have : FiniteDimensional K (irreducibleQuotient b lam) :=
    Module.Finite.of_injective (f : irreducibleQuotient b lam →ₗ[K] M)
      ((LieModuleHom.ker_eq_bot f).mp hker)
  exact hlam ((finiteDimensional_iff_isDominantIntegral_of_isHighestWeightVector
    (isHighestWeightVector_irreducibleQuotientGenerator b lam h0)).mp inferInstance)

variable (b) in
/-- **The character of a finite-dimensional module is the multiplicity-weighted sum of the
irreducible characters.** A decomposition into irreducibles labels each summand by the dominant
integral weight whose `L(lam)` it is a copy of; characters are additive over the decomposition, and
the summands carrying a given label are counted by the multiplicity of `L(lam)`
(`TauCeti.natCard_eq_isotypicMultiplicity_irreducibleQuotient`). -/
theorem formalCharacter_eq_finsum_isotypicMultiplicity_smul [FiniteDimensional K M] :
    formalCharacter K H M
      = ∑ᶠ lam : {l : Dual K H // IsDominantIntegral b l},
          (LieModule.isotypicMultiplicity K L M (irreducibleQuotient b lam.1) : ℤ) •
            irreducibleFormalCharacter b lam := by
  classical
  have := complementedLattice_lieSubmodule_of_isKilling K L M
  obtain ⟨k, N, hint, hirr⟩ := exists_isInternal_isIrreducible K L M
  choose c hcdom hcequiv using fun i ↦
    have := hirr i
    exists_isDominantIntegral_nonempty_lieModuleEquiv_irreducibleQuotient
      (M := (N i : Type w)) b
  -- the labelling of the summands by dominant integral weights
  set d : Fin k → {l : Dual K H // IsDominantIntegral b l} := fun i ↦ ⟨c i, hcdom i⟩ with hd
  have hcard : ∀ lam : {l : Dual K H // IsDominantIntegral b l},
      (Finset.univ.filter fun i ↦ d i = lam).card
        = LieModule.isotypicMultiplicity K L M (irreducibleQuotient b lam.1) := by
    intro lam
    rw [← natCard_eq_isotypicMultiplicity_irreducibleQuotient b N hint hirr c hcequiv lam.2,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext i
    simp [hd, Subtype.ext_iff]
  have hchar : ∀ i, formalCharacter K H (N i : Type w) = irreducibleFormalCharacter b (d i) := by
    intro i
    have := finiteDimensional_irreducibleQuotient_of_isDominantIntegral (hcdom i)
    rw [irreducibleFormalCharacter_def]
    exact formalCharacter_congr (LieModuleEquiv.restrictLie (hcequiv i).some H)
  -- the summands with a label outside the image of the labelling are absent, so the sum is finite
  have hsupp : (Function.support fun lam : {l : Dual K H // IsDominantIntegral b l} ↦
      (LieModule.isotypicMultiplicity K L M (irreducibleQuotient b lam.1) : ℤ) •
        irreducibleFormalCharacter b lam) ⊆ (Finset.univ.image d : Finset _) := by
    intro lam hlam
    by_contra hmem
    refine hlam ?_
    have : (Finset.univ.filter fun i ↦ d i = lam).card = 0 := by
      refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun i hi ↦ hmem ?_)
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
    simp only [← hcard lam, this, Nat.cast_zero, zero_smul]
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, formalCharacter_eq_sum_of_isInternal hint]
  simp only [hchar]
  rw [Finset.sum_comp (fun lam ↦ irreducibleFormalCharacter b lam) d]
  refine Finset.sum_congr rfl fun lam _ ↦ ?_
  rw [← Nat.cast_smul_eq_nsmul ℤ, hcard lam]

end TauCeti
