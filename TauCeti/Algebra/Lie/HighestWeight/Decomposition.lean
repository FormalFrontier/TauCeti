/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.Multiplicity
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
import TauCeti.Algebra.Lie.HighestWeight.Irreducible
import TauCeti.Algebra.Lie.Submodule.Decomposition

public section

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

## Main results

* `TauCeti.natCard_eq_isotypicMultiplicity_irreducibleQuotient`: **the summands of a decomposition
  labelled by a dominant integral `λ` are counted by the multiplicity of `L(λ)`.**
* `TauCeti.nonempty_lieModuleEquiv_directSum_irreducibleQuotient`: **the packaged isotypic
  decomposition** `M ≃ ⨁_λ L(λ)^{m λ}`.

## References

This is the packaged-decomposition item of the milestone "isotypic components and multiplicities,
through the enveloping-algebra dictionary" in the Layer 6 decomposition toolkit of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.3 (complete
  reducibility) and §§20.3, 21.2 (the classification of the finite-dimensional irreducible
  modules).
-/

namespace TauCeti

open LieAlgebra Module

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

end TauCeti
