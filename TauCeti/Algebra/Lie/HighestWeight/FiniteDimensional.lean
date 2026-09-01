/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Multiplicity
public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.HighestWeight.WeightSupport
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.HighestWeight.Existence
import TauCeti.Algebra.Lie.HighestWeight.Irreducible
import TauCeti.Algebra.Lie.Submodule.Atom

public section

/-!
# Finite-dimensionality of dominant irreducible highest weight modules

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero. An irreducible highest weight `L`-module is
finite-dimensional exactly when its highest weight is dominant integral.

The forward implication is the rank-one argument of
`TauCeti.IsHighestWeightVector.isDominantIntegral`. For the reverse implication, two earlier
milestones supply the necessary finiteness:

* `TauCeti.finite_setOf_genWeightSpace_ne_bot_of_isHighestWeightVector` says that a dominant
  irreducible highest weight module has only finitely many nonzero weight spaces;
* `TauCeti.finiteDimensional_genWeightSpace_of_isHighestWeightVector_of_lieSpan_eq_top` says that
  each of those weight spaces is finite-dimensional.

The weight-cone decomposition of a highest weight module says that these spaces span the whole
module. Their finite supremum is therefore finitely generated, which proves the result without
assuming finite-dimensionality of the ambient module at any intermediate step.

The criterion is then read at the named carrier `TauCeti.irreducibleQuotient b lam`, that is
`L(lam)`, in the two directions a consumer wants: **`L(lam)` is finite-dimensional whenever `lam`
is dominant integral**, with no side condition on the Verma module `M(lam)` because `L(lam)` is the
zero module when `M(lam)` vanishes; and conversely **every finite-dimensional irreducible module is
a copy of `L(lam)` for a dominant integral `lam`**, which is the classification of the
finite-dimensional irreducibles.

## Main results

* `TauCeti.finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral`: the difficult
  implication, from dominance to finite-dimensionality.
* `TauCeti.finiteDimensional_iff_isDominantIntegral_of_isHighestWeightVector`: the complete
  finite-dimensionality criterion for an irreducible highest weight module.
* `TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral`: **`L(lam)` is
  finite-dimensional at a dominant integral weight**, unconditionally.
* `TauCeti.exists_isDominantIntegral_nonempty_lieModuleEquiv_irreducibleQuotient`: **a
  finite-dimensional irreducible module is a copy of `L(lam)`** for a dominant integral `lam`.

## References

This closes the **finite-dimensionality** milestone of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`. It is the last assembly step in
the proof that the irreducible highest weight module `L(lam)` is finite-dimensional precisely for
dominant integral `lam`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.2.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L]
  [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [LieModule.IsIrreducible K L M]
  {b : (IsKilling.rootSystem H).Base} {lam : Dual K H} {v : M}

/-- **An irreducible highest weight module of dominant integral highest weight is
finite-dimensional.** Its nonzero weight spaces form a finite family, every member of that family
is finite-dimensional, and the family spans the module. -/
theorem finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam) :
    FiniteDimensional K M := by
  have hgen : LieSubmodule.lieSpan K L {v} = ⊤ :=
    lieSpan_singleton_eq_top_of_ne_zero hv.ne_zero
  have hfinite :
      {chi : H → K |
        (genWeightSpace M chi : LieSubmodule K H M).toSubmodule ≠ ⊥}.Finite := by
    convert finite_setOf_genWeightSpace_ne_bot_of_isHighestWeightVector hv hlam using 1
    ext chi
    simp
  let _ : Fintype
      {chi : H → K |
        (genWeightSpace M chi : LieSubmodule K H M).toSubmodule ≠ ⊥} :=
    hfinite.fintype
  have htop :
      (⨆ chi : {chi : H → K |
          (genWeightSpace M chi : LieSubmodule K H M).toSubmodule ≠ ⊥},
        (genWeightSpace M (chi : H → K) : LieSubmodule K H M).toSubmodule) = ⊤ := by
    calc
      _ = ⨆ chi : H → K,
          (genWeightSpace M chi : LieSubmodule K H M).toSubmodule :=
        iSup_ne_bot_subtype _
      _ = ⊤ := by
        apply LieSubmodule.iSup_toSubmodule_eq_top.mpr
        refine eq_top_iff.mpr ?_
        rw [←
          iSup_genWeightSpace_sub_posRootCone_eq_top_of_isHighestWeightVector_of_lieSpan_eq_top
            hv hgen]
        exact iSup₂_le fun nu _ ↦
          le_iSup (fun chi : H → K ↦ genWeightSpace M chi)
            (((lam - nu : Dual K H) : H → K))
  apply Module.Finite.of_fg_top
  rw [← htop]
  refine Submodule.fg_iSup _ fun chi ↦ ?_
  exact (Submodule.fg_iff_finiteDimensional _).mpr
    (finiteDimensional_genWeightSpace_of_isHighestWeightVector_of_lieSpan_eq_top
      hv hgen (chi : H → K))

/-- **Finite-dimensionality criterion for an irreducible highest weight module.** Such a module is
finite-dimensional if and only if its highest weight is dominant integral. -/
theorem finiteDimensional_iff_isDominantIntegral_of_isHighestWeightVector
    (hv : IsHighestWeightVector b lam v) :
    FiniteDimensional K M ↔ IsDominantIntegral b lam := by
  constructor
  · intro hM
    let _ := hM
    exact hv.isDominantIntegral
  · exact finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral hv

/-! ### The criterion at the named carrier `L(lam)` -/

/-- **`L(lam)` is finite-dimensional at a dominant integral weight.** When `M(lam)` is nonzero,
`L(lam)` is an irreducible highest weight module of dominant integral weight, and
`TauCeti.finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral` applies; otherwise
`L(lam)` is the zero module. No hypothesis on `M(lam)` is needed either way. -/
theorem finiteDimensional_irreducibleQuotient_of_isDominantIntegral
    (hlam : IsDominantIntegral b lam) : FiniteDimensional K (irreducibleQuotient b lam) := by
  by_cases h : vermaGenerator b lam = 0
  · have _ := (subsingleton_irreducibleQuotient_iff b lam).mpr h
    exact Module.finite_of_rank_eq_zero (rank_subsingleton' K _)
  · have _ := isIrreducible_irreducibleQuotient b lam h
    exact finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral
      (isHighestWeightVector_irreducibleQuotientGenerator b lam h) hlam

variable (b) in
/-- **A finite-dimensional irreducible module is a copy of `L(lam)`, for a dominant integral
weight `lam`.** It carries a highest weight vector of a dominant integral weight
(`TauCeti.exists_isHighestWeightVector_and_isDominantIntegral_of_irreducible`), which makes
`M(lam)` nonzero, and two irreducible modules with highest weight vectors of the same weight are
equivalent. -/
theorem exists_isDominantIntegral_nonempty_lieModuleEquiv_irreducibleQuotient
    [FiniteDimensional K M] :
    ∃ lam : Dual K H, IsDominantIntegral b lam ∧
      Nonempty (M ≃ₗ⁅K,L⁆ irreducibleQuotient b lam) := by
  obtain ⟨lam, v, hv, hlam⟩ :=
    exists_isHighestWeightVector_and_isDominantIntegral_of_irreducible (M := M) b
  have hne := vermaGenerator_ne_zero_of_isHighestWeightVector b lam hv
  have _ := isIrreducible_irreducibleQuotient b lam hne
  exact ⟨lam, hlam, nonempty_lieModuleEquiv_of_isHighestWeightVector hv
    (isHighestWeightVector_irreducibleQuotientGenerator b lam hne)⟩

end TauCeti
