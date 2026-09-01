/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Adjoining roots of finitely many elements

For finitely many elements of a field `F` and `0 < n`, there is a finite extension of `F` in
which each of them has an `n`-th root: adjoin the roots inside an algebraic closure.

Nothing here is specific to purely inseparable extensions or to a characteristic exponent; the
result is stated for an arbitrary positive power.

It has no consumer in this repository yet. The motivating application is the `L'` of Stacks
10.161.13 (tag 032O), feeding `RingTheory/IntegralClosure/NormalizationFinite`: the embedding
theorem in `TauCeti/FieldTheory/PurelyInseparable/Embedding.lean` assumes exactly such an
extension as a hypothesis rather than building one, so it does not use this lemma.

## Main results

* `TauCeti.exists_finiteDimensional_forall_exists_pow_eq`: a finite extension of `F` containing
  `n`-th roots of finitely many given elements of `F`.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`.
-/

public section

universe u

namespace TauCeti

/-- For finitely many elements `s` of a field `F` and `0 < n`, there is a finite extension `E` of
`F` in which every `c ∈ s` has an `n`-th root: adjoin the roots inside an algebraic closure. Both
conjuncts concern the same witness `E`, which is why they are bundled.

This is the shape the construction of the extension `L′` in Stacks, Lemma 10.161.13 (tag 032O)
needs —
"There exists a finite purely inseparable field extension `L′/K` and `q = p^e` such that
`L ⊂ L′(x^{1/q})`" — but is NOT that extension: nothing here asserts that `E / F` is purely
inseparable, only that it is finite and contains the required roots. -/
theorem exists_finiteDimensional_forall_exists_pow_eq (F : Type u) [Field F] (s : Finset F)
    {n : ℕ} (hn : 0 < n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E),
      FiniteDimensional F E ∧ ∀ c ∈ s, ∃ d : E, d ^ n = algebraMap F E c := by
  classical
  -- pick an `n`-th root of each `c` inside an algebraic closure, then adjoin the finitely many
  have hroot : ∀ c : F, ∃ d : AlgebraicClosure F,
      d ^ n = algebraMap F (AlgebraicClosure F) c := fun c ↦ IsAlgClosed.exists_pow_nat_eq _ hn
  choose d hd using hroot
  have : Finite (d '' (s : Set F)) := (s.finite_toSet.image d).to_subtype
  refine ⟨IntermediateField.adjoin F (d '' (s : Set F)), inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin (fun x _ ↦ Algebra.IsIntegral.isIntegral x),
    fun c hc ↦ ⟨⟨d c, IntermediateField.subset_adjoin F _ ⟨c, hc, rfl⟩⟩, ?_⟩⟩
  ext
  push_cast
  exact hd c

end TauCeti
