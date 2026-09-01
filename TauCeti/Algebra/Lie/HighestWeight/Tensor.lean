/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Decomposition

public section

/-!
# Tensor multiplicities of irreducible modules

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, `H` a Cartan subalgebra and `b` a base of its root system.
For dominant integral weights `lam` and `mu` the tensor product `L(lam) ⊗ L(mu)` is a
finite-dimensional `L`-module, so Weyl's theorem decomposes it into irreducibles; the
**tensor multiplicity** `TauCeti.tensorMultiplicity b lam mu nu` is the number of copies of
`L(nu)` in that decomposition, the structure constant `c^nu_{lam mu}`.

The theorem about it is the character identity

`ch L(lam) · ch L(mu) = ∑_nu c^nu_{lam mu} · ch L(nu)`,

which combines two facts already in place: formal characters are multiplicative on tensor products
(`TauCeti.formalCharacter_tensor`), and the character of a finite-dimensional module is the
multiplicity-weighted sum of the irreducible characters
(`TauCeti.formalCharacter_eq_finsum_isotypicMultiplicity_smul`). It is what makes the tensor
multiplicities computable from characters, and the identity a Pieri or Littlewood-Richardson rule
evaluates.

Nothing here *assumes* that `L(nu)` is nonzero. Whether `M(nu) ≠ 0`, equivalently `L(nu) ≠ 0`
(`TauCeti.subsingleton_irreducibleQuotient_iff`), is the Poincaré--Birkhoff--Witt input that
`TauCeti/Algebra/Lie/HighestWeight/Verma.lean` does not have and that the roadmap stages as a
sub-project of its own; as in `TauCeti/Algebra/Lie/HighestWeight/Decomposition.lean`, the
statements here are arranged so as not to need it. That arrangement does not leave the
multiplicities undetermined, and it does not make the identity a statement about zero modules:

* at a weight whose Verma module vanishes `L(nu)` is the zero module and `c^nu_{lam mu}` is `0`
  (`LieModule.isotypicMultiplicity_eq_zero_of_subsingleton`), the correct count of copies of a zero
  module in a decomposition into irreducibles, so that weight contributes nothing to the sum;
* conversely every weight that *does* contribute has `M(nu) ≠ 0`, so `L(nu)` there is genuinely
  irreducible (`TauCeti.isIrreducible_irreducibleQuotient_of_tensorMultiplicity_ne_zero`), and the
  same holds of the two characters on the left
  (`TauCeti.isIrreducible_irreducibleQuotient_of_irreducibleFormalCharacter_ne_zero`);
* and the identity is not vacuous: `TauCeti.irreducibleFormalCharacter_zero_ne_zero` proves
  without any appeal to PBW that `L(0)` is a nonzero irreducible with a nonzero character.

PBW would enlarge the set of weights known to contribute, without changing any statement below.

## Main definitions

* `TauCeti.tensorMultiplicity`: the multiplicity `c^nu_{lam mu}` of `L(nu)` in `L(lam) ⊗ L(mu)`.

## Main results

* `TauCeti.irreducibleFormalCharacter_mul_eq_finsum_tensorMultiplicity_smul`: **the character
  identity** `ch L(lam) · ch L(mu) = ∑_nu c^nu_{lam mu} · ch L(nu)`.
* `TauCeti.isIrreducible_irreducibleQuotient_of_tensorMultiplicity_ne_zero`: a weight with a
  nonzero tensor multiplicity has an irreducible `L(nu)`.

## References

This is the tensor-multiplicity item of the milestone "tensor multiplicities and the minuscule
Pieri rule" in the Layer 6 decomposition toolkit of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, which asks for `c^ν_{λμ}` "with
the character identity `ch L(λ) · ch L(μ) = Σ_ν c^ν_{λμ} ch L(ν)` through `formalCharacter_tensor`".
The minuscule Pieri rule itself, which evaluates these multiplicities, awaits the Weyl character
formula.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.
-/

open scoped TensorProduct

namespace TauCeti

open LieAlgebra Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable (b : (IsKilling.rootSystem H).Base)

/-- **The tensor multiplicity** `c^nu_{lam mu}`: the number of copies of `L(nu)` in the
decomposition of `L(lam) ⊗ L(mu)` into irreducibles, that is the multiplicity of `L(nu)` in the
tensor product in the sense of `LieModule.isotypicMultiplicity`. -/
noncomputable def tensorMultiplicity (lam mu nu : Dual K H) : ℕ :=
  LieModule.isotypicMultiplicity K L
    (irreducibleQuotient b lam ⊗[K] irreducibleQuotient b mu) (irreducibleQuotient b nu)

-- This private reduction is required by Lean's module system: an exported theorem cannot unfold
-- the opaque exported definition directly while checking its public signature.
private theorem tensorMultiplicity_def_aux (lam mu nu : Dual K H) :
    tensorMultiplicity b lam mu nu = LieModule.isotypicMultiplicity K L
      (irreducibleQuotient b lam ⊗[K] irreducibleQuotient b mu) (irreducibleQuotient b nu) :=
  (rfl)

/-- The tensor multiplicity is the multiplicity of `L(nu)` in the tensor product. -/
@[simp]
theorem tensorMultiplicity_def (lam mu nu : Dual K H) :
    tensorMultiplicity b lam mu nu = LieModule.isotypicMultiplicity K L
      (irreducibleQuotient b lam ⊗[K] irreducibleQuotient b mu) (irreducibleQuotient b nu) :=
  tensorMultiplicity_def_aux b lam mu nu

/-- **A nonzero tensor multiplicity counts copies of an honest irreducible.** Were `L(nu)` the zero
module, its multiplicity would vanish (`LieModule.isotypicMultiplicity_eq_zero_of_subsingleton`),
so every weight that contributes to the character identity has `M(nu) ≠ 0`, and `L(nu)` there is
irreducible. -/
theorem isIrreducible_irreducibleQuotient_of_tensorMultiplicity_ne_zero {lam mu nu : Dual K H}
    (h : tensorMultiplicity b lam mu nu ≠ 0) :
    LieModule.IsIrreducible K L (irreducibleQuotient b nu) := by
  refine isIrreducible_irreducibleQuotient b nu fun h0 ↦ h ?_
  have _ := (subsingleton_irreducibleQuotient_iff b nu).mpr h0
  rw [tensorMultiplicity_def]
  exact LieModule.isotypicMultiplicity_eq_zero_of_subsingleton K L _ _

/-- **The character identity for a tensor product of irreducibles**: the product of the characters
of `L(lam)` and `L(mu)` is the sum of the characters of the `L(nu)`, weighted by the tensor
multiplicities.

Formal characters are multiplicative on tensor products, so the left-hand side is the character of
`L(lam) ⊗ L(mu)`; that module is finite-dimensional, so its character is the
multiplicity-weighted sum of the irreducible characters. -/
theorem irreducibleFormalCharacter_mul_eq_finsum_tensorMultiplicity_smul
    (lam mu : {l : Dual K H // IsDominantIntegral b l}) :
    irreducibleFormalCharacter b lam * irreducibleFormalCharacter b mu
      = ∑ᶠ nu : {l : Dual K H // IsDominantIntegral b l},
          (tensorMultiplicity b lam.1 mu.1 nu.1 : ℤ) • irreducibleFormalCharacter b nu := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral lam.2
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral mu.2
  simp only [tensorMultiplicity_def]
  rw [irreducibleFormalCharacter_def, irreducibleFormalCharacter_def,
    ← formalCharacter_tensor]
  exact formalCharacter_eq_finsum_isotypicMultiplicity_smul b

end TauCeti
