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
The **tensor multiplicity** `TauCeti.tensorMultiplicity b lam mu nu` is the dimension of the space
of morphisms `L(nu) →ₗ⁅K,L⁆ L(lam) ⊗ L(mu)`. For dominant integral `lam` and `mu` the tensor
product is a finite-dimensional `L`-module, so Weyl's theorem decomposes it into irreducibles, and
at a `nu` with `L(nu)` nonzero, hence irreducible, that dimension is the number of copies of
`L(nu)` in the decomposition, the structure constant `c^nu_{lam mu}`. The definition itself, and
the lemmas reading irreducibility off a nonzero multiplicity, ask only for a triangularizable
Cartan subalgebra; algebraic closure enters with the character identity, which calls on Weyl's
complete reducibility theorem.

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
* conversely a nonzero `c^nu_{lam mu}` forces *all three* of `L(lam)`, `L(mu)` and `L(nu)` to be
  nonzero, hence irreducible
  (`TauCeti.isIrreducible_irreducibleQuotient_of_tensorMultiplicity_ne_zero` and its two companions
  for the factors), so a multiplicity that is not visibly `0` counts copies of an honest irreducible
  inside a tensor product of two honest irreducibles;
* the identity never degenerates to `0 = 0`: as soon as `M(lam) ≠ 0` and `M(mu) ≠ 0` some
  `c^nu_{lam mu}` is nonzero (`TauCeti.exists_tensorMultiplicity_ne_zero`), because
  `L(lam) ⊗ L(mu)` is then a nonzero finite-dimensional module;
* and that hypothesis is met unconditionally at `lam = mu = 0`
  (`TauCeti.exists_tensorMultiplicity_zero_ne_zero`), where `M(0) ≠ 0` comes from the trivial
  module rather than from PBW.

PBW would enlarge the set of weights known to contribute, without changing any statement below.

## Main definitions

* `TauCeti.tensorMultiplicity`: the multiplicity `c^nu_{lam mu}` of `L(nu)` in `L(lam) ⊗ L(mu)`.

## Main results

* `TauCeti.irreducibleFormalCharacter_mul_eq_finsum_tensorMultiplicity_smul`: **the character
  identity** `ch L(lam) · ch L(mu) = ∑_nu c^nu_{lam mu} · ch L(nu)`.
* `TauCeti.isIrreducible_irreducibleQuotient_of_tensorMultiplicity_ne_zero`,
  `TauCeti.isIrreducible_irreducibleQuotient_left_of_tensorMultiplicity_ne_zero` and
  `TauCeti.isIrreducible_irreducibleQuotient_right_of_tensorMultiplicity_ne_zero`: a nonzero tensor
  multiplicity makes all three of `L(lam)`, `L(mu)`, `L(nu)` irreducible.
* `TauCeti.exists_tensorMultiplicity_ne_zero`: **some tensor multiplicity is nonzero** whenever the
  two Verma modules are, so the character identity is not a statement about zero modules.
* `TauCeti.exists_tensorMultiplicity_zero_ne_zero`: some `c^nu_{0 0}` is nonzero, unconditionally.

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

-- Algebraic closure is not assumed here: the highest weight theory of
-- `TauCeti/Algebra/Lie/HighestWeight/Verma.lean` that the definition rests on asks only for a
-- triangularizable Cartan subalgebra. It is assumed in the character-identity section below.
variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [_root_.LieModule.IsTriangularizable K H L]

variable (b : (IsKilling.rootSystem H).Base)

/-- **The tensor multiplicity** `c^nu_{lam mu}`: the multiplicity of `L(nu)` in
`L(lam) ⊗ L(mu)` in the sense of `LieModule.isotypicMultiplicity`, that is the dimension of the
space of morphisms `L(nu) →ₗ⁅K,L⁆ L(lam) ⊗ L(mu)`.

It is the number of copies of `L(nu)` in a decomposition of the tensor product into irreducibles
when that reading is available: `lam` and `mu` dominant integral, so that the tensor product is
finite-dimensional and completely reducible, and `L(nu)` nonzero, hence irreducible. At a `nu`
whose Verma module vanishes it is `0`
(`LieModule.isotypicMultiplicity_eq_zero_of_subsingleton`). -/
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

/-- **A nonzero tensor multiplicity makes the left factor an honest irreducible.** Were `L(lam)`
the zero module, so would be `L(lam) ⊗ L(mu)`, in which nothing has a nonzero multiplicity. -/
theorem isIrreducible_irreducibleQuotient_left_of_tensorMultiplicity_ne_zero
    {lam mu nu : Dual K H} (h : tensorMultiplicity b lam mu nu ≠ 0) :
    LieModule.IsIrreducible K L (irreducibleQuotient b lam) := by
  refine isIrreducible_irreducibleQuotient b lam fun h0 ↦ h ?_
  have _ := (subsingleton_irreducibleQuotient_iff b lam).mpr h0
  rw [tensorMultiplicity_def]
  exact LieModule.isotypicMultiplicity_eq_zero_of_subsingleton_codomain K L _ _

/-- **A nonzero tensor multiplicity makes the right factor an honest irreducible.** Were `L(mu)`
the zero module, so would be `L(lam) ⊗ L(mu)`, in which nothing has a nonzero multiplicity. -/
theorem isIrreducible_irreducibleQuotient_right_of_tensorMultiplicity_ne_zero
    {lam mu nu : Dual K H} (h : tensorMultiplicity b lam mu nu ≠ 0) :
    LieModule.IsIrreducible K L (irreducibleQuotient b mu) := by
  refine isIrreducible_irreducibleQuotient b mu fun h0 ↦ h ?_
  have _ := (subsingleton_irreducibleQuotient_iff b mu).mpr h0
  rw [tensorMultiplicity_def]
  exact LieModule.isotypicMultiplicity_eq_zero_of_subsingleton_codomain K L _ _

/-! ### The character identity

The character of `L(lam)` is the character of a decomposition into irreducibles, so from here on
the field is algebraically closed: that is what Weyl's complete reducibility theorem is available
over in `TauCeti/Algebra/Lie/HighestWeight/Decomposition.lean`.
-/

section CharacterIdentity

variable [IsAlgClosed K]

/-- **The character identity for a tensor product of highest weight modules**: the product of the
characters of `L(lam)` and `L(mu)` is the sum of the characters of the `L(nu)`, weighted by the
tensor multiplicities. The weights at which `L(nu)` is nonzero, hence irreducible, are the ones
that contribute: elsewhere both the character and the multiplicity vanish.

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

/-- **The character identity is never a statement about zero modules.** If the two Verma modules
`M(lam)` and `M(mu)` are nonzero then `L(lam) ⊗ L(mu)` is a nonzero finite-dimensional module, so
at least one tensor multiplicity is nonzero, and the sum
`ch L(lam) · ch L(mu) = ∑_nu c^nu_{lam mu} · ch L(nu)` has a term that survives. -/
theorem exists_tensorMultiplicity_ne_zero (lam mu : {l : Dual K H // IsDominantIntegral b l})
    (hlam : vermaGenerator b lam.1 ≠ 0) (hmu : vermaGenerator b mu.1 ≠ 0) :
    ∃ nu : {l : Dual K H // IsDominantIntegral b l}, tensorMultiplicity b lam.1 mu.1 nu.1 ≠ 0 := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral lam.2
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral mu.2
  by_contra hall
  push Not at hall
  -- every term of the sum vanishes, so the product of the two characters does
  have hzero : ∀ nu : {l : Dual K H // IsDominantIntegral b l},
      (tensorMultiplicity b lam.1 mu.1 nu.1 : ℤ) • irreducibleFormalCharacter b nu = 0 := by
    intro nu
    rw [hall nu]
    simp
  have hprod : irreducibleFormalCharacter b lam * irreducibleFormalCharacter b mu = 0 := by
    rw [irreducibleFormalCharacter_mul_eq_finsum_tensorMultiplicity_smul b lam mu,
      finsum_congr hzero, finsum_zero]
  -- characters are multiplicative on tensor products, so this is the character of `L(lam) ⊗ L(mu)`
  -- vanishing, which says that the tensor product is zero-dimensional
  rw [irreducibleFormalCharacter_def, irreducibleFormalCharacter_def, ← formalCharacter_tensor,
    formalCharacter_eq_zero_iff, Module.finrank_tensorProduct] at hprod
  -- so one of the two factors is zero-dimensional, that is, one of the Verma modules vanishes
  rcases Nat.mul_eq_zero.mp hprod with h | h
  · exact hlam ((subsingleton_irreducibleQuotient_iff b lam.1).mp (Module.finrank_zero_iff.mp h))
  · exact hmu ((subsingleton_irreducibleQuotient_iff b mu.1).mp (Module.finrank_zero_iff.mp h))

/-- **At the zero weight the hypothesis of `TauCeti.exists_tensorMultiplicity_ne_zero` holds
outright**, with no appeal to Poincaré--Birkhoff--Witt: the trivial one-dimensional module makes
`M(0) ≠ 0` (`TauCeti.isHighestWeightVector_vermaGenerator_zero`). So there is a weight at which the
character identity relates honest nonzero irreducibles with a nonzero structure constant. -/
theorem exists_tensorMultiplicity_zero_ne_zero :
    ∃ nu : {l : Dual K H // IsDominantIntegral b l},
      tensorMultiplicity b (0 : Dual K H) 0 nu.1 ≠ 0 :=
  exists_tensorMultiplicity_ne_zero b ⟨0, isDominantIntegral_zero⟩ ⟨0, isDominantIntegral_zero⟩
    (isHighestWeightVector_vermaGenerator_zero b).ne_zero
    (isHighestWeightVector_vermaGenerator_zero b).ne_zero

end CharacterIdentity

end TauCeti
