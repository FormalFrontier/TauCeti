/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Classification
public import TauCeti.Algebra.Lie.Sl2.CompleteReducibility
-- Non-public: `TauCeti.exists_isInternal_isIrreducible` and
-- `TauCeti.finrank_eq_sum_finrank_of_isInternal` appear only inside proofs, never in the type of
-- an exported declaration.
import TauCeti.Algebra.Lie.Submodule.Decomposition
import TauCeti.LinearAlgebra.Dimension.DirectSum

/-!
# Every finite-dimensional `sl₂`-module is a direct sum of the `V(n)`

`TauCeti/Algebra/Lie/Sl2/CompleteReducibility.lean` proves complete reducibility in its
complement form: every Lie submodule of a finite-dimensional module over a Lie algebra generated
by an `sl₂` triple has a complement. `TauCeti/Algebra/Lie/Sl2/Classification.lean` proves that the
finite-dimensional irreducibles are exactly the standard modules `TauCeti.Sl2Std K n = V(n)`. This
file joins the two into the decomposition itself: such a module is an internal direct sum of
finitely many irreducible Lie submodules, and over `LieAlgebra.SpecialLinear.sl (Fin 2) K` each
summand is a `V(n)`.

The passage from complements to a decomposition is lattice-theoretic, and is carried out for an
arbitrary Lie module in `TauCeti/Algebra/Lie/Submodule/Decomposition.lean`
(`TauCeti.exists_isInternal_isIrreducible`); this file only feeds it the `sl₂` complements and
identifies the resulting summands.

## Main results

* `TauCeti.Sl2Std.exists_isInternal_lieModuleEquiv`: **every finite-dimensional `sl₂`-module is
  `⨁ V(nᵢ)`.** Over `LieAlgebra.SpecialLinear.sl (Fin 2) K` the summands are the standard modules.
* `TauCeti.Sl2Std.finrank_eq_sum`: the dimension of the module is `∑ᵢ (nᵢ + 1)`.

## References

This closes the complete-reducibility item of Layer 0 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, which asks that every
finite-dimensional `sl₂`-module be exhibited as a direct sum of the `V(nᵢ)`.

* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972],
  §6.3 and §7.2.
-/

public section

namespace TauCeti

open LieModule Module

namespace Sl2Std

open LieAlgebra

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {M : Type*} [AddCommGroup M] [Module K M]
  [LieRingModule (SpecialLinear.sl (Fin 2) K) M] [LieModule K (SpecialLinear.sl (Fin 2) K) M]
  [FiniteDimensional K M]

variable (K M) in
/-- **Every finite-dimensional `sl₂`-module is `⨁ V(nᵢ)`.** Over an algebraically closed field of
characteristic zero, a finite-dimensional `LieAlgebra.SpecialLinear.sl (Fin 2) K`-module is the
internal direct sum of a finite family of Lie submodules, the `i`-th of which is equivalent to the
standard irreducible `V(nᵢ)`. The highest weights `nᵢ` are returned alongside the summands. -/
theorem exists_isInternal_lieModuleEquiv :
    ∃ (k : ℕ) (N : Fin k → LieSubmodule K (SpecialLinear.sl (Fin 2) K) M) (n : Fin k → ℕ),
      DirectSum.IsInternal (fun i ↦ (N i).toSubmodule) ∧
        ∀ i, Nonempty (N i ≃ₗ⁅K,SpecialLinear.sl (Fin 2) K⁆ Sl2Std K (n i)) := by
  have _i : ComplementedLattice (LieSubmodule K (SpecialLinear.sl (Fin 2) K) M) :=
    ⟨exists_isCompl_sl_fin_two⟩
  obtain ⟨k, N, hint, hirr⟩ := exists_isInternal_isIrreducible K (SpecialLinear.sl (Fin 2) K) M
  have hex : ∀ i, ∃ n : ℕ,
      Nonempty (N i ≃ₗ⁅K,SpecialLinear.sl (Fin 2) K⁆ Sl2Std K n) := fun i ↦
    have := hirr i
    (existsUnique_nonempty_lieModuleEquiv (M := N i)).exists
  choose n hn using hex
  exact ⟨k, N, n, hint, hn⟩

omit [CharZero K] [IsAlgClosed K] [LieModule K (SpecialLinear.sl (Fin 2) K) M]
  [FiniteDimensional K M] in
/-- **The dimension of an `sl₂`-module from its decomposition.** If the module is the internal
direct sum of Lie submodules equivalent to `V(n₀), …, V(n_{k-1})`, its dimension is `∑ᵢ (nᵢ + 1)`,
each `V(nᵢ)` having dimension `nᵢ + 1`. -/
theorem finrank_eq_sum {k : ℕ} {N : Fin k → LieSubmodule K (SpecialLinear.sl (Fin 2) K) M}
    {n : Fin k → ℕ} (hint : DirectSum.IsInternal fun i ↦ (N i).toSubmodule)
    (hn : ∀ i, Nonempty (N i ≃ₗ⁅K,SpecialLinear.sl (Fin 2) K⁆ Sl2Std K (n i))) :
    finrank K M = ∑ i, (n i + 1) := by
  have hfin (i : Fin k) : Module.Finite K (N i).toSubmodule :=
    Module.Finite.equiv (hn i).some.toLinearEquiv.symm
  rw [finrank_eq_sum_finrank_of_isInternal hint]
  exact Finset.sum_congr rfl fun i _ ↦
    ((hn i).some.toLinearEquiv.finrank_eq).trans finrank_eq

end Sl2Std

end TauCeti
