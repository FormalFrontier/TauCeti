/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
-- Non-public: `Module.finrank_pi_fintype` and `Module.Finite.of_restrictScalars_finite` are used
-- only inside proofs, and no exported statement here mentions a product module or `Module.Finite`
-- over the ring, so downstream importers do not pay for either module.
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Modules over a simple Artinian ring are classified by their dimension

Over a simple Artinian ring `R` all simple modules are isomorphic: Mathlib records this as
`IsSimpleRing.isIsotypic`, which says that any two simple submodules of any `R`-module are
isomorphic. A semisimple module is a direct sum of simple ones, so a finitely generated `R`-module
is `Sⁿ` for a **fixed** simple module `S` and a single natural number `n`, and `n` is the only
invariant there is.

This file turns that into the working statement: if `R` is moreover an algebra over a field `K` and
`M`, `N` are `R`-modules which are finite-dimensional over `K`, then

  `M ≃ₗ[R] N ↔ finrank K M = finrank K N`.

The dimension count is the bookkeeping that converts "the same number of simple summands" into a
condition that can be checked, and it is what makes the classification usable: two `R`-module
structures put on the *same* finite-dimensional `K`-vector space are automatically isomorphic. That
is exactly the input the Skolem-Noether theorem needs, in
`TauCeti/Algebra/CentralSimple/SkolemNoether.lean`.

## Main results

* `TauCeti.IsIsotypicOfType.of_isSimpleRing`: over a simple Artinian ring, every module is isotypic
  of the type of any chosen minimal left ideal. This upgrades Mathlib's `IsSimpleRing.isIsotypic`,
  which compares simple submodules of a single module, to a comparison against a fixed simple
  module, which is what lets two different modules be compared with each other.
* `TauCeti.IsSimpleRing.nonempty_linearEquiv_of_finrank_eq`: two finite-dimensional modules over a
  simple Artinian `K`-algebra with the same `K`-dimension are isomorphic.
* `TauCeti.IsSimpleRing.nonempty_linearEquiv_iff_finrank_eq`: the two-way form, the classification
  itself.

## Implementation notes

The chosen simple module is a minimal left ideal `S : Submodule R R`, produced as an atom of the
lattice of submodules of the regular module rather than assumed. Taking it inside `R` rather than
inside `M` is what makes it available to `M` and `N` at once, and it inherits the `K`-module
structure from `R`, so its dimension is finite and nonzero and can be cancelled.

Simplicity of `R` is not weakened to semisimplicity: over a semisimple ring with more than one block
the dimension is not a complete invariant, since a module can distribute the same total dimension
over the blocks in different ways.

## References

This supplies the classification of modules over a simple Artinian ring used by the Layer 5 target
`skolemNoether` of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, Chapter 1, and R. S. Pierce,
*Associative Algebras*, GTM 88, Chapter 3.
-/

public section

namespace TauCeti

open Module

variable {R : Type*} [Ring R] [IsSimpleRing R] [IsArtinianRing R]

/-- Over a **simple Artinian** ring `R`, every `R`-module is isotypic of the type of a chosen
minimal left ideal `S`: every simple submodule of every `R`-module is isomorphic to `S`.

Mathlib's `IsSimpleRing.isIsotypic` compares two simple submodules of one and the same module. The
content added here is that the comparison can be made against a fixed simple module living in `R`
itself, so that simple submodules of *different* modules become comparable: a simple submodule of
`M` is isomorphic to some ideal of `R` because `R` is semisimple, and that ideal is isomorphic to
`S` because `R` is isotypic over itself. -/
theorem IsIsotypicOfType.of_isSimpleRing (S : Submodule R R) [IsSimpleModule R S]
    (M : Type*) [AddCommGroup M] [Module R M] : IsIsotypicOfType R M S := by
  intro m _
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule (R := R) (M := m)
  have : IsSimpleModule R I := IsSimpleModule.congr e.symm
  exact ⟨e.trans (IsSimpleRing.isIsotypic R R I S).some.symm⟩

namespace IsSimpleRing

variable (K : Type*) [Field K] [Algebra K R] [FiniteDimensional K R]
  {M : Type*} [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [FiniteDimensional K M]
  {N : Type*} [AddCommGroup N] [Module K N] [Module R N] [IsScalarTower K R N]
  [FiniteDimensional K N]

/-- **Modules over a simple Artinian algebra are classified by their dimension.** If `R` is a
finite-dimensional simple `K`-algebra and `M`, `N` are `R`-modules which are finite-dimensional over
`K`, then equal `K`-dimension forces an `R`-linear isomorphism.

Both modules are direct sums of copies of one and the same simple module `S`
(`TauCeti.IsIsotypicOfType.of_isSimpleRing`), say `Sⁿ` and `Sᵐ`; comparing dimensions gives
`n * finrank K S = m * finrank K S`, and `finrank K S ≠ 0`, so `n = m`. -/
theorem nonempty_linearEquiv_of_finrank_eq (h : finrank K M = finrank K N) :
    Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R R)
  rw [← isSimpleModule_iff_isAtom] at hS
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite K R M
  have : Module.Finite R N := Module.Finite.of_restrictScalars_finite K R N
  obtain ⟨n, ⟨eM⟩⟩ := (IsIsotypicOfType.of_isSimpleRing S M).linearEquiv_fun
  obtain ⟨m, ⟨eN⟩⟩ := (IsIsotypicOfType.of_isSimpleRing S N).linearEquiv_fun
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  have hSpos : 0 < finrank K S := Module.finrank_pos
  have hM : finrank K M = n * finrank K S := by
    rw [(eM.restrictScalars K).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hN : finrank K N = m * finrank K S := by
    rw [(eN.restrictScalars K).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  obtain rfl : n = m := Nat.eq_of_mul_eq_mul_right hSpos (hM.symm.trans (h.trans hN))
  exact ⟨eM.trans eN.symm⟩

/-- **The classification of finite-dimensional modules over a simple Artinian algebra**: the
`K`-dimension is a complete invariant. The forward implication holds over any ring; the content is
the converse, `TauCeti.IsSimpleRing.nonempty_linearEquiv_of_finrank_eq`. -/
theorem nonempty_linearEquiv_iff_finrank_eq :
    Nonempty (M ≃ₗ[R] N) ↔ finrank K M = finrank K N :=
  ⟨fun ⟨e⟩ ↦ (e.restrictScalars K).finrank_eq, nonempty_linearEquiv_of_finrank_eq K⟩

end IsSimpleRing

end TauCeti
