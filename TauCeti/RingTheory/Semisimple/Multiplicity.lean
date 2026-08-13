/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Semisimple.Schur

/-!
# The multiplicity of a simple module, as the dimension of a hom space

Let `A` be an algebra over an algebraically closed field `k` and let `S` be a simple `A`-module,
finite-dimensional over `k`.  If a module `M` is written as a finite direct sum of simple
modules, the number of summands isomorphic to `S` is the **multiplicity** of `S` in `M`.  Written
that way the multiplicity refers to a chosen decomposition; this file identifies it with the
manifestly choice-free number

`Module.finrank k (S →ₗ[A] M)`,

so that the multiplicity is an invariant of `M` and needs no decomposition to be defined.

The proof is Schur's lemma plus additivity.  A hom space out of `S` into a finite product splits
as the product of the hom spaces into the factors, and each factor contributes `1` or `0`
according as it is or is not isomorphic to `S`.  Those two values are the dimension forms of
Schur's lemma, `TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv` and
`TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv`, proved in
`TauCeti/RingTheory/Semisimple/Schur.lean` alongside the transport of a hom space along an
isomorphism of its target, `TauCeti.homCongrRight`.

Everything is stated for a `k`-algebra `A` and `A`-modules that are `k`-modules compatibly, which
is the generality the group-representation application needs: for `A = k[G]` the hom space is the
space of intertwiners and the theorem is the classical "multiplicity equals the dimension of the
space of intertwiners".

## Main results

* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`: **the multiplicity theorem.**  If
  `M ≃ₗ[A] ∀ i, N i` with every `N i` simple, then `finrank k (S →ₗ[A] M)` is the number of
  indices `i` with `N i ≅ S`.
* `TauCeti.natCard_eq_natCard_of_linearEquiv_pi`: consequently equivalent finite products of
  simple modules have the same number of factors isomorphic to `S`; applied to two decompositions
  of one module, this says that the multiplicity is well defined.
* `TauCeti.finrank_linearMap_pos_iff_exists_nonempty_linearEquiv`: the multiplicity is positive
  exactly when `S` occurs among the factors, so the hom space detects the constituents.
* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi_const`: the isotypic case, where `M` is
  a power of `S` itself and the multiplicity is the number of copies.

## Implementation notes

The index set of a decomposition is counted with `Nat.card` of a subtype rather than with a
`Finset.filter`, so that no `DecidablePred` instance enters the statements; the proofs introduce
classical decidability and a `Fintype` structure locally.

Simplicity of `S` and finite dimensionality of `S` over `k` are standing hypotheses, but nothing
is assumed about `M`: the multiplicity theorem takes the decomposition of `M` as data, and the
existence of a decomposition is the separate semisimplicity input.

## References

This builds the multiplicity half of the isotypic-decomposition API that Layer 5 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` lists as a prerequisite of
Clifford theory: "its **isotypic components** and their **multiplicities**, with multiplicity
equal to `finrank` of the relevant `Hom` space".  It is also the counted form of the isotypic
decomposition asked for in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md`.

See C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
§25, or J.-P. Serre, *Linear Representations of Finite Groups*, §2.
-/

public section

namespace TauCeti

/-! ### The multiplicity of a simple module in a finite direct sum -/

section Multiplicity

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)]
  [∀ i, Module A (N i)] [∀ i, IsScalarTower k A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- **The multiplicity theorem for a product of simple modules.**  The dimension of the space of
`A`-linear maps from a simple module `S` into a finite product of simple modules counts the
factors isomorphic to `S`. -/
theorem finrank_linearMap_pi_eq_natCard :
    Module.finrank k (S →ₗ[A] ∀ i, N i) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : Module.finrank k (S →ₗ[A] ∀ i, N i) = ∑ i, Module.finrank k (S →ₗ[A] N i) := by
    rw [← (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k).finrank_eq]
    exact Module.finrank_pi_fintype k
  have hval : ∀ i, Module.finrank k (S →ₗ[A] N i)
      = if Nonempty (S ≃ₗ[A] N i) then 1 else 0 := by
    intro i
    split_ifs with h
    · exact finrank_linearMap_eq_one_of_nonempty_linearEquiv h.some
    · exact finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (not_nonempty_iff.mp h)
  rw [hpi, Finset.sum_congr rfl fun i _ ↦ hval i, Finset.sum_boole, Nat.cast_id,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **The multiplicity theorem.**  If `M` decomposes as a finite direct sum of simple modules
`N i`, then the dimension of the space of `A`-linear maps from a simple module `S` into `M` is
the number of factors isomorphic to `S`.

Only the right-hand side mentions the decomposition, so this is the statement that the
multiplicity of `S` in `M` is an invariant of `M`; see
`TauCeti.natCard_eq_natCard_of_linearEquiv_pi`. -/
theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    Module.finrank k (S →ₗ[A] M) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  rw [← finrank_linearMap_pi_eq_natCard (k := k) (S := S) (N := N),
    ← (homCongrRight k (S := S) e).finrank_eq]

/-- A module with a finite decomposition into simple modules has a finite-dimensional space of
maps from a finite-dimensional simple module into it. -/
theorem finiteDimensional_linearMap_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    FiniteDimensional k (S →ₗ[A] M) := by
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : FiniteDimensional k (S →ₗ[A] ∀ i, N i) :=
    Module.Finite.equiv (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k)
  exact Module.Finite.equiv (homCongrRight k (S := S) e).symm

/-- **A hom space detects a constituent.**  There is a nonzero `A`-linear map from the simple
module `S` into `M` exactly when `S` occurs among the simple factors of `M`. -/
theorem finrank_linearMap_pos_iff_exists_nonempty_linearEquiv {M : Type*} [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    0 < Module.finrank k (S →ₗ[A] M) ↔ ∃ i, Nonempty (S ≃ₗ[A] N i) := by
  rw [finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) e, Nat.card_pos_iff,
    nonempty_subtype]
  exact and_iff_left inferInstance

/-- **The multiplicity is well defined.**  Equivalent finite products of simple modules have the
same number of factors isomorphic to a given simple module.

For two decompositions `e : M ≃ₗ[A] ∀ i, N i` and `f : M ≃ₗ[A] ∀ j, P j` of one module, apply
this to `e.symm.trans f` to see that the multiplicity of `S` in `M` does not depend on the
decomposition.

This is the Jordan-Hölder invariance of the multiplicity, obtained from the multiplicity theorem
rather than from a refinement argument: both counts compute the same dimension. -/
theorem natCard_eq_natCard_of_linearEquiv_pi {κ : Type*} [Finite κ] {P : κ → Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module k (P j)] [∀ j, Module A (P j)]
    [∀ j, IsScalarTower k A (P j)] [∀ j, IsSimpleModule A (P j)]
    (e : (∀ i, N i) ≃ₗ[A] ∀ j, P j) :
    Nat.card {i // Nonempty (S ≃ₗ[A] N i)} = Nat.card {j // Nonempty (S ≃ₗ[A] P j)} := by
  rw [← finrank_linearMap_pi_eq_natCard (k := k) (S := S) (N := N),
    finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) e]

end Multiplicity

/-! ### The isotypic case -/

section Isotypic

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]

/-- **The multiplicity of `S` in a power of `S`.**  If `M` is a finite power of the simple module
`S`, the dimension of the space of `A`-linear maps `S → M` is the number of copies.

This is the form Clifford theory uses: an isotypic component of a restriction is a power of a
single constituent, and its multiplicity is read off as a dimension. -/
theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi_const {ι : Type*} [Finite ι] {M : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] (ι → S)) :
    Module.finrank k (S →ₗ[A] M) = Nat.card ι := by
  rw [finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) (N := fun _ : ι ↦ S) e]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ ⟨LinearEquiv.refl A S⟩)

end Isotypic

end TauCeti
