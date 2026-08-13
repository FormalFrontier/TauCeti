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
according as it is or is not isomorphic to `S`: `1` because the endomorphism algebra of a
finite-dimensional simple module over an algebraically closed field is `k` itself
(`TauCeti.endAlgEquivSelfOfIsSimpleModule`), and `0` because a map between inequivalent simple
modules vanishes (`TauCeti.hom_eq_zero_of_isEmpty_linearEquiv`).

Everything is stated for a `k`-algebra `A` and `A`-modules that are `k`-modules compatibly, which
is the generality the group-representation application needs: for `A = k[G]` the hom space is the
space of intertwiners and the theorem is the classical "multiplicity equals the dimension of the
space of intertwiners".

## Main definitions

* `TauCeti.homCompRight`: postcomposition with an `A`-linear map, as a `k`-linear map of hom
  spaces out of a fixed module.
* `TauCeti.homCongrRight`: isomorphic `A`-modules have `k`-isomorphic hom spaces out of a fixed
  module.  This is `LinearEquiv.congrRight` for a noncommutative `A`, with the auxiliary scalars
  `k` supplying the linear structure that `A` cannot.

## Main results

* `TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv` and
  `TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv`: Schur's lemma in dimension form.
* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`: **the multiplicity theorem.**  If
  `M ≃ₗ[A] ∀ i, N i` with every `N i` simple, then `finrank k (S →ₗ[A] M)` is the number of
  indices `i` with `N i ≅ S`.
* `TauCeti.natCard_eq_natCard_of_linearEquiv_pi`: consequently the number of factors isomorphic
  to `S` is the same for any two such decompositions of `M`, so the multiplicity is well defined.
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

/-! ### Transporting a hom space along an isomorphism of the target -/

section CongrRight

variable (k : Type*) {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
variable {S : Type*} [AddCommMonoid S] [Module A S]
variable {N : Type*} [AddCommMonoid N] [Module A N] [Module k N] [IsScalarTower k A N]
variable {P : Type*} [AddCommMonoid P] [Module A P] [Module k P] [IsScalarTower k A P]

/-- Postcomposition with an `A`-linear map, as a `k`-linear map of hom spaces out of `S`.

The ring `A` is not assumed commutative, so the hom spaces are not `A`-modules and Mathlib's
`LinearMap.compRight` does not apply; the auxiliary base ring `k`, acting on the targets
compatibly with `A`, supplies the linear structure instead. -/
def homCompRight (g : N →ₗ[A] P) : (S →ₗ[A] N) →ₗ[k] (S →ₗ[A] P) where
  toFun f := g ∘ₗ f
  map_add' _ _ := by ext s; simp
  map_smul' c f := by
    ext s
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    exact g.map_smul_of_tower c (f s)

@[simp]
theorem homCompRight_apply (g : N →ₗ[A] P) (f : S →ₗ[A] N) (s : S) :
    homCompRight k (S := S) g f s = g (f s) :=
  (rfl)

/-- **Isomorphic targets give isomorphic hom spaces.**  An `A`-linear isomorphism `e : N ≃ₗ[A] P`
carries `S →ₗ[A] N` to `S →ₗ[A] P` by postcomposition, `k`-linearly.

This is `LinearEquiv.congrRight` with the auxiliary scalars `k` in place of a commutativity
assumption on `A`. -/
def homCongrRight (e : N ≃ₗ[A] P) : (S →ₗ[A] N) ≃ₗ[k] (S →ₗ[A] P) :=
  LinearEquiv.ofLinearMap (homCompRight k (S := S) (e : N →ₗ[A] P))
    (homCompRight k (S := S) (e.symm : P →ₗ[A] N))
    (by ext f s; simp) (by ext f s; simp)

@[simp]
theorem homCongrRight_apply (e : N ≃ₗ[A] P) (f : S →ₗ[A] N) (s : S) :
    homCongrRight k (S := S) e f s = e (f s) :=
  (rfl)

@[simp]
theorem homCongrRight_symm_apply (e : N ≃ₗ[A] P) (f : S →ₗ[A] P) (s : S) :
    (homCongrRight k (S := S) e).symm f s = e.symm (f s) :=
  (rfl)

end CongrRight

/-! ### Schur's lemma in dimension form -/

section Vanishing

variable {k A S N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module A S] [IsSimpleModule A S]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N] [IsSimpleModule A N]

/-- **Schur's lemma, vanishing form, in dimensions.**  Between inequivalent simple modules the
hom space is trivial, hence of dimension zero. -/
theorem finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] N)) :
    Module.finrank k (S →ₗ[A] N) = 0 := by
  have : Subsingleton (S →ₗ[A] N) := subsingleton_linearMap_of_isEmpty_linearEquiv h
  exact Module.finrank_zero_of_subsingleton

/-- The hom space between inequivalent simple modules is finite-dimensional, being trivial. -/
theorem finiteDimensional_linearMap_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] N)) :
    FiniteDimensional k (S →ₗ[A] N) := by
  have : Subsingleton (S →ₗ[A] N) := subsingleton_linearMap_of_isEmpty_linearEquiv h
  exact Module.Finite.of_surjective (0 : k →ₗ[k] (S →ₗ[A] N)) fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

end Vanishing

section Schur

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [IsSimpleModule A N]

omit [IsSimpleModule A N] in
/-- **Schur's lemma over an algebraically closed field, in dimensions.**  Between equivalent
finite-dimensional simple modules the hom space is a line: every map is a scalar multiple of a
fixed isomorphism. -/
theorem finrank_linearMap_eq_one_of_nonempty_linearEquiv (e : S ≃ₗ[A] N) :
    Module.finrank k (S →ₗ[A] N) = 1 := by
  have hend : Module.finrank k (Module.End A S) = 1 := by
    rw [(endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  rw [← (homCongrRight k (S := S) e).finrank_eq]
  exact hend

/-- The hom space out of a finite-dimensional simple module into a simple module is
finite-dimensional: by Schur's lemma it is a line or trivial. -/
theorem finiteDimensional_linearMap_of_isSimpleModule : FiniteDimensional k (S →ₗ[A] N) := by
  by_cases h : Nonempty (S ≃ₗ[A] N)
  · have hend : FiniteDimensional k (S →ₗ[A] S) :=
      Module.Finite.equiv
        (endAlgEquivSelfOfIsSimpleModule (k := k) (A := A) (S := S)).toLinearEquiv.symm
    exact Module.Finite.equiv (homCongrRight k (S := S) h.some)
  · exact finiteDimensional_linearMap_of_isEmpty_linearEquiv (not_nonempty_iff.mp h)

end Schur

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

/-- **The multiplicity is well defined.**  Two decompositions of the same module into finite
products of simple modules have the same number of factors isomorphic to a given simple module.

This is the Jordan-Hölder invariance of the multiplicity, obtained from the multiplicity theorem
rather than from a refinement argument: both counts compute the same dimension. -/
theorem natCard_eq_natCard_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] {κ : Type*} [Finite κ] {P : κ → Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module k (P j)] [∀ j, Module A (P j)]
    [∀ j, IsScalarTower k A (P j)] [∀ j, IsSimpleModule A (P j)]
    (e : M ≃ₗ[A] ∀ i, N i) (f : M ≃ₗ[A] ∀ j, P j) :
    Nat.card {i // Nonempty (S ≃ₗ[A] N i)} = Nat.card {j // Nonempty (S ≃ₗ[A] P j)} := by
  rw [← finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) e,
    finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) f]

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
