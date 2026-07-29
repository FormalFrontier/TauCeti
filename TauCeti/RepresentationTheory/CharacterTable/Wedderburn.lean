/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Matrix.Pi
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# The Wedderburn blocks of a finite group algebra

Over an algebraically closed field `k` whose characteristic does not divide the order of a finite
group `G`, Maschke's theorem makes `k[G]` semisimple and Artin--Wedderburn presents it as a finite
product of matrix algebras `∏ᵢ Matₙᵢ(k)`. This file reads the two classical numerical invariants
off such a presentation:

* `TauCeti.sum_sq_eq_card_of_algEquiv_pi_matrix`: the matrix sizes satisfy `∑ᵢ nᵢ² = |G|`, because
  both sides compute `dimₖ k[G]`;
* `TauCeti.card_eq_card_conjClasses_of_algEquiv_pi_matrix`: the **number of blocks is the number of
  conjugacy classes** of `G`, because both sides compute `dimₖ Z(k[G])` — on one side through the
  class-sum basis (`TauCeti.finrank_center_monoidAlgebra`), on the other because the center of a
  product of matrix algebras over `k` is the product of their (one-dimensional) centers.

`TauCeti.exists_algEquiv_pi_matrix` assembles Maschke and Artin--Wedderburn into the existence of a
presentation, and `TauCeti.exists_algEquiv_pi_matrix_conjClasses` packages the three results: there
is a presentation of `k[G]` indexed by the conjugacy classes of `G` whose degrees have squares
summing to `|G|`.

Two further statements about a Wedderburn presentation are deliberately not proved here, and are
needed before the block count can be *called* the count of irreducible representations: that the
blocks are in bijection with the isomorphism classes of simple `k[G]`-modules, and that the multiset
of degrees does not depend on the chosen presentation. What this file supplies is the numerical
half, which is what the dimension arguments can see.

## References

This implements the Layer 2 targets `exists_algEquiv_pi_matrix`, `sum_sq_dim_eq_card`,
`center_algEquiv_pi`, and `card_irreps_eq_card_conjClasses` of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
and its
[suggested declarations](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/Suggested.lean).
-/

public section

namespace TauCeti

open scoped BigOperators

section Presentation

variable {k G : Type*} [Field k] {ι : Type*} {d : ι → ℕ}

/-- **The sum of the squares of the matrix sizes is the order of the group**: both sides compute
the dimension of `k[G]`. -/
theorem sum_sq_eq_card_of_algEquiv_pi_matrix [Monoid G] [Finite G] [Fintype ι]
    (e : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    ∑ i, d i ^ 2 = Nat.card G :=
  calc ∑ i, d i ^ 2
      = Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) := (finrank_pi_matrix k d).symm
    _ = Module.finrank k (MonoidAlgebra k G) := e.toLinearEquiv.finrank_eq.symm
    _ = Nat.card G := by
        letI := Fintype.ofFinite G
        rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G k), Fintype.card_eq_nat_card]

/-- **The center of the group algebra splits**: a Wedderburn presentation of `k[G]` with blocks
indexed by `ι` identifies `Z(k[G])` with the algebra `ι → k` of functions on the blocks. -/
noncomputable def centerMonoidAlgebraAlgEquivPi [Monoid G] [∀ i, NeZero (d i)]
    (e : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (ι → k) :=
  (centerCongr e).trans (centerPiMatrixAlgEquiv k d)

/-- `centerMonoidAlgebraAlgEquivPi e` records, block by block, the scalar that a central element of
`k[G]` acts by: the `i`-th component of the image of `e` is that scalar matrix. -/
@[simp]
theorem algebraMap_centerMonoidAlgebraAlgEquivPi_apply [Monoid G] [∀ i, NeZero (d i)]
    (e : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)
    (z : Subalgebra.center k (MonoidAlgebra k G)) (i : ι) :
    algebraMap k (Matrix (Fin (d i)) (Fin (d i)) k) (centerMonoidAlgebraAlgEquivPi e z i) =
      e (z : MonoidAlgebra k G) i := by
  simp [centerMonoidAlgebraAlgEquivPi]

/-- The inverse of `centerMonoidAlgebraAlgEquivPi e` builds the central element acting on each
block by the prescribed scalar. -/
@[simp]
theorem centerMonoidAlgebraAlgEquivPi_symm_apply [Monoid G] [∀ i, NeZero (d i)]
    (e : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) (f : ι → k) (i : ι) :
    e ((centerMonoidAlgebraAlgEquivPi e).symm f : MonoidAlgebra k G) i =
      algebraMap k (Matrix (Fin (d i)) (Fin (d i)) k) (f i) := by
  simp [centerMonoidAlgebraAlgEquivPi]

/-- **The number of Wedderburn blocks of `k[G]` is the number of conjugacy classes of `G`**: both
sides compute the dimension of `Z(k[G])`.

This is the numerical half of the count `#irreducibles = #conjugacy classes`; identifying the blocks
with the isomorphism classes of simple `k[G]`-modules is a separate statement. -/
theorem card_eq_card_conjClasses_of_algEquiv_pi_matrix [Group G] [Finite G] [Fintype ι]
    [∀ i, NeZero (d i)] (e : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    Fintype.card ι = Nat.card (ConjClasses G) :=
  calc Fintype.card ι
      = Module.finrank k (Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) :=
        (finrank_center_pi_matrix k d).symm
    _ = Module.finrank k (Subalgebra.center k (MonoidAlgebra k G)) :=
        (centerCongr e).toLinearEquiv.finrank_eq.symm
    _ = Nat.card (ConjClasses G) := finrank_center_monoidAlgebra k G

end Presentation

section Existence

variable (k G : Type*) [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)] [IsAlgClosed k]

/-- **Maschke and Artin--Wedderburn for a finite group algebra**: over an algebraically closed field
whose characteristic does not divide `|G|`, the group algebra is a finite product of matrix algebras
of positive size. -/
theorem exists_algEquiv_pi_matrix :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (MonoidAlgebra k G)

/-- The Wedderburn decomposition of `k[G]`, with its blocks indexed by the conjugacy classes of `G`
themselves, and with the degrees squaring to a sum of `|G|`.

The indexing is by an arbitrary bijection between the blocks and the conjugacy classes: the
statement asserts nothing about *which* class labels a given block. -/
theorem exists_algEquiv_pi_matrix_conjClasses :
    ∃ d : ConjClasses G → ℕ, (∀ i, NeZero (d i)) ∧ ∑ᶠ i, d i ^ 2 = Nat.card G ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix k G
  haveI := hd
  obtain rfl : n = Nat.card (ConjClasses G) := by
    simpa using card_eq_card_conjClasses_of_algEquiv_pi_matrix e
  set σ := Finite.equivFin (ConjClasses G)
  refine ⟨fun c => d (σ c), fun c => hd _, ?_,
    ⟨e.trans (AlgEquiv.piCongrLeft k (fun i => Matrix (Fin (d i)) (Fin (d i)) k) σ).symm⟩⟩
  rw [finsum_comp_equiv σ (f := fun i => d i ^ 2), finsum_eq_sum_of_fintype]
  exact sum_sq_eq_card_of_algEquiv_pi_matrix e

end Existence

end TauCeti
