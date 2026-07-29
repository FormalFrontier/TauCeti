/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Subalgebra.Center
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# The Wedderburn blocks of a finite group algebra

Over an algebraically closed field `k` whose characteristic does not divide the order of a finite
group `G`, Maschke's theorem makes `k[G]` semisimple and Artin--Wedderburn presents it as a finite
product of matrix algebras `∏ᵢ Matₙᵢ(k)`. This file reads the two classical numerical invariants
off such a presentation:

* `TauCeti.sum_sq_eq_card_of_algEquiv_pi_matrix`: the degrees satisfy `∑ᵢ nᵢ² = |G|`, because both
  sides compute `dimₖ k[G]`;
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

/-! ### Products of matrix algebras -/

section PiMatrix

variable (k : Type*) [Field k] {n : ℕ} (d : Fin n → ℕ)

/-- The dimension of a finite product of matrix algebras is the sum of the squares of the sizes. -/
theorem finrank_pi_matrix :
    Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) = ∑ i, d i ^ 2 := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_matrix]
  simp [sq]

/-- The center of a finite product of nonzero matrix algebras over a field consists of the tuples of
scalar matrices, so it is the algebra of functions on the index. -/
noncomputable def centerPiMatrixAlgEquiv [∀ i, NeZero (d i)] :
    Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) ≃ₐ[k] (Fin n → k) :=
  centerPiAlgEquiv.trans (AlgEquiv.piCongrRight fun i =>
    haveI : Nonempty (Fin (d i)) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne (d i)))
    centerAlgEquivOfIsCentral k _)

/-- The center of a finite product of nonzero matrix algebras over a field has dimension the number
of factors. -/
theorem finrank_center_pi_matrix [∀ i, NeZero (d i)] :
    Module.finrank k (Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) = n := by
  rw [(centerPiMatrixAlgEquiv k d).toLinearEquiv.finrank_eq, Module.finrank_pi, Fintype.card_fin]

end PiMatrix

/-! ### The group algebra -/

section GroupAlgebra

variable (k G : Type*) [Field k] [Finite G]

/-- The group algebra of a finite group has dimension the order of the group. -/
theorem finrank_monoidAlgebra : Module.finrank k (MonoidAlgebra k G) = Nat.card G := by
  letI := Fintype.ofFinite G
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G k), Fintype.card_eq_nat_card]

variable [Group G]
variable {k G}

/-- **The sum of the squares of the block degrees is the order of the group**: both sides compute
the dimension of `k[G]`. -/
theorem sum_sq_eq_card_of_algEquiv_pi_matrix {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    ∑ i, d i ^ 2 = Nat.card G :=
  calc ∑ i, d i ^ 2
      = Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) := (finrank_pi_matrix k d).symm
    _ = Module.finrank k (MonoidAlgebra k G) := e.toLinearEquiv.finrank_eq.symm
    _ = Nat.card G := finrank_monoidAlgebra k G

/-- **The center of the group algebra splits**: a Wedderburn presentation of `k[G]` with `n` blocks
identifies `Z(k[G])` with `k ^ n`. -/
noncomputable def centerMonoidAlgebraAlgEquivPi {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (e : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (Fin n → k) :=
  (centerCongr e).trans (centerPiMatrixAlgEquiv k d)

/-- **The number of Wedderburn blocks of `k[G]` is the number of conjugacy classes of `G`**: both
sides compute the dimension of `Z(k[G])`.

This is the numerical half of the count `#irreducibles = #conjugacy classes`; identifying the blocks
with the isomorphism classes of simple `k[G]`-modules is a separate statement. -/
theorem card_eq_card_conjClasses_of_algEquiv_pi_matrix {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (e : MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    n = Nat.card (ConjClasses G) :=
  calc n = Module.finrank k (Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) :=
        (finrank_center_pi_matrix k d).symm
    _ = Module.finrank k (Subalgebra.center k (MonoidAlgebra k G)) :=
        (centerCongr e).toLinearEquiv.finrank_eq.symm
    _ = Nat.card (ConjClasses G) := finrank_center_monoidAlgebra k G

variable (k G) [NeZero (Nat.card G : k)] [IsAlgClosed k]

/-- **Maschke and Artin--Wedderburn for a finite group algebra**: over an algebraically closed field
whose characteristic does not divide `|G|`, the group algebra is a finite product of matrix algebras
of positive size. -/
theorem exists_algEquiv_pi_matrix :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (MonoidAlgebra k G)

/-- The Wedderburn decomposition of `k[G]`, indexed by the conjugacy classes of `G`, with the
degrees squaring to a sum of `|G|`. -/
theorem exists_algEquiv_pi_matrix_conjClasses :
    ∃ d : Fin (Nat.card (ConjClasses G)) → ℕ, (∀ i, NeZero (d i)) ∧ ∑ i, d i ^ 2 = Nat.card G ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix k G
  haveI := hd
  obtain rfl : n = Nat.card (ConjClasses G) := card_eq_card_conjClasses_of_algEquiv_pi_matrix e
  exact ⟨d, hd, sum_sq_eq_card_of_algEquiv_pi_matrix e, ⟨e⟩⟩

end GroupAlgebra

end TauCeti
