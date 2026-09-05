/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.KostantLattice

/-!
# The graph automorphism of the type-`D` spin representation

The Dynkin diagram `Dₙ` has the symmetry that exchanges its two fork nodes, and it is the source
of the twisted family `²Dₙ(q)`. On the split orthogonal Lie algebra that symmetry is conjugation
by an orthogonal transformation of determinant `-1`, and on the spinor module it is therefore
realized by an element of the Clifford algebra rather than of its even part. This file exhibits
that element and proves the intertwining relations it satisfies.

The vector is `TauCeti.SpinPolarizationData.typeDGraphVector`,

```text
v = b_{n-1} - b'_{n-1},
```

the difference of the last basis vector of the first isotropic summand and its polar dual in the
second. It has `Q v = -1`, so `ι v` squares to `-1` in the Clifford algebra and the reflection in
`v` exchanges `b_{n-1}` with `b'_{n-1}` and fixes every other basis or dual basis vector. Since
conjugation by `ι v` is that reflection up to a sign on each generator, and the type-`D` root
representatives of `TauCeti/RepresentationTheory/Spin/Polarization/TypeD/RootBivectors.lean` are
products of two generators, the two signs cancel on each of them and `ι v` intertwines the
representative at a node with the representative at the node's image under
`TauCeti.graphPermD`. That holds for the positive representatives, the negative ones, and the
coroots alike, so the fork exchange is realized uniformly on the whole pinned Serre system rather
than only on the raising operators.

On the spinor module the resulting operator is
`TauCeti.SpinPolarizationData.typeDGraphOperator`: the spin action of `ι v`, that is creation at
the last coordinate minus annihilation at it. It squares to `-1`, hence is invertible, and it
preserves the coordinate integral lattice in both directions because creation and annihilation
operators do.

Nothing here builds a group, a group scheme, or an automorphism of one. What the numbered-symmetry
machinery of
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Scheme/NumberedSymmetry.lean`
consumes is a lattice-preserving linear automorphism of the representation intertwining the
numbered generators along a permutation of their index, and the last section supplies exactly that
datum for the type-`D` spin representation and the permutation `TauCeti.graphPermD`.

## Main definitions

* `TauCeti.SpinPolarizationData.typeDGraphVector`: the anisotropic vector whose reflection
  exchanges the two fork nodes of `Dₙ`.
* `TauCeti.SpinPolarizationData.typeDGraphOperator`: its spin action on the spinor module, as a
  linear equivalence.

## Main results

* `TauCeti.SpinPolarizationData.quadraticForm_typeDGraphVector` and
  `TauCeti.SpinPolarizationData.ι_typeDGraphVector_mul_self`: the graph vector has quadratic norm
  `-1`, so its Clifford generator squares to `-1`.
* `TauCeti.SpinPolarizationData.ι_typeDGraphVector_mul_typeDSimpleRootBivector`, its negative
  counterpart, and
  `TauCeti.SpinPolarizationData.ι_typeDGraphVector_mul_typeDSimpleCorootBivector`: the Clifford
  generator of the graph vector intertwines the numbered type-`D` representatives along
  `TauCeti.graphPermD`.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_eq_wedge_sub_contract`: the operator is
  creation at the last coordinate minus annihilation at it.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_typeDGraphOperator`: it squares to `-1`.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_spinAction_typeDSimpleRootBivector`, its
  negative counterpart, and
  `TauCeti.SpinPolarizationData.typeDGraphOperator_spinAction_typeDSimpleCorootBivector`: the same
  renumbering, read on the spinor module.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_mem_integralLattice_iff`: it preserves the
  coordinate integral lattice, in both directions.
* `TauCeti.SpinPolarizationData.typeDGraphOperator_typeDSpinRep_rootGenerator`: the intertwining
  relation for the numbered generators of the rational type-`D` Serre representation.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spinor model and the
  action of the Clifford generators on it.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15, for
  the graph automorphism of a pinned group of Lie type.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV, for the numbering of the
  `Dₙ` diagram whose last two nodes the symmetry exchanges.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.SpinPolarizationData

universe u v

section CommRing

variable {K : Type u} [CommRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
variable {n : ℕ} (b : Module.Basis (Fin n) K P.W)

/-! ## The graph vector -/

/-- **The vector whose reflection exchanges the two fork nodes of `Dₙ`**: the difference of the
last basis vector of the first isotropic summand and its polar dual in the second. Its quadratic
norm is `-1`, and the reflection in it exchanges those two vectors while fixing every other basis
and dual basis vector, which is the coordinate description of the diagram symmetry. -/
noncomputable def typeDGraphVector (hn : 2 ≤ n) : V :=
  (b ⟨n - 1, by omega⟩ : V) - (P.dualVector b ⟨n - 1, by omega⟩ : V)

/-- The defining difference of the type-`D` graph vector. -/
theorem typeDGraphVector_def (hn : 2 ≤ n) :
    P.typeDGraphVector b hn =
      (b ⟨n - 1, by omega⟩ : V) - (P.dualVector b ⟨n - 1, by omega⟩ : V) :=
  -- `(rfl)`, not `rfl`: the body of `typeDGraphVector` is not `@[expose]`d.
  (rfl)

/-- The graph vector is orthogonal to every basis vector other than the last. -/
theorem isOrtho_typeDGraphVector_basis_of_ne (hn : 2 ≤ n) {j : Fin n} (hj : (j : ℕ) ≠ n - 1) :
    Q.IsOrtho (P.typeDGraphVector b hn) (b j : V) := by
  rw [← isOrtho_polarBilin, polarBilin_apply_apply, typeDGraphVector_def, polar_comm,
    polar_sub_right, P.polar_W_eq_zero, P.polar_dualVector]
  simp only [Fin.ext_iff, zero_sub, neg_eq_zero, ite_eq_right_iff]
  omega

/-- The graph vector pairs with the last basis vector to `-1`. -/
theorem polar_typeDGraphVector_basis_last (hn : 2 ≤ n) :
    polar Q (P.typeDGraphVector b hn) (b ⟨n - 1, by omega⟩ : V) = -1 := by
  rw [typeDGraphVector_def, polar_comm, polar_sub_right, P.polar_W_eq_zero,
    P.polar_dualVector_self]
  ring

/-- The graph vector is orthogonal to every dual basis vector other than the last. -/
theorem isOrtho_typeDGraphVector_dualVector_of_ne (hn : 2 ≤ n) {j : Fin n}
    (hj : (j : ℕ) ≠ n - 1) : Q.IsOrtho (P.typeDGraphVector b hn) (P.dualVector b j : V) := by
  rw [← isOrtho_polarBilin, polarBilin_apply_apply, typeDGraphVector_def, polar_sub_left,
    P.polar_W'_eq_zero, P.polar_dualVector]
  simp only [Fin.ext_iff, sub_zero, ite_eq_right_iff]
  omega

/-- The graph vector pairs with the last dual basis vector to `1`. -/
theorem polar_typeDGraphVector_dualVector_last (hn : 2 ≤ n) :
    polar Q (P.typeDGraphVector b hn) (P.dualVector b ⟨n - 1, by omega⟩ : V) = 1 := by
  rw [typeDGraphVector_def, polar_sub_left, P.polar_W'_eq_zero, P.polar_dualVector_self]
  ring

/-- **The graph vector is anisotropic of norm `-1`.** Both summands are isotropic, so the norm is
the negative of the pairing of a basis vector with its own polar dual. -/
@[simp]
theorem quadraticForm_typeDGraphVector (hn : 2 ≤ n) : Q (P.typeDGraphVector b hn) = -1 := by
  rw [typeDGraphVector_def, sub_eq_add_neg, QuadraticMap.map_add Q, P.isotropic_W,
    QuadraticMap.map_neg, P.isotropic_W', polar_neg_right, P.polar_dualVector_self]
  ring

/-- The Clifford generator of the graph vector squares to `-1`. This is not `@[simp]`: `simp`
already closes it from `CliffordAlgebra.ι_sq_scalar` and `quadraticForm_typeDGraphVector`. -/
theorem ι_typeDGraphVector_mul_self (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) * ι Q (P.typeDGraphVector b hn) = -1 := by
  rw [ι_sq_scalar, quadraticForm_typeDGraphVector, map_neg, map_one]

/-! ## Conjugation is the fork reflection -/

/-- Conjugating a Clifford generator by the graph generator is the reflection in the graph vector,
up to the sign that twisted conjugation carries on a vector.

The map `m ↦ m + polar Q v m • v` appearing here is `TauCeti.QuadraticMap.reflection Q v` at a
vector of norm `-1`, which is the same map that `CliffordAlgebra.pinToOrthogonal_ι_apply` computes
as the twisted-conjugation action of `ι v`. It is derived here from the Clifford relation instead
of from the Pin group, because that route needs `2` invertible in the base ring while the type-`D`
representatives below are stated over an arbitrary commutative ring. -/
private theorem ι_typeDGraphVector_mul_ι (hn : 2 ≤ n) (u : V) :
    ι Q (P.typeDGraphVector b hn) * ι Q u =
      -(ι Q (u + polar Q (P.typeDGraphVector b hn) u • P.typeDGraphVector b hn) *
        ι Q (P.typeDGraphVector b hn)) := by
  rw [map_add, map_smul, add_mul, smul_mul_assoc, ι_typeDGraphVector_mul_self,
    ι_mul_ι_comm (Q := Q), Algebra.algebraMap_eq_smul_one]
  module

/-- Conjugation carries the last basis vector to its polar dual. -/
private theorem ι_typeDGraphVector_mul_ι_basis_last (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) * ι Q (b ⟨n - 1, by omega⟩ : V) =
      -(ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) * ι Q (P.typeDGraphVector b hn)) := by
  have hreflect : (b ⟨n - 1, by omega⟩ : V) +
      polar Q (P.typeDGraphVector b hn) (b ⟨n - 1, by omega⟩ : V) • P.typeDGraphVector b hn =
      (P.dualVector b ⟨n - 1, by omega⟩ : V) := by
    rw [polar_typeDGraphVector_basis_last, typeDGraphVector_def]
    module
  rw [P.ι_typeDGraphVector_mul_ι b hn _, hreflect]

/-- Conjugation carries the last dual basis vector to the last basis vector. -/
private theorem ι_typeDGraphVector_mul_ι_dualVector_last (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) =
      -(ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.typeDGraphVector b hn)) := by
  have hreflect : (P.dualVector b ⟨n - 1, by omega⟩ : V) +
      polar Q (P.typeDGraphVector b hn) (P.dualVector b ⟨n - 1, by omega⟩ : V) •
        P.typeDGraphVector b hn = (b ⟨n - 1, by omega⟩ : V) := by
    rw [polar_typeDGraphVector_dualVector_last, typeDGraphVector_def]
    module
  rw [P.ι_typeDGraphVector_mul_ι b hn _, hreflect]

/-- The two signs of the generator conjugation cancel on a product of two generators. -/
private theorem ι_typeDGraphVector_mul_ι_mul_ι (hn : 2 ≤ n) {x y x' y' : V}
    (hx : ι Q (P.typeDGraphVector b hn) * ι Q x = -(ι Q x' * ι Q (P.typeDGraphVector b hn)))
    (hy : ι Q (P.typeDGraphVector b hn) * ι Q y = -(ι Q y' * ι Q (P.typeDGraphVector b hn))) :
    ι Q (P.typeDGraphVector b hn) * (ι Q x * ι Q y) =
      ι Q x' * ι Q y' * ι Q (P.typeDGraphVector b hn) := by
  rw [← mul_assoc, hx, neg_mul, mul_assoc, hy, mul_neg, neg_neg, ← mul_assoc]

/-! ## The fork exchange on the numbered representatives -/

/-- A positive representative at a chain node, in the raw Clifford form. -/
private theorem typeDSimpleRootBivector_of_chain (hn : 2 ≤ n) {i j : Fin n}
    (h : (i : ℕ) + 1 < n) (hj : (j : ℕ) = (i : ℕ) + 1) :
    P.typeDSimpleRootBivector b hn i = ι Q (b i : V) * ι Q (P.dualVector b j : V) := by
  have hij : (⟨(i : ℕ) + 1, h⟩ : Fin n) = j := Fin.ext hj.symm
  rw [typeDSimpleRootBivector_def, dite_eq_left h, hij]

/-- The positive representative at the fork node, in the raw Clifford form. -/
private theorem typeDSimpleRootBivector_of_fork (hn : 2 ≤ n) {i : Fin n}
    (h : ¬(i : ℕ) + 1 < n) :
    P.typeDSimpleRootBivector b hn i =
      ι Q (b ⟨n - 2, by omega⟩ : V) * ι Q (b ⟨n - 1, by omega⟩ : V) := by
  rw [typeDSimpleRootBivector_def, dite_eq_right h]

/-- A negative representative at a chain node, in the raw Clifford form. -/
private theorem typeDSimpleNegativeRootBivector_of_chain (hn : 2 ≤ n) {i j : Fin n}
    (h : (i : ℕ) + 1 < n) (hj : (j : ℕ) = (i : ℕ) + 1) :
    P.typeDSimpleNegativeRootBivector b hn i = ι Q (b j : V) * ι Q (P.dualVector b i : V) := by
  have hij : (⟨(i : ℕ) + 1, h⟩ : Fin n) = j := Fin.ext hj.symm
  rw [typeDSimpleNegativeRootBivector_def, dite_eq_left h, hij]

/-- The negative representative at the fork node, in the raw Clifford form. -/
private theorem typeDSimpleNegativeRootBivector_of_fork (hn : 2 ≤ n) {i : Fin n}
    (h : ¬(i : ℕ) + 1 < n) :
    P.typeDSimpleNegativeRootBivector b hn i =
      ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) *
        ι Q (P.dualVector b ⟨n - 2, by omega⟩ : V) := by
  rw [typeDSimpleNegativeRootBivector_def, dite_eq_right h]

/-- A coroot representative at a chain node, in the raw Clifford form. -/
private theorem typeDSimpleCorootBivector_of_chain (hn : 2 ≤ n) {i j : Fin n}
    (h : (i : ℕ) + 1 < n) (hj : (j : ℕ) = (i : ℕ) + 1) :
    P.typeDSimpleCorootBivector b hn i =
      ι Q (b i : V) * ι Q (P.dualVector b i : V) -
        ι Q (b j : V) * ι Q (P.dualVector b j : V) := by
  have hij : (⟨(i : ℕ) + 1, h⟩ : Fin n) = j := Fin.ext hj.symm
  rw [typeDSimpleCorootBivector_def, dite_eq_left h, hij]

/-- The coroot representative at the fork node, in the raw Clifford form. -/
private theorem typeDSimpleCorootBivector_of_fork (hn : 2 ≤ n) {i : Fin n}
    (h : ¬(i : ℕ) + 1 < n) :
    P.typeDSimpleCorootBivector b hn i =
      ι Q (b ⟨n - 2, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 2, by omega⟩ : V) +
        ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) - 1 := by
  rw [typeDSimpleCorootBivector_def, dite_eq_right h]

/-- The occupation product at a node other than the last commutes with the graph generator. -/
private theorem ι_typeDGraphVector_mul_occupation_of_ne (hn : 2 ≤ n) {j : Fin n}
    (hj : (j : ℕ) ≠ n - 1) :
    ι Q (P.typeDGraphVector b hn) * (ι Q (b j : V) * ι Q (P.dualVector b j : V)) =
      ι Q (b j : V) * ι Q (P.dualVector b j : V) * ι Q (P.typeDGraphVector b hn) :=
  P.ι_typeDGraphVector_mul_ι_mul_ι b hn
    (ι_mul_ι_comm_of_isOrtho (P.isOrtho_typeDGraphVector_basis_of_ne b hn hj))
    (ι_mul_ι_comm_of_isOrtho (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn hj))

/-- Conjugating the occupation product at the last node reverses it, and reversing it subtracts it
from `1`. -/
private theorem ι_typeDGraphVector_mul_occupation_last (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) *
        (ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V)) =
      (1 - ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V)) *
        ι Q (P.typeDGraphVector b hn) := by
  have hswap : ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) * ι Q (b ⟨n - 1, by omega⟩ : V) =
      1 - ι Q (b ⟨n - 1, by omega⟩ : V) * ι Q (P.dualVector b ⟨n - 1, by omega⟩ : V) := by
    rw [ι_mul_ι_comm (Q := Q), polar_comm, P.polar_dualVector_self, map_one]
  rw [← hswap]
  exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
    (P.ι_typeDGraphVector_mul_ι_basis_last b hn)
    (P.ι_typeDGraphVector_mul_ι_dualVector_last b hn)

/-- The graph permutation sends the fork node to the penultimate node. -/
private theorem graphPermD_of_val_eq_last (hn : 2 ≤ n) {i : Fin n} (hi : (i : ℕ) = n - 1) :
    graphPermD n hn i = (⟨n - 2, by omega⟩ : Fin n) := by
  have hlast : i = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext hi
  rw [hlast]
  exact graphPermD_apply_right n hn

/-- The graph permutation sends the penultimate node to the fork node. -/
private theorem graphPermD_of_val_eq_penultimate (hn : 2 ≤ n) {i : Fin n} (hi : (i : ℕ) = n - 2) :
    graphPermD n hn i = (⟨n - 1, by omega⟩ : Fin n) := by
  have hpenultimate : i = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext hi
  rw [hpenultimate]
  exact graphPermD_apply_left n hn

/-- The basis vector at a node known only through its value `n - 2`. The fork branches of the
proofs below meet the penultimate node as the value equation `(i : ℕ) = n - 2` rather than as an
index, so the equation has to be transported through `b` and the inclusion of the isotropic
summand before it can rewrite the goal. -/
private theorem basis_coe_of_val_eq_penultimate {i : Fin n} (hi : (i : ℕ) = n - 2) :
    (b i : V) = (b ⟨n - 2, by omega⟩ : V) :=
  congrArg _ (congrArg b (Fin.ext hi))

/-- The dual basis vector at a node known only through its value `n - 2`, the polar-dual
counterpart of `basis_coe_of_val_eq_penultimate`. -/
private theorem dualVector_coe_of_val_eq_penultimate {i : Fin n} (hi : (i : ℕ) = n - 2) :
    (P.dualVector b i : V) = (P.dualVector b ⟨n - 2, by omega⟩ : V) :=
  congrArg _ (congrArg (P.dualVector b) (Fin.ext hi))

/-- **The graph generator exchanges the two fork raising operators** and commutes with the others:
multiplying the positive type-`D` representative at a node by the Clifford generator of the graph
vector renumbers that representative by `TauCeti.graphPermD`. -/
theorem ι_typeDGraphVector_mul_typeDSimpleRootBivector (hn : 2 ≤ n) (i : Fin n) :
    ι Q (P.typeDGraphVector b hn) * P.typeDSimpleRootBivector b hn i =
      P.typeDSimpleRootBivector b hn (graphPermD n hn i) * ι Q (P.typeDGraphVector b hn) := by
  by_cases hfork : (i : ℕ) = n - 1
  · rw [P.typeDSimpleRootBivector_of_fork b hn (by omega),
      graphPermD_of_val_eq_last hn hfork,
      P.typeDSimpleRootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩)
        (show n - 2 + 1 < n by omega) (show n - 1 = n - 2 + 1 by omega)]
    exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
      (ι_mul_ι_comm_of_isOrtho
        (P.isOrtho_typeDGraphVector_basis_of_ne b hn (show n - 2 ≠ n - 1 by omega)))
      (P.ι_typeDGraphVector_mul_ι_basis_last b hn)
  · by_cases hpen : (i : ℕ) = n - 2
    · rw [P.typeDSimpleRootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩) (by omega)
          (show n - 1 = (i : ℕ) + 1 by omega),
        graphPermD_of_val_eq_penultimate hn hpen,
        P.typeDSimpleRootBivector_of_fork b hn (show ¬n - 1 + 1 < n by omega),
        P.basis_coe_of_val_eq_penultimate b hpen]
      exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
        (ι_mul_ι_comm_of_isOrtho
          (P.isOrtho_typeDGraphVector_basis_of_ne b hn (show n - 2 ≠ n - 1 by omega)))
        (P.ι_typeDGraphVector_mul_ι_dualVector_last b hn)
    · have hnext : (i : ℕ) + 1 < n := by omega
      rw [P.typeDSimpleRootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl,
        graphPermD_apply_of_ne_of_ne n hn i hpen hfork,
        P.typeDSimpleRootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl]
      exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
        (ι_mul_ι_comm_of_isOrtho (P.isOrtho_typeDGraphVector_basis_of_ne b hn hfork))
        (ι_mul_ι_comm_of_isOrtho
          (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn (show (i : ℕ) + 1 ≠ n - 1 by omega)))

/-- **The graph generator exchanges the two fork lowering operators** and commutes with the
others. -/
theorem ι_typeDGraphVector_mul_typeDSimpleNegativeRootBivector (hn : 2 ≤ n) (i : Fin n) :
    ι Q (P.typeDGraphVector b hn) * P.typeDSimpleNegativeRootBivector b hn i =
      P.typeDSimpleNegativeRootBivector b hn (graphPermD n hn i) *
        ι Q (P.typeDGraphVector b hn) := by
  by_cases hfork : (i : ℕ) = n - 1
  · rw [P.typeDSimpleNegativeRootBivector_of_fork b hn (by omega),
      graphPermD_of_val_eq_last hn hfork,
      P.typeDSimpleNegativeRootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩)
        (show n - 2 + 1 < n by omega) (show n - 1 = n - 2 + 1 by omega)]
    exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
      (P.ι_typeDGraphVector_mul_ι_dualVector_last b hn)
      (ι_mul_ι_comm_of_isOrtho
        (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn (show n - 2 ≠ n - 1 by omega)))
  · by_cases hpen : (i : ℕ) = n - 2
    · rw [P.typeDSimpleNegativeRootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩) (by omega)
          (show n - 1 = (i : ℕ) + 1 by omega),
        graphPermD_of_val_eq_penultimate hn hpen,
        P.typeDSimpleNegativeRootBivector_of_fork b hn (show ¬n - 1 + 1 < n by omega),
        P.dualVector_coe_of_val_eq_penultimate b hpen]
      exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
        (P.ι_typeDGraphVector_mul_ι_basis_last b hn)
        (ι_mul_ι_comm_of_isOrtho
          (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn (show n - 2 ≠ n - 1 by omega)))
    · have hnext : (i : ℕ) + 1 < n := by omega
      rw [P.typeDSimpleNegativeRootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl,
        graphPermD_apply_of_ne_of_ne n hn i hpen hfork,
        P.typeDSimpleNegativeRootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl]
      exact P.ι_typeDGraphVector_mul_ι_mul_ι b hn
        (ι_mul_ι_comm_of_isOrtho
          (P.isOrtho_typeDGraphVector_basis_of_ne b hn (show (i : ℕ) + 1 ≠ n - 1 by omega)))
        (ι_mul_ι_comm_of_isOrtho (P.isOrtho_typeDGraphVector_dualVector_of_ne b hn hfork))

/-- **The graph generator exchanges the two fork coroots** and commutes with the others. The two
fork coroots differ by the reversal of the occupation product at the last node, which is what
turns the difference of the last two occupation products into their sum less `1`. -/
theorem ι_typeDGraphVector_mul_typeDSimpleCorootBivector (hn : 2 ≤ n) (i : Fin n) :
    ι Q (P.typeDGraphVector b hn) * P.typeDSimpleCorootBivector b hn i =
      P.typeDSimpleCorootBivector b hn (graphPermD n hn i) * ι Q (P.typeDGraphVector b hn) := by
  by_cases hfork : (i : ℕ) = n - 1
  · rw [P.typeDSimpleCorootBivector_of_fork b hn (by omega),
      graphPermD_of_val_eq_last hn hfork,
      P.typeDSimpleCorootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩)
        (show n - 2 + 1 < n by omega) (show n - 1 = n - 2 + 1 by omega),
      mul_sub, mul_one, mul_add,
      P.ι_typeDGraphVector_mul_occupation_of_ne b hn (show n - 2 ≠ n - 1 by omega),
      P.ι_typeDGraphVector_mul_occupation_last b hn]
    noncomm_ring
  · by_cases hpen : (i : ℕ) = n - 2
    · rw [P.typeDSimpleCorootBivector_of_chain b hn (j := ⟨n - 1, by omega⟩) (by omega)
          (show n - 1 = (i : ℕ) + 1 by omega),
        graphPermD_of_val_eq_penultimate hn hpen,
        P.typeDSimpleCorootBivector_of_fork b hn (show ¬n - 1 + 1 < n by omega),
        P.basis_coe_of_val_eq_penultimate b hpen,
        P.dualVector_coe_of_val_eq_penultimate b hpen, mul_sub,
        P.ι_typeDGraphVector_mul_occupation_of_ne b hn (show n - 2 ≠ n - 1 by omega),
        P.ι_typeDGraphVector_mul_occupation_last b hn]
      noncomm_ring
    · have hnext : (i : ℕ) + 1 < n := by omega
      rw [P.typeDSimpleCorootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl,
        graphPermD_apply_of_ne_of_ne n hn i hpen hfork,
        P.typeDSimpleCorootBivector_of_chain b hn (j := ⟨(i : ℕ) + 1, hnext⟩) hnext rfl,
        mul_sub, P.ι_typeDGraphVector_mul_occupation_of_ne b hn hfork,
        P.ι_typeDGraphVector_mul_occupation_of_ne b hn (show (i : ℕ) + 1 ≠ n - 1 by omega)]
      noncomm_ring


/-! ## The graph operator on the spinor module -/

/-- The spin action of the graph generator squares to `-1`. -/
private theorem spinAction_ι_typeDGraphVector_mul_self (hn : 2 ≤ n) :
    spinAction Q P (ι Q (P.typeDGraphVector b hn)) *
        spinAction Q P (ι Q (P.typeDGraphVector b hn)) = -1 := by
  rw [← map_mul, ι_typeDGraphVector_mul_self, map_neg, map_one]

/-- **The graph operator of the type-`D` spinor module**: the spin action of the Clifford
generator of the graph vector, that is creation at the last coordinate minus annihilation at it.
It squares to `-1`, hence is a linear equivalence with `-` itself as inverse. -/
noncomputable def typeDGraphOperator (hn : 2 ≤ n) :
    ExteriorAlgebra K P.W ≃ₗ[K] ExteriorAlgebra K P.W :=
  LinearEquiv.ofLinearMap (spinAction Q P (ι Q (P.typeDGraphVector b hn)))
    (-spinAction Q P (ι Q (P.typeDGraphVector b hn)))
    (by
      rw [LinearMap.comp_neg, ← Module.End.mul_eq_comp,
        P.spinAction_ι_typeDGraphVector_mul_self b hn, neg_neg]
      rfl)
    (by
      rw [LinearMap.neg_comp, ← Module.End.mul_eq_comp,
        P.spinAction_ι_typeDGraphVector_mul_self b hn, neg_neg]
      rfl)

/-- The graph operator acts by the spin action of the graph generator. This is not `@[simp]`: the
spin action of the graph generator is the implementation, and the equations below are the intended
normal forms. -/
theorem typeDGraphOperator_apply (hn : 2 ≤ n) (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn x = spinAction Q P (ι Q (P.typeDGraphVector b hn)) x :=
  -- `(rfl)`, not `rfl`: the body of `typeDGraphOperator` is not `@[expose]`d.
  (rfl)

/-- **The graph operator is creation at the last coordinate minus annihilation at it.** This is
the Fock-model description of the spin action of the graph generator. It is not `@[simp]`:
unfolding the operator into the Fock model takes `typeDGraphOperator_typeDGraphOperator` and
`typeDGraphOperator_symm_apply`, which are the intended normal forms, out of simp normal form. -/
theorem typeDGraphOperator_eq_wedge_sub_contract (hn : 2 ≤ n) (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn x =
      P.wedge (b ⟨n - 1, by omega⟩) x - P.contract (P.dualVector b ⟨n - 1, by omega⟩) x := by
  rw [typeDGraphOperator_apply, typeDGraphVector_def, map_sub, map_sub, LinearMap.sub_apply,
    spinAction_ι, spinAction_ι, P.cliffordOperator_coe_W, P.cliffordOperator_coe_W']

/-- The graph operator squares to `-1`. -/
@[simp]
theorem typeDGraphOperator_typeDGraphOperator (hn : 2 ≤ n) (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (P.typeDGraphOperator b hn x) = -x := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, ← Module.End.mul_apply,
    P.spinAction_ι_typeDGraphVector_mul_self b hn]
  simp

/-- The inverse of the graph operator is its negative. -/
@[simp]
theorem typeDGraphOperator_symm_apply (hn : 2 ≤ n) (x : ExteriorAlgebra K P.W) :
    (P.typeDGraphOperator b hn).symm x = -P.typeDGraphOperator b hn x :=
  (P.typeDGraphOperator b hn).symm_apply_eq.2 (by
    rw [map_neg, typeDGraphOperator_typeDGraphOperator, neg_neg])

/-- **The graph operator intertwines the numbered raising operators along `TauCeti.graphPermD`.**
-/
theorem typeDGraphOperator_spinAction_typeDSimpleRootBivector (hn : 2 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (spinAction Q P (P.typeDSimpleRootBivector b hn i) x) =
      spinAction Q P (P.typeDSimpleRootBivector b hn (graphPermD n hn i))
        (P.typeDGraphOperator b hn x) := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    P.ι_typeDGraphVector_mul_typeDSimpleRootBivector b hn i]

/-- **The graph operator intertwines the numbered lowering operators along `TauCeti.graphPermD`.**
-/
theorem typeDGraphOperator_spinAction_typeDSimpleNegativeRootBivector (hn : 2 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (spinAction Q P (P.typeDSimpleNegativeRootBivector b hn i) x) =
      spinAction Q P (P.typeDSimpleNegativeRootBivector b hn (graphPermD n hn i))
        (P.typeDGraphOperator b hn x) := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    P.ι_typeDGraphVector_mul_typeDSimpleNegativeRootBivector b hn i]

/-- **The graph operator intertwines the numbered coroots along `TauCeti.graphPermD`.** -/
theorem typeDGraphOperator_spinAction_typeDSimpleCorootBivector (hn : 2 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra K P.W) :
    P.typeDGraphOperator b hn (spinAction Q P (P.typeDSimpleCorootBivector b hn i) x) =
      spinAction Q P (P.typeDSimpleCorootBivector b hn (graphPermD n hn i))
        (P.typeDGraphOperator b hn x) := by
  rw [typeDGraphOperator_apply, typeDGraphOperator_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    P.ι_typeDGraphVector_mul_typeDSimpleCorootBivector b hn i]

end CommRing

/-! ## Integrality and the rational Serre representation -/

section Rat

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) {n : ℕ} (b : Module.Basis (Fin n) ℚ P.W)

/-- The graph generator acts integrally on the spinor lattice: it is the difference of a creation
and an annihilation operator, and both are integral. -/
theorem ι_typeDGraphVector_mem_integralSpinActionSubring (hn : 2 ≤ n) :
    ι Q (P.typeDGraphVector b hn) ∈ P.integralSpinActionSubring b := by
  rw [typeDGraphVector_def, map_sub]
  exact sub_mem (P.ι_basis_mem_integralSpinActionSubring b _)
    (P.ι_dualVector_mem_integralSpinActionSubring b _)

/-- The graph operator preserves the coordinate integral lattice in the spinor module. -/
theorem typeDGraphOperator_mem_integralLattice (hn : 2 ≤ n) {x : ExteriorAlgebra ℚ P.W}
    (hx : x ∈ TauCeti.ExteriorAlgebra.integralLattice b) :
    P.typeDGraphOperator b hn x ∈ TauCeti.ExteriorAlgebra.integralLattice b := by
  rw [typeDGraphOperator_apply]
  exact (P.mem_integralSpinActionSubring b).mp
    (P.ι_typeDGraphVector_mem_integralSpinActionSubring b hn) hx

/-- **The graph operator preserves the spinor lattice in both directions**, since its square is
`-1` and the lattice is a subgroup. This is the lattice-invariance datum that the numbered-symmetry
construction of a Chevalley--Demazure carrier consumes. It is not `@[simp]`:
`TauCeti.ExteriorAlgebra.mem_integralLattice_iff` is, and rewrites the membership into its
coordinate form, so this left-hand side is not in simp normal form. -/
theorem typeDGraphOperator_mem_integralLattice_iff (hn : 2 ≤ n) {x : ExteriorAlgebra ℚ P.W} :
    P.typeDGraphOperator b hn x ∈ TauCeti.ExteriorAlgebra.integralLattice b ↔
      x ∈ TauCeti.ExteriorAlgebra.integralLattice b := by
  refine ⟨fun hx => ?_, P.typeDGraphOperator_mem_integralLattice b hn⟩
  have hsq := P.typeDGraphOperator_mem_integralLattice b hn hx
  rw [typeDGraphOperator_typeDGraphOperator] at hsq
  exact neg_mem_iff.mp hsq

/-- The graph operator intertwines the represented positive Serre generators along
`TauCeti.graphPermD`. -/
theorem typeDGraphOperator_typeDSpinRep_serreE (hn : 4 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra ℚ P.W) :
    P.typeDGraphOperator b (by omega)
        (P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreE ℚ (CartanMatrix.D n) i)) x) =
      P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreE ℚ (CartanMatrix.D n) (graphPermD n (by omega) i)))
        (P.typeDGraphOperator b (by omega) x) := by
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinRep_ι b hn,
    P.typeDSpinSerreRepresentation_serreE b hn, P.typeDSpinSerreRepresentation_serreE b hn]
  exact P.typeDGraphOperator_spinAction_typeDSimpleRootBivector b (by omega) i x

/-- The graph operator intertwines the represented negative Serre generators along
`TauCeti.graphPermD`. -/
theorem typeDGraphOperator_typeDSpinRep_serreF (hn : 4 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra ℚ P.W) :
    P.typeDGraphOperator b (by omega)
        (P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreF ℚ (CartanMatrix.D n) i)) x) =
      P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreF ℚ (CartanMatrix.D n) (graphPermD n (by omega) i)))
        (P.typeDGraphOperator b (by omega) x) := by
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinRep_ι b hn,
    P.typeDSpinSerreRepresentation_serreF b hn, P.typeDSpinSerreRepresentation_serreF b hn]
  exact P.typeDGraphOperator_spinAction_typeDSimpleNegativeRootBivector b (by omega) i x

/-- The graph operator intertwines the represented Cartan generators along
`TauCeti.graphPermD`. -/
theorem typeDGraphOperator_typeDSpinRep_serreH (hn : 4 ≤ n) (i : Fin n)
    (x : ExteriorAlgebra ℚ P.W) :
    P.typeDGraphOperator b (by omega)
        (P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreH ℚ (CartanMatrix.D n) i)) x) =
      P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreH ℚ (CartanMatrix.D n) (graphPermD n (by omega) i)))
        (P.typeDGraphOperator b (by omega) x) := by
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinRep_ι b hn,
    P.typeDSpinSerreRepresentation_serreH b hn, P.typeDSpinSerreRepresentation_serreH b hn]
  exact P.typeDGraphOperator_spinAction_typeDSimpleCorootBivector b (by omega) i x

/-- **The intertwining datum of the type-`D` fork symmetry.** The graph operator carries the
action of the numbered root generator at `k` to the action of the one at the image of `k` under
the fork exchange, on both the raising and the lowering half of the numbering. Together with
`TauCeti.SpinPolarizationData.typeDGraphOperator_mem_integralLattice_iff` this is exactly the
symmetry datum a numbered Kostant carrier consumes. -/
theorem typeDGraphOperator_typeDSpinRep_rootGenerator (hn : 4 ≤ n) (k : Fin n ⊕ Fin n)
    (x : ExteriorAlgebra ℚ P.W) :
    P.typeDGraphOperator b (by omega)
        (P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.D n) k)) x) =
      P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator (CartanMatrix.D n)
            (Sum.map (graphPermD n (by omega)) (graphPermD n (by omega)) k)))
        (P.typeDGraphOperator b (by omega) x) := by
  cases k with
  | inl i =>
      rw [Sum.map_inl, TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inl]
      exact P.typeDGraphOperator_typeDSpinRep_serreE b hn i x
  | inr i =>
      rw [Sum.map_inr, TauCeti.serreRootGenerator_inr, TauCeti.serreRootGenerator_inr]
      exact P.typeDGraphOperator_typeDSpinRep_serreF b hn i x

end Rat

end TauCeti.SpinPolarizationData

