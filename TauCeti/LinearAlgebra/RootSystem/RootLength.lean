/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

/-!
# Long and short simple roots of a Dynkin type

A Cartan matrix records more than an unoriented diagram: the ratio of a transposed pair of its
off-diagonal entries is the ratio of the squared lengths of the two simple roots. This file reads
that information off the standard Cartan matrices of `TauCeti.DynkinType`, pinning for each type
which of its nodes carry long simple roots and which carry short ones, and then proves that the
reading is correct against Mathlib's `RootPairing.RootPositiveForm.rootLength`.

Two pieces of data are attached to a type, both read off family by family.
`TauCeti.DynkinType.rootLength` gives the relative squared length of each simple root, normalised
for a *valid* type so that a shortest one has length `1`; it symmetrises the standard Cartan matrix
*on the right*, `A i j * ℓ j = A j i * ℓ i`, so it is integral where the symmetriser `d` asked for
by `TauCeti.IsFiniteType`, which scales the matrix on the left, is rational: that one is the
reciprocal `d i = (ℓ i)⁻¹`. `TauCeti.DynkinType.IsLongSimpleRoot` then singles out the long nodes.
Away from the degenerate `B 1` those are exactly the nodes of maximal length
(`TauCeti.DynkinType.isLongSimpleRoot_iff`), in particular for a valid type.

A handful of degenerate types stand between the family-wise reading and its intended meaning, and
each of the four statements below that meets one is proved first in its exact form, naming the
types it excludes, and then specialised to a valid type for the downstream consumers, which reach a
type through `TauCeti.HasCartanType` and so have validity and nothing else. The sole node of `C 1`
is the last node of the `Cₙ` family, hence long, of length `2`: nothing shorter sits beside it to
normalise against, so `rootLength` is off by the factor `2` there. The sole node of `B 1` is the
last node of the `Bₙ` family, hence short, while being of maximal length for want of competition:
that is the one type where the family-wise reading and the maximality reading of
`IsLongSimpleRoot` part company. Finally the rank-zero types `A 0`, `B 0`, `C 0` and `D 0` have no
node at all. A statement quantified over the nodes cannot see that, but an existential one can.

## The Bourbaki numbering

Everything here is stated against the node numbering of `TauCeti.DynkinType.cartanMatrix`, which is
Bourbaki's with node `i` at `Fin` index `i - 1`. Zero-based `Fin` indices against one-based
Bourbaki labels are the standing trap, so the numbering is pinned explicitly: the `Aₙ` chain runs
`0, 1, …, n - 1` in order; `Bₙ` and `Cₙ` continue that chain with the double edge between `n - 2`
and `n - 1`, the short simple root being the last node of `Bₙ` and the long one the last node of
`Cₙ`; `Dₙ` forks at `n - 3`; `Eₙ` follows Bourbaki with index `1` the branch node; `F₄` has
`0, 1` long and `2, 3` short; and `G₂` is short then long, so `TauCeti.DynkinType.IsLongSimpleRoot`
selects index `1` there.

`G₂` is the one place where Mathlib's convention differs from Bourbaki's, and
`TauCeti.DynkinType.cartanMatrix` follows Bourbaki: Mathlib's `CartanMatrix.G₂ = !![2, -3; -1, 2]`
is documented as the transpose of Bourbaki's plate IX matrix, so the standard matrix pinned here is
`CartanMatrix.G₂ᵀ = !![2, -1; -3, 2]`, whose short simple root comes first. That orientation is
what `TauCeti.DynkinType.cartanMatrix_mul_rootLength` forces: reading the lengths off the
transposed matrix instead would make that identity false.

## Main definitions

* `TauCeti.DynkinType.rootLength`: the relative squared length of each simple root of a type.
* `TauCeti.DynkinType.IsLongSimpleRoot`: the nodes its family calls long, which for a valid type
  are exactly those carrying a simple root of maximal length.

## Main results

* `TauCeti.DynkinType.cartanMatrix_mul_rootLength`: the standard Cartan matrix of a type is
  symmetrised on the right by `rootLength`, that is `A i j * ℓ j = A j i * ℓ i`. This is the
  identity that pins the relative lengths, and it holds for every type, valid or not.
* `TauCeti.DynkinType.exists_rootLength_eq_one_iff`: a type has a simple root of length `1` exactly
  when it has a node at all and is not `C 1`, whose sole node has length `2`; with
  `TauCeti.DynkinType.rootLength_pos` this is the normalisation of the lengths.
  `TauCeti.DynkinType.exists_rootLength_eq_one` is the corollary for a valid type.
* `TauCeti.DynkinType.isLongSimpleRoot_iff`: outside the degenerate `B 1`, a node is long exactly
  when its simple root has maximal length; `B 1` has a single node, which is of maximal length
  while `IsLongSimpleRoot` calls it short, because it is the short node of the `Bₙ` family.
  `TauCeti.DynkinType.isLongSimpleRoot_iff_of_valid` is the corollary for a valid type.
* `TauCeti.DynkinType.forall_isLongSimpleRoot_iff`: a type has all its simple roots long exactly
  when it is simply laced, has no node at all, or is `C 1`; for a valid type this is
  `TauCeti.DynkinType.forall_isLongSimpleRoot_iff_isSimplyLaced`.
* `TauCeti.DynkinType.exists_isLongSimpleRoot_iff`: a type has a long simple root exactly when it
  has a node at all and is not `B 1`; `TauCeti.DynkinType.exists_isLongSimpleRoot` is the corollary
  for a valid type.
* `TauCeti.DynkinType.isLongSimpleRoot_C_iff_not_isLongSimpleRoot_B`: `Bₙ` and `Cₙ` carry the same
  diagram with the lengths exchanged.
* `TauCeti.RootPairing.RootPositiveForm.rootLength_le_iff_pairingIn_le`: in any root pairing
  carrying a root-positive form, two roots meeting at a strictly negative pairing compare in length
  exactly as the transposed pair of pairings compares. This is the statement that makes the
  Cartan-matrix reading above meaningful.
* `TauCeti.RootPairing.RootPositiveForm.rootLength_le_iff_dynkinRootLength_le`: for a base matched
  to a Dynkin type, adjacent simple roots compare in length exactly as
  `TauCeti.DynkinType.rootLength` says they do.

## References

This file implements the "pin the node numbering" item of Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signature
`DynkinType.IsLongSimpleRoot` in that roadmap's `Suggested.lean`. See Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4-6*, plates I-IX, for the numbering and the root lengths, and Kac, *Infinite
Dimensional Lie Algebras*, Chapter 2, for symmetrisable Cartan matrices.
-/

namespace TauCeti

namespace DynkinType

/-- The relative squared length of the simple roots of a Dynkin type, in the Bourbaki numbering of
`TauCeti.DynkinType.cartanMatrix`, given family by family and normalised, for a valid type, so that
a shortest simple root has length `1`.

"Length" is squared length, as in Mathlib's `RootPairing.RootPositiveForm.rootLength`: it is the
value of an invariant form on a root with itself. The vector symmetrises the standard Cartan matrix
on the right (`TauCeti.DynkinType.cartanMatrix_mul_rootLength`), the symmetriser `d` that scales it
on the left, as in `TauCeti.IsFiniteType`, being the reciprocal `d i = (ℓ i)⁻¹`. Either way the
matrix alone determines the vector up to a positive factor once the diagram is connected; the
normalisation fixes that factor.

Validity is what the normalisation needs, and among the types of positive rank `C 1` is the one
that lacks it (the rank-zero types have no node to normalise against): its sole node is
the last node of the `Cₙ` family, hence of length `2`, with no shorter node beside it, so every
length there is twice what the normalisation would ask. Fixing that by hand would cost a
special case in `rootLength` and in every proof reading it, to normalise a type that
`TauCeti.DynkinType.Valid` excludes anyway; the family-wise reading is kept instead. -/
def rootLength : (t : DynkinType) → Fin t.rank → ℤ
  | .A _, _ | .D _, _ | .E6, _ | .E7, _ | .E8, _ => 1
  | .B n, i => if (i : ℕ) + 1 = n then 1 else 2
  | .C n, i => if (i : ℕ) + 1 = n then 2 else 1
  | .F4, i => if (i : ℕ) < 2 then 2 else 1
  | .G2, i => if (i : ℕ) = 0 then 1 else 3

-- The parenthesized `(rfl)` proofs keep these out of the implicit `@[defeq]` set, which would
-- otherwise demand that `rootLength` be `@[expose]`d. They are stated at the level of the whole
-- length vector rather than of one entry, as `TauCeti.DynkinType.cartanMatrix_A` and its siblings
-- are: an entrywise statement carries an index of type `Fin (A n).rank`, which does not match the
-- reduced `Fin n` that a case split on the type leaves behind.
@[simp] lemma rootLength_A (n : ℕ) : (A n).rootLength = fun _ ↦ 1 := (rfl)
@[simp] lemma rootLength_D (n : ℕ) : (D n).rootLength = fun _ ↦ 1 := (rfl)
@[simp] lemma rootLength_E6 : E6.rootLength = fun _ ↦ 1 := (rfl)
@[simp] lemma rootLength_E7 : E7.rootLength = fun _ ↦ 1 := (rfl)
@[simp] lemma rootLength_E8 : E8.rootLength = fun _ ↦ 1 := (rfl)

@[simp] lemma rootLength_B (n : ℕ) :
    (B n).rootLength = fun i : Fin (B n).rank ↦ if (i : ℕ) + 1 = n then (1 : ℤ) else 2 := (rfl)

@[simp] lemma rootLength_C (n : ℕ) :
    (C n).rootLength = fun i : Fin (C n).rank ↦ if (i : ℕ) + 1 = n then (2 : ℤ) else 1 := (rfl)

@[simp] lemma rootLength_F4 :
    F4.rootLength = fun i : Fin F4.rank ↦ if (i : ℕ) < 2 then (2 : ℤ) else 1 := (rfl)

@[simp] lemma rootLength_G2 :
    G2.rootLength = fun i : Fin G2.rank ↦ if (i : ℕ) = 0 then (1 : ℤ) else 3 := (rfl)

/-- Every simple root has positive length. -/
lemma rootLength_pos (t : DynkinType) (i : Fin t.rank) : 0 < t.rootLength i := by
  cases t <;> simp only [rootLength_A, rootLength_B, rootLength_C, rootLength_D, rootLength_E6,
    rootLength_E7, rootLength_E8, rootLength_F4, rootLength_G2] <;> (try split_ifs) <;> norm_num

/-- **A Dynkin type has a simple root of length `1` exactly when it has a node at all and is not
`C 1`.** With `TauCeti.DynkinType.rootLength_pos` this is the normalisation that
`TauCeti.DynkinType.rootLength` is stated up to: away from the two exceptions the shortest simple
roots are exactly those of length `1`.

Both exceptions are degenerate. The rank-zero types `A 0`, `B 0`, `C 0` and `D 0` have no simple
root at all to exhibit; and the sole node of `C 1` is the last node of the `Cₙ` family, which that
family calls long and gives length `2`. -/
theorem exists_rootLength_eq_one_iff (t : DynkinType) :
    (∃ i, t.rootLength i = 1) ↔ 0 < t.rank ∧ t ≠ C 1 := by
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨(Nat.zero_le _).trans_lt i.isLt, ?_⟩, fun ⟨hr, hne⟩ ↦ ?_⟩
  · -- The sole node of `C 1` is the long last node of the `Cₙ` family.
    rintro rfl
    have h1 : (i : ℕ) < 1 := i.isLt
    simp only [rootLength_C] at hi
    split_ifs at hi <;> omega
  · cases t with
    | A n => exact ⟨⟨0, hr⟩, by simp⟩
    | D n => exact ⟨⟨0, hr⟩, by simp⟩
    | E6 => exact ⟨⟨0, by simp⟩, by simp⟩
    | E7 => exact ⟨⟨0, by simp⟩, by simp⟩
    | E8 => exact ⟨⟨0, by simp⟩, by simp⟩
    | B n =>
        -- The last node of `Bₙ` is its short one.
        have hn : 0 < n := hr
        obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, (j₀ : ℕ) = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
        exact ⟨j₀, by simp only [rootLength_B]; split_ifs <;> omega⟩
    | C n =>
        -- Every node of `Cₙ` but the last is short, and `n ≠ 1` gives a node before the last.
        have hn : 0 < n := hr
        have hn1 : n ≠ 1 := by rintro rfl; exact hne rfl
        obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, (j₀ : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
        exact ⟨j₀, by simp only [rootLength_C]; split_ifs <;> omega⟩
    | F4 =>
        obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin 4, (j₀ : ℕ) = 2 := ⟨⟨2, by omega⟩, rfl⟩
        exact ⟨j₀, by simp only [rootLength_F4]; split_ifs <;> omega⟩
    | G2 =>
        obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin 2, (j₀ : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
        exact ⟨j₀, by simp only [rootLength_G2]; split_ifs <;> omega⟩

/-- **A valid Dynkin type has a simple root of length `1`.** This is
`TauCeti.DynkinType.exists_rootLength_eq_one_iff` for a valid type, which excludes both of its
exceptions: the rank-zero types and `C 1`. -/
theorem exists_rootLength_eq_one {t : DynkinType} (ht : t.Valid) : ∃ i, t.rootLength i = 1 :=
  (exists_rootLength_eq_one_iff t).mpr ⟨rank_pos ht, by rintro rfl; simp at ht⟩

/-- A simply-laced type has all its simple roots of length `1`. -/
lemma rootLength_eq_one_of_isSimplyLaced {t : DynkinType} (ht : t.IsSimplyLaced)
    (i : Fin t.rank) : t.rootLength i = 1 := by
  cases t
  case B n => exact absurd ht (not_isSimplyLaced_B n)
  case C n => exact absurd ht (not_isSimplyLaced_C n)
  case F4 => exact absurd ht not_isSimplyLaced_F4
  case G2 => exact absurd ht not_isSimplyLaced_G2
  all_goals simp

/-- **The standard Cartan matrix of a Dynkin type is symmetrised on the right by `rootLength`.**
Writing `A = t.cartanMatrix` and `ℓ = t.rootLength`, the products `A i j * ℓ j` are symmetric in
`i` and `j`, so `ℓ i / ℓ j = A i j / A j i` whenever the two nodes are joined. This is what fixes
the relative lengths, and with `TauCeti.DynkinType.rootLength_pos` it exhibits the rational
symmetriser `d i = (ℓ i)⁻¹` that `TauCeti.IsFiniteType` asks for, which scales the matrix on the
left rather than on the right as `ℓ` does.

No validity hypothesis is needed: the identity holds for the degenerate low-rank types too. -/
theorem cartanMatrix_mul_rootLength (t : DynkinType) (i j : Fin t.rank) :
    t.cartanMatrix i j * t.rootLength j = t.cartanMatrix j i * t.rootLength i := by
  -- For the simply-laced types both lengths are `1` and the matrix is symmetric. For `Bₙ` the
  -- only asymmetric pair of entries is the double edge, and the lengths `2` and `1` there
  -- compensate for it exactly; `Cₙ` is the transpose of `Bₙ`, whose length vector is reciprocal.
  cases t with
  | A n => simpa using (CartanMatrix.A_isSymm n).apply j i
  | D n => simpa using (CartanMatrix.D_isSymm n).apply j i
  | E6 => simpa using (CartanMatrix.E_isSymm 6).apply j i
  | E7 => simpa using (CartanMatrix.E_isSymm 7).apply j i
  | E8 => simpa using (CartanMatrix.E_isSymm 8).apply j i
  | F4 =>
      simp only [cartanMatrix_F4, rootLength_F4]
      fin_cases i <;> fin_cases j <;> decide
  | G2 =>
      simp only [cartanMatrix_G2, rootLength_G2]
      fin_cases i <;> fin_cases j <;> decide
  | B n =>
      -- Splitting on `t` leaves dependent indices that elaborate as `Fin t.rank`; expose their
      -- definitional reduction to `Fin n` before unfolding the non-symmetric matrix.
      change Fin n at i j
      have hi : (i : ℕ) < n := i.isLt
      have hj : (j : ℕ) < n := j.isLt
      simp only [cartanMatrix_B, rootLength_B]
      unfold CartanMatrix.B
      simp only [Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
  | C n =>
      -- As in the `B` branch, make the reduced dependent index explicit.
      change Fin n at i j
      have hi : (i : ℕ) < n := i.isLt
      have hj : (j : ℕ) < n := j.isLt
      simp only [cartanMatrix_C, rootLength_C]
      unfold CartanMatrix.C
      simp only [Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega

/-- A simple root of a Dynkin type is **long** when its type's family calls that node long, in the
Bourbaki numbering of `TauCeti.DynkinType.cartanMatrix`: simply-laced types have all their simple
roots of the same length, hence all long; `Bₙ` is short at its last node, `Cₙ` long only at its
last node, `F₄` long at its first two nodes and `G₂` long at its second, following Bourbaki's
numbering as `TauCeti.DynkinType.cartanMatrix` pins it.

Away from the degenerate `B 1` this is exactly maximality of length among the simple roots
(`TauCeti.DynkinType.isLongSimpleRoot_iff`), in particular for a valid type
(`TauCeti.DynkinType.isLongSimpleRoot_iff_of_valid`). `B 1` really is an exception: it has a single
node, of maximal length, that this predicate calls short as the short node of the `Bₙ` family. -/
def IsLongSimpleRoot : (t : DynkinType) → Fin t.rank → Prop
  | .A _, _ | .D _, _ | .E6, _ | .E7, _ | .E8, _ => True
  | .B n, i => (i : ℕ) + 1 < n
  | .C n, i => (i : ℕ) + 1 = n
  | .F4, i => (i : ℕ) < 2
  | .G2, i => (i : ℕ) = 1

instance : ∀ t : DynkinType, DecidablePred t.IsLongSimpleRoot
  | .A _ | .D _ | .E6 | .E7 | .E8 => fun _ ↦ inferInstanceAs (Decidable True)
  | .B n => fun i ↦ inferInstanceAs (Decidable ((i : ℕ) + 1 < n))
  | .C n => fun i ↦ inferInstanceAs (Decidable ((i : ℕ) + 1 = n))
  | .F4 => fun i ↦ inferInstanceAs (Decidable ((i : ℕ) < 2))
  | .G2 => fun i ↦ inferInstanceAs (Decidable ((i : ℕ) = 1))

@[simp] lemma isLongSimpleRoot_A (n : ℕ) : (A n).IsLongSimpleRoot = fun _ ↦ True := (rfl)
@[simp] lemma isLongSimpleRoot_D (n : ℕ) : (D n).IsLongSimpleRoot = fun _ ↦ True := (rfl)
@[simp] lemma isLongSimpleRoot_E6 : E6.IsLongSimpleRoot = fun _ ↦ True := (rfl)
@[simp] lemma isLongSimpleRoot_E7 : E7.IsLongSimpleRoot = fun _ ↦ True := (rfl)
@[simp] lemma isLongSimpleRoot_E8 : E8.IsLongSimpleRoot = fun _ ↦ True := (rfl)

@[simp] lemma isLongSimpleRoot_B (n : ℕ) :
    (B n).IsLongSimpleRoot = fun i : Fin (B n).rank ↦ (i : ℕ) + 1 < n := (rfl)

@[simp] lemma isLongSimpleRoot_C (n : ℕ) :
    (C n).IsLongSimpleRoot = fun i : Fin (C n).rank ↦ (i : ℕ) + 1 = n := (rfl)

@[simp] lemma isLongSimpleRoot_F4 :
    F4.IsLongSimpleRoot = fun i : Fin F4.rank ↦ (i : ℕ) < 2 := (rfl)

@[simp] lemma isLongSimpleRoot_G2 :
    G2.IsLongSimpleRoot = fun i : Fin G2.rank ↦ (i : ℕ) = 1 := (rfl)

/-- **A node of a Dynkin type other than `B 1` is long exactly when its simple root has maximal
length.**

The exception is not decoration. The degenerate type `B 1` has a single node, necessarily of maximal
length, but `TauCeti.DynkinType.IsLongSimpleRoot` calls it short because it is the short node of
the `Bₙ` family; that node is the only counterexample among all the types. -/
theorem isLongSimpleRoot_iff {t : DynkinType} (ht : t ≠ B 1) (i : Fin t.rank) :
    t.IsLongSimpleRoot i ↔ ∀ j, t.rootLength j ≤ t.rootLength i := by
  cases t with
  | A n | D n | E6 | E7 | E8 => simp
  | F4 => simp only [isLongSimpleRoot_F4, rootLength_F4]; revert i; decide
  | G2 => simp only [isLongSimpleRoot_G2, rootLength_G2]; revert i; decide
  | B n =>
      -- As in `cartanMatrix_mul_rootLength`, the case split leaves `i` elaborated at the
      -- unreduced type `Fin (B n).rank`; expose its definitional reduction to `Fin n` so that
      -- `i.isLt` bounds `i` by `n` and `omega` can compare it with the last node.
      change Fin n at i
      have hi : (i : ℕ) < n := i.isLt
      -- The node `i` bounds `n` below by `1`, and `B 1` is the excluded type.
      have hn : 2 ≤ n := by
        have hn1 : n ≠ 1 := by rintro rfl; exact ht rfl
        omega
      simp only [isLongSimpleRoot_B, rootLength_B]
      refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
      · split_ifs <;> omega
      · -- The first node is long, so a node of maximal length cannot be the short last one.
        obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, (j₀ : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
        have h₀ := h j₀
        split_ifs at h₀ <;> omega
  | C n =>
      -- As in the `B` branch, make the reduced dependent index explicit before bounding it.
      change Fin n at i
      have hi : (i : ℕ) < n := i.isLt
      simp only [isLongSimpleRoot_C, rootLength_C]
      refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
      · split_ifs <;> omega
      · -- The last node is the only long one, so a node of maximal length is that node.
        obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, (j₀ : ℕ) = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
        have h₀ := h j₀
        split_ifs at h₀ <;> omega

/-- **A node of a valid Dynkin type is long exactly when its simple root has maximal length.** This
is `TauCeti.DynkinType.isLongSimpleRoot_iff` for a valid type, which excludes its one exception
`B 1`. -/
theorem isLongSimpleRoot_iff_of_valid {t : DynkinType} (ht : t.Valid) (i : Fin t.rank) :
    t.IsLongSimpleRoot i ↔ ∀ j, t.rootLength j ≤ t.rootLength i :=
  isLongSimpleRoot_iff (by rintro rfl; simp at ht) i

/-- Every simple root of a simply-laced type is long: all its simple roots have the same length. -/
lemma isLongSimpleRoot_of_isSimplyLaced {t : DynkinType} (ht : t.IsSimplyLaced) (i : Fin t.rank) :
    t.IsLongSimpleRoot i := by
  cases t
  case B n => exact absurd ht (not_isSimplyLaced_B n)
  case C n => exact absurd ht (not_isSimplyLaced_C n)
  case F4 => exact absurd ht not_isSimplyLaced_F4
  case G2 => exact absurd ht not_isSimplyLaced_G2
  all_goals simp

/-- **A Dynkin type has all its simple roots long exactly when it is simply laced, has no node at
all, or is `C 1`.** The multiply-laced types `Bₙ`, `Cₙ`, `F₄` and `G₂` each have a short simple
root, save in the two degenerate cases the right-hand side names: the rank-zero `B 0` and `C 0`,
which have no node at all to be short, and `C 1`, whose sole node the `Cₙ` family calls long. The
remaining degenerate type `B 1` is no exception, its sole node being short. -/
theorem forall_isLongSimpleRoot_iff (t : DynkinType) :
    (∀ i, t.IsLongSimpleRoot i) ↔ t.IsSimplyLaced ∨ t.rank = 0 ∨ t = C 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases t with
    | A n | D n | E6 | E7 | E8 => exact Or.inl (by simp)
    | B n =>
        obtain rfl | hn : n = 0 ∨ 0 < n := by omega
        · exact Or.inr (Or.inl (by simp))
        · obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, (j₀ : ℕ) = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
          have h₀ := h j₀
          simp only [isLongSimpleRoot_B] at h₀
          exact absurd h₀ (by omega)
    | C n =>
        obtain rfl | rfl | hn : n = 0 ∨ n = 1 ∨ 2 ≤ n := by omega
        · exact Or.inr (Or.inl (by simp))
        · exact Or.inr (Or.inr rfl)
        · obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, (j₀ : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
          have h₀ := h j₀
          simp only [isLongSimpleRoot_C] at h₀
          exact absurd h₀ (by omega)
    | F4 =>
        obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin 4, (j₀ : ℕ) = 2 := ⟨⟨2, by omega⟩, rfl⟩
        have h₀ := h j₀
        simp only [isLongSimpleRoot_F4] at h₀
        exact absurd h₀ (by omega)
    | G2 =>
        obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin 2, (j₀ : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
        have h₀ := h j₀
        simp only [isLongSimpleRoot_G2] at h₀
        exact absurd h₀ (by omega)
  · rintro (h | h | rfl) i
    · exact isLongSimpleRoot_of_isSimplyLaced h i
    · -- A type of rank zero has no node for the statement to constrain.
      exact absurd i.isLt (by omega)
    · -- The sole node of `C 1` is its last one, which the `Cₙ` family calls long.
      have h1 : (i : ℕ) < 1 := i.isLt
      simp only [isLongSimpleRoot_C]
      omega

/-- **A valid Dynkin type has all its simple roots long exactly when it is simply laced.** This is
`TauCeti.DynkinType.forall_isLongSimpleRoot_iff` for a valid type, which excludes both of its
degenerate cases: the rank-zero `B 0` and `C 0`, and `C 1`. -/
theorem forall_isLongSimpleRoot_iff_isSimplyLaced {t : DynkinType} (ht : t.Valid) :
    (∀ i, t.IsLongSimpleRoot i) ↔ t.IsSimplyLaced := by
  refine (forall_isLongSimpleRoot_iff t).trans (or_iff_left ?_)
  rintro (h | rfl)
  · have := rank_pos ht
    omega
  · simp at ht

/-- **A Dynkin type has a long simple root exactly when it has a node at all and is not `B 1`.**
Both exceptions are degenerate: the rank-zero types have no node to be long, and the sole node of
`B 1` is the short last node of the `Bₙ` family. -/
theorem exists_isLongSimpleRoot_iff (t : DynkinType) :
    (∃ i, t.IsLongSimpleRoot i) ↔ 0 < t.rank ∧ t ≠ B 1 := by
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨(Nat.zero_le _).trans_lt i.isLt, ?_⟩, fun ⟨hr, hne⟩ ↦ ?_⟩
  · -- The sole node of `B 1` is the short last node of the `Bₙ` family.
    rintro rfl
    have h1 : (i : ℕ) < 1 := i.isLt
    simp only [isLongSimpleRoot_B] at hi
    omega
  · -- A type with a node has one of maximal length, which is long by
    -- `TauCeti.DynkinType.isLongSimpleRoot_iff`.
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_max_image Finset.univ t.rootLength ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    exact ⟨i, (isLongSimpleRoot_iff hne i).mpr fun j ↦ hi j (Finset.mem_univ j)⟩

/-- Every valid Dynkin type has a long simple root. This is
`TauCeti.DynkinType.exists_isLongSimpleRoot_iff` for a valid type, which excludes both of its
exceptions: the rank-zero types and `B 1`. -/
theorem exists_isLongSimpleRoot {t : DynkinType} (ht : t.Valid) : ∃ i, t.IsLongSimpleRoot i :=
  (exists_isLongSimpleRoot_iff t).mpr ⟨rank_pos ht, by rintro rfl; simp at ht⟩

/-- **Types `Bₙ` and `Cₙ` have the same diagram with long and short exchanged.** Their standard
Cartan matrices are transposes of one another (`CartanMatrix.B_transpose`), and this is that duality
read at the level of root lengths: a node long in one type is short in the other. -/
theorem isLongSimpleRoot_C_iff_not_isLongSimpleRoot_B (n : ℕ) (i : Fin n) :
    (C n).IsLongSimpleRoot i ↔ ¬ (B n).IsLongSimpleRoot i := by
  have hi : (i : ℕ) < n := i.isLt
  simp only [isLongSimpleRoot_B, isLongSimpleRoot_C]
  omega

end DynkinType

/-- Comparing two positive quantities tied together by a strictly negative multiplier. If
`a * y = c * x` with `x` positive and `a` strictly negative, then `x ≤ y` exactly when `c ≤ a`.

This is the shared arithmetic behind the two length comparisons below: a transposed pair of Cartan
entries and a pair of root lengths always satisfy such a symmetrised relation, whether the lengths
are those of `TauCeti.DynkinType.rootLength` or those measured by a root-positive form. -/
private lemma le_iff_le_of_mul_eq_mul {S : Type*} [CommRing S] [LinearOrder S]
    [IsStrictOrderedRing S] {a c x y : S} (hx : 0 < x) (ha : a < 0) (h : a * y = c * x) :
    x ≤ y ↔ c ≤ a := by
  refine ⟨fun hxy ↦ ?_, fun hca ↦ ?_⟩
  · have h1 : c * x ≤ a * x := h ▸ mul_le_mul_of_nonpos_left hxy ha.le
    exact le_of_mul_le_mul_right h1 hx
  · have h1 : a * y ≤ a * x := h ▸ mul_le_mul_of_nonneg_right hca hx.le
    exact (mul_le_mul_left_of_neg ha).mp h1

namespace RootPairing.RootPositiveForm

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section IsValuedIn

variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R]
  [FaithfulSMul S R] [Module S M] [IsScalarTower S R M]
  {P : RootPairing ι R M N} [P.IsValuedIn S]

/-- **Two roots meeting at a strictly negative pairing compare in length exactly as their
transposed pair of pairings compares.** This is the content behind reading root lengths off a
Cartan matrix: `⟨αᵢ, αⱼ^∨⟩ / ⟨αⱼ, αᵢ^∨⟩` is the ratio `‖αᵢ‖² / ‖αⱼ‖²`, so the more negative entry
belongs to the longer root.

The negativity hypothesis is what pins the direction. It is automatic for two distinct simple roots
of a base, whose pairings are nonpositive, once they are not orthogonal; for a pair with positive
pairings the comparison is reversed. -/
theorem rootLength_le_iff_pairingIn_le (B : P.RootPositiveForm S) {i j : ι}
    (h : P.pairingIn S i j < 0) :
    B.rootLength i ≤ B.rootLength j ↔ P.pairingIn S j i ≤ P.pairingIn S i j :=
  le_iff_le_of_mul_eq_mul (B.rootLength_pos i) h
    (B.pairingIn_mul_eq_pairingIn_mul_swap i j).symm

end IsValuedIn

section IsCrystallographic

variable [CharZero R] {P : RootPairing ι R M N} [P.IsCrystallographic]

/-- **A base matched to a Dynkin type has its adjacent simple roots comparing in length exactly as
`TauCeti.DynkinType.rootLength` says.** The matching `e` is taken as data rather than through
`TauCeti.HasCartanType` so that the statement names the node the comparison is made at; any witness
of `TauCeti.HasCartanType` supplies one, and since the left-hand side does not mention `e`, the
comparison read off the type is the same for every witness.

The hypothesis that the two nodes are joined is necessary: two simple roots that are orthogonal are
constrained by nothing, and in `Cₙ` for instance the first node is short although no neighbour of
it is longer. -/
theorem rootLength_le_iff_dynkinRootLength_le {b : P.Base} {t : DynkinType}
    {e : b.support ≃ Fin t.rank} (he : ∀ i j, b.cartanMatrix i j = t.cartanMatrix (e i) (e j))
    (B : P.RootPositiveForm ℤ) {i j : b.support} (h : b.cartanMatrix i j < 0) :
    B.rootLength i ≤ B.rootLength j ↔ t.rootLength (e i) ≤ t.rootLength (e j) := by
  -- The comparison of `rootLength_le_iff_pairingIn_le` is one of pairings, and the Cartan
  -- entries of a base are those pairings definitionally (`RootPairing.Base.cartanMatrixIn_def`).
  have key : B.rootLength i ≤ B.rootLength j ↔ b.cartanMatrix j i ≤ b.cartanMatrix i j :=
    rootLength_le_iff_pairingIn_le B h
  rw [key, he i j, he j i]
  refine (le_iff_le_of_mul_eq_mul (t.rootLength_pos (e i)) ?_
    (t.cartanMatrix_mul_rootLength (e i) (e j))).symm
  rwa [he i j] at h

end IsCrystallographic

end RootPairing.RootPositiveForm

end TauCeti
