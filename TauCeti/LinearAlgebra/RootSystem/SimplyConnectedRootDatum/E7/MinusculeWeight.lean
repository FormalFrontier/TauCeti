/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# The minuscule weight orbit of type E7

This file enumerates the Weyl orbit of the seventh fundamental weight of the pinned simply
connected root datum `TauCeti.DynkinType.e7SimplyConnectedRootDatum`. The fifty-six weights are
expressed in the fundamental-weight basis `Fin 7 → ℤ`. The first weight is `ϖ₇`, and the table
is closed under the seven Bourbaki-numbered simple reflections through explicit permutations of
`Fin 56`.

The table is the weight diagram of the 56-dimensional minuscule representation. Every simple-
coroot coordinate is `-1`, `0`, or `1`; the table is exactly the Weyl orbit of `ϖ₇`; and its
weights span the complete character lattice. The spanning statement is the input that lets the
weight torus in the eventual integral minuscule carrier be a closed immersion, rather than seeing
only the index-two root lattice of the adjoint representation.

No representation or group scheme is constructed here. This is the pinned full-weight lattice
input for the type-`E₇` Chevalley--Demazure construction in Layer 9 of the ReductiveGroups
roadmap, consumed by the explicit pinned-carrier milestone of the CFSG statement roadmap.

## Main declarations

* `TauCeti.DynkinType.e7MinusculeWeight`: the fifty-six weights in fundamental coordinates.
* `TauCeti.DynkinType.e7MinusculeReflection`: the permutation induced by a simple reflection.
* `TauCeti.DynkinType.e7MinusculeWeight_reflection`: the simple-reflection equation.
* `TauCeti.DynkinType.range_e7MinusculeWeight`: the table is exactly the Weyl orbit of `ϖ₇`.
* `TauCeti.DynkinType.span_range_e7MinusculeWeight_eq_top`: the weights span the character
  lattice.

## References

The node numbering and the choice of the minuscule weight `ϖ₇` follow Bourbaki, *Lie Groups and
Lie Algebras, Chapters 4--6*, Plate VI. The 56-dimensional minuscule weight diagram follows
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.4, and J. C.
Jantzen, *Representations of Algebraic Groups*, II.2. The formal organization follows the
type-`E₆` minuscule orbit in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight`.
-/

public section

namespace TauCeti.DynkinType

open Set

/-! ## The weight table -/

/-- **The fifty-six weights in the Weyl orbit of the type-`E₇` minuscule weight `ϖ₇`.**

Coordinates are pairings with the seven Bourbaki-numbered simple coroots. The ordering begins at
`ϖ₇ = (0, 0, 0, 0, 0, 0, 1)` and then lists weights reached successively by simple
reflections; no mathematical structure depends on the ordering. -/
def e7MinusculeWeight : Fin 56 → Fin 7 → ℤ := ![
  ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, -1],
  ![0, 0, 0, 0, 1, -1, 0], ![0, 0, 0, 1, -1, 0, 0],
  ![0, 1, 1, -1, 0, 0, 0], ![0, -1, 1, 0, 0, 0, 0],
  ![1, 1, -1, 0, 0, 0, 0], ![1, -1, -1, 1, 0, 0, 0],
  ![-1, 1, 0, 0, 0, 0, 0], ![-1, -1, 0, 1, 0, 0, 0],
  ![1, 0, 0, -1, 1, 0, 0], ![-1, 0, 1, -1, 1, 0, 0],
  ![1, 0, 0, 0, -1, 1, 0], ![0, 0, -1, 0, 1, 0, 0],
  ![-1, 0, 1, 0, -1, 1, 0], ![1, 0, 0, 0, 0, -1, 1],
  ![0, 0, -1, 1, -1, 1, 0], ![-1, 0, 1, 0, 0, -1, 1],
  ![1, 0, 0, 0, 0, 0, -1], ![0, 1, 0, -1, 0, 1, 0],
  ![0, 0, -1, 1, 0, -1, 1], ![-1, 0, 1, 0, 0, 0, -1],
  ![0, -1, 0, 0, 0, 1, 0], ![0, 1, 0, -1, 1, -1, 1],
  ![0, 0, -1, 1, 0, 0, -1], ![0, -1, 0, 0, 1, -1, 1],
  ![0, 1, 0, 0, -1, 0, 1], ![0, 1, 0, -1, 1, 0, -1],
  ![0, -1, 0, 1, -1, 0, 1], ![0, -1, 0, 0, 1, 0, -1],
  ![0, 1, 0, 0, -1, 1, -1], ![0, 0, 1, -1, 0, 0, 1],
  ![0, -1, 0, 1, -1, 1, -1], ![0, 1, 0, 0, 0, -1, 0],
  ![1, 0, -1, 0, 0, 0, 1], ![0, 0, 1, -1, 0, 1, -1],
  ![0, -1, 0, 1, 0, -1, 0], ![-1, 0, 0, 0, 0, 0, 1],
  ![1, 0, -1, 0, 0, 1, -1], ![0, 0, 1, -1, 1, -1, 0],
  ![-1, 0, 0, 0, 0, 1, -1], ![1, 0, -1, 0, 1, -1, 0],
  ![0, 0, 1, 0, -1, 0, 0], ![-1, 0, 0, 0, 1, -1, 0],
  ![1, 0, -1, 1, -1, 0, 0], ![-1, 0, 0, 1, -1, 0, 0],
  ![1, 1, 0, -1, 0, 0, 0], ![-1, 1, 1, -1, 0, 0, 0],
  ![1, -1, 0, 0, 0, 0, 0], ![-1, -1, 1, 0, 0, 0, 0],
  ![0, 1, -1, 0, 0, 0, 0], ![0, -1, -1, 1, 0, 0, 0],
  ![0, 0, 0, -1, 1, 0, 0], ![0, 0, 0, 0, -1, 1, 0],
  ![0, 0, 0, 0, 0, -1, 1], ![0, 0, 0, 0, 0, 0, -1]]

/-- The fifty-six minuscule weights are pairwise distinct. -/
theorem e7MinusculeWeight_injective : Function.Injective e7MinusculeWeight := by
  decide +kernel +revert

/-- The first weight in the table is the seventh fundamental weight `ϖ₇`. -/
@[simp]
theorem e7MinusculeWeight_zero : e7MinusculeWeight 0 = Pi.single 6 1 := by
  decide

/-- Every pairing of an `E₇` minuscule weight with a simple coroot is `-1`, `0`, or `1`. -/
theorem e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (a : Fin 56) (i : Fin 7) :
    e7MinusculeWeight a i = -1 ∨ e7MinusculeWeight a i = 0 ∨
      e7MinusculeWeight a i = 1 := by
  fin_cases a <;> fin_cases i <;> decide

/-! ## Simple reflections -/

/-- The index table underlying the seven simple-reflection permutations. -/
private def e7MinusculeReflectionIndex : Fin 7 → Fin 56 → Fin 56 := ![
  ![0, 1, 2, 3, 4, 5, 8, 9, 6, 7, 11, 10, 14, 13,
    12, 17, 16, 15, 21, 19, 20, 18, 22, 23, 24, 25, 26, 27,
    28, 29, 30, 31, 32, 33, 37, 35, 36, 34, 40, 39, 38, 43,
    42, 41, 45, 44, 47, 46, 49, 48, 50, 51, 52, 53, 54, 55],
  ![0, 1, 2, 3, 5, 4, 7, 6, 9, 8, 10, 11, 12, 13,
    14, 15, 16, 17, 18, 22, 20, 21, 19, 25, 24, 23, 28, 29,
    26, 27, 32, 31, 30, 36, 34, 35, 33, 37, 38, 39, 40, 41,
    42, 43, 44, 45, 48, 49, 46, 47, 51, 50, 52, 53, 54, 55],
  ![0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 13, 12, 11,
    16, 15, 14, 20, 18, 19, 17, 24, 22, 23, 21, 25, 26, 27,
    28, 29, 30, 34, 32, 33, 31, 38, 36, 37, 35, 41, 40, 39,
    44, 43, 42, 45, 46, 50, 48, 51, 47, 49, 52, 53, 54, 55],
  ![0, 1, 2, 4, 3, 5, 6, 10, 8, 11, 7, 9, 12, 13,
    14, 15, 19, 17, 18, 16, 23, 21, 22, 20, 27, 25, 26, 24,
    31, 29, 30, 28, 35, 33, 34, 32, 39, 37, 38, 36, 40, 41,
    42, 43, 46, 47, 44, 45, 48, 49, 50, 52, 51, 53, 54, 55],
  ![0, 1, 3, 2, 4, 5, 6, 7, 8, 9, 12, 14, 10, 16,
    11, 15, 13, 17, 18, 19, 20, 21, 22, 26, 24, 28, 23, 30,
    25, 32, 27, 31, 29, 33, 34, 35, 36, 37, 38, 42, 40, 44,
    39, 45, 41, 43, 46, 47, 48, 49, 50, 51, 53, 52, 54, 55],
  ![0, 2, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 13,
    17, 12, 20, 14, 18, 23, 16, 21, 25, 19, 24, 22, 26, 27,
    28, 29, 33, 31, 36, 30, 34, 39, 32, 37, 41, 35, 43, 38,
    42, 40, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 53, 55],
  ![1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
    14, 18, 16, 21, 15, 19, 24, 17, 22, 27, 20, 29, 30, 23,
    32, 25, 26, 35, 28, 33, 38, 31, 36, 40, 34, 39, 37, 41,
    42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 54]]

private theorem e7MinusculeReflectionIndex_involutive (i : Fin 7) :
    Function.Involutive (e7MinusculeReflectionIndex i) := by
  fin_cases i <;> intro a <;> fin_cases a <;> decide

/-- **The permutation of the fifty-six minuscule weights induced by the `i`-th simple
reflection.** -/
def e7MinusculeReflection (i : Fin 7) : Equiv.Perm (Fin 56) :=
  (e7MinusculeReflectionIndex_involutive i).toPerm

/-- Applying the same simple reflection twice fixes every index in the weight table. -/
@[simp]
theorem e7MinusculeReflection_apply_apply (i : Fin 7) (a : Fin 56) :
    e7MinusculeReflection i (e7MinusculeReflection i a) = a :=
  e7MinusculeReflectionIndex_involutive i a

private theorem e7MinusculeWeight_reflection_table (i : Fin 7) (a : Fin 56) :
    e7MinusculeWeight (e7MinusculeReflection i a) =
      e7MinusculeWeight a - e7MinusculeWeight a i • CartanMatrix.E 7 i := by
  rw [CartanMatrix.E_seven_eq]
  decide +kernel +revert

/-- **The coordinate equation for a simple reflection on the minuscule weights.** Reflection in
the `i`-th simple root subtracts the pairing with the `i`-th simple coroot times that root. -/
theorem e7MinusculeWeight_reflection (i : Fin 7) (a : Fin 56) :
    e7MinusculeWeight (e7MinusculeReflection i a) =
      e7MinusculeWeight a - e7MinusculeWeight a i • e7Root (e7SimpleIndex i) := by
  rw [root_e7SimpleIndex]
  exact e7MinusculeWeight_reflection_table i a

/-- A simple reflection fixes a minuscule weight exactly when its simple-coroot coordinate is
zero. -/
@[simp]
theorem e7MinusculeReflection_eq_self_iff (i : Fin 7) (a : Fin 56) :
    e7MinusculeReflection i a = a ↔ e7MinusculeWeight a i = 0 := by
  constructor
  · intro h
    have hweight := congrArg e7MinusculeWeight h
    rw [e7MinusculeWeight_reflection] at hweight
    have hi := congrFun hweight i
    simp [root_e7SimpleIndex, CartanMatrix.E_seven_eq] at hi
    fin_cases i <;> simp_all
  · intro h
    apply e7MinusculeWeight_injective
    rw [e7MinusculeWeight_reflection]
    simp [h]

/-- The explicit permutation agrees with reflection in the pinned simply connected root datum. -/
@[simp]
theorem e7SimplyConnectedRootDatum_reflection_e7MinusculeWeight
    (i : Fin 7) (a : Fin 56) :
    e7SimplyConnectedRootDatum.reflection (e7SimpleIndex i) (e7MinusculeWeight a) =
      e7MinusculeWeight (e7MinusculeReflection i a) := by
  rw [e7MinusculeWeight_reflection]
  simp [RootPairing.reflection_apply]

/-! ## The Weyl orbit -/

/-- A parent of every non-highest weight in the reflection graph. -/
private def e7MinusculeParent : Fin 55 → Fin 56 := ![
  0, 1, 2, 3, 4, 4, 5, 6, 7, 7, 9, 10, 11, 11,
  12, 13, 14, 15, 16, 16, 17, 19, 19, 20, 22, 23, 23, 25,
  25, 26, 28, 28, 30, 31, 31, 32, 34, 34, 35, 37, 38, 39,
  40, 41, 43, 44, 45, 46, 47, 47, 49, 51, 52, 53, 54]

/-- The simple reflection carrying each parent to its child. -/
private def e7MinusculeParentNode : Fin 55 → Fin 7 := ![
  6, 5, 4, 3, 1, 2, 2, 0, 0, 3, 3, 4, 2, 4,
  5, 4, 5, 6, 3, 5, 6, 1, 5, 6, 5, 4, 6, 4,
  6, 6, 3, 6, 5, 2, 6, 5, 0, 6, 5, 6, 5, 4,
  5, 4, 4, 3, 3, 1, 1, 2, 2, 3, 4, 5, 6]

private theorem e7MinusculeParent_lt_succ (a : Fin 55) :
    (e7MinusculeParent a : ℕ) < (a.succ : ℕ) := by
  fin_cases a <;> decide

private theorem e7MinusculeWeight_succ_eq_reflection_parent (a : Fin 55) :
    e7MinusculeWeight a.succ =
      e7SimplyConnectedRootDatum.reflection
        (e7SimpleIndex (e7MinusculeParentNode a))
        (e7MinusculeWeight (e7MinusculeParent a)) := by
  rw [e7SimplyConnectedRootDatum_reflection_e7MinusculeWeight]
  fin_cases a <;> decide

private theorem e7MinusculeWeight_mem_orbit (a : Fin 56) :
    e7MinusculeWeight a ∈
      MulAction.orbit e7SimplyConnectedRootDatum.weylGroup
        (Pi.single 6 1 : Fin 7 → ℤ) := by
  have aux : ∀ n, ∀ hn : n < 56, e7MinusculeWeight ⟨n, hn⟩ ∈
      MulAction.orbit e7SimplyConnectedRootDatum.weylGroup
        (Pi.single 6 1 : Fin 7 → ℤ) := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hzero : n = 0
        · subst n
          -- Expose the zero index so the public highest-weight lemma applies.
          change e7MinusculeWeight 0 ∈
            MulAction.orbit e7SimplyConnectedRootDatum.weylGroup
              (Pi.single 6 1 : Fin 7 → ℤ)
          rw [e7MinusculeWeight_zero]
          exact MulAction.mem_orbit_self _
        · let a : Fin 55 := ⟨n - 1, by omega⟩
          have hasucc : a.succ = (⟨n, hn⟩ : Fin 56) := by
            apply Fin.ext
            simp [a]
            omega
          have hparent : (e7MinusculeParent a : ℕ) < n := by
            have h := e7MinusculeParent_lt_succ a
            -- The equality of `Fin` values exposes the natural-number endpoint in `h`.
            rw [show (a.succ : ℕ) = n from congrArg Fin.val hasucc] at h
            exact h
          rw [← hasucc, e7MinusculeWeight_succ_eq_reflection_parent]
          exact MulAction.mem_orbit_of_mem_orbit
            (RootPairing.weylGroup.ofIdx e7SimplyConnectedRootDatum
              (e7SimpleIndex (e7MinusculeParentNode a)))
            (ih (e7MinusculeParent a) hparent (e7MinusculeParent a).isLt)
  exact aux a a.isLt

/-- **The explicit table is exactly the Weyl orbit of the seventh fundamental weight `ϖ₇`.** -/
theorem range_e7MinusculeWeight :
    Set.range e7MinusculeWeight =
      MulAction.orbit e7SimplyConnectedRootDatum.weylGroup
        (Pi.single 6 1 : Fin 7 → ℤ) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    exact e7MinusculeWeight_mem_orbit a
  · rintro x ⟨w, rfl⟩
    obtain ⟨l, rfl⟩ := exists_wordProd_eq e7SimplyConnectedRootDatum
      e7SimplyConnectedBase w
    induction l with
    | nil =>
        refine ⟨0, ?_⟩
        simp
    | cons i l ih =>
        obtain ⟨a, ha⟩ := ih
        -- Unfold the orbit witness's coercion so the induction hypothesis is stated in terms of
        -- the explicit simple-reflection word.
        change e7MinusculeWeight a =
          wordProd e7SimplyConnectedRootDatum e7SimplyConnectedBase l •
            (Pi.single 6 1 : Fin 7 → ℤ) at ha
        let j : Fin 7 := ⟨(i : Fin 126), mem_support_e7SimplyConnectedBase.mp i.property⟩
        have hij : (i : Fin 126) = e7SimpleIndex j := Fin.ext (by simp [j])
        refine ⟨e7MinusculeReflection j a, ?_⟩
        rw [wordProd_cons]
        -- Expose the product in the Weyl action so `mul_smul` and the reflection API apply.
        change e7MinusculeWeight (e7MinusculeReflection j a) =
          (RootPairing.weylGroup.ofIdx e7SimplyConnectedRootDatum (i : Fin 126) *
            wordProd e7SimplyConnectedRootDatum e7SimplyConnectedBase l) •
              (Pi.single 6 1 : Fin 7 → ℤ)
        rw [mul_smul, RootPairing.weylGroup.ofIdx_smul, ← ha, hij,
          RootPairing.Equiv.reflection_smul,
          e7SimplyConnectedRootDatum_reflection_e7MinusculeWeight]

/-- The Weyl orbit of `ϖ₇` has fifty-six elements. -/
theorem ncard_orbit_e7MinusculeWeight :
    (MulAction.orbit e7SimplyConnectedRootDatum.weylGroup
      (Pi.single 6 1 : Fin 7 → ℤ)).ncard = 56 := by
  rw [← range_e7MinusculeWeight]
  simpa using Set.ncard_range_of_injective e7MinusculeWeight_injective

/-! ## Generation of the character lattice -/

/-- **The fifty-six minuscule weights span the full type-`E₇` character lattice.** In
particular, a diagonal torus acting with these weights is represented faithfully. -/
theorem span_range_e7MinusculeWeight_eq_top :
    Submodule.span ℤ (Set.range e7MinusculeWeight) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 7)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  let S := Submodule.span ℤ (Set.range e7MinusculeWeight)
  have h (a : Fin 56) : e7MinusculeWeight a ∈ S :=
    Submodule.subset_span (Set.mem_range_self a)
  fin_cases i
  -- In each branch the displayed, kernel-checked identity expresses the corresponding standard
  -- basis vector as an integral combination of seven weights from the table.
  · change Pi.single (0 : Fin 7) 1 ∈ S
    rw [show Pi.single (0 : Fin 7) 1 =
        e7MinusculeWeight 0 + e7MinusculeWeight 1 + e7MinusculeWeight 2 +
          e7MinusculeWeight 3 - e7MinusculeWeight 4 - e7MinusculeWeight 6 -
            2 • e7MinusculeWeight 9 by decide +kernel]
    exact S.sub_mem
      (S.sub_mem (S.sub_mem
        (S.add_mem (S.add_mem (S.add_mem (h 0) (h 1)) (h 2)) (h 3)) (h 4)) (h 6))
      (S.smul_mem 2 (h 9))
  · change Pi.single (1 : Fin 7) 1 ∈ S
    rw [show Pi.single (1 : Fin 7) 1 =
      e7MinusculeWeight 4 + e7MinusculeWeight 6 + e7MinusculeWeight 9 by decide +kernel]
    exact S.add_mem (S.add_mem (h 4) (h 6)) (h 9)
  · change Pi.single (2 : Fin 7) 1 ∈ S
    rw [show Pi.single (2 : Fin 7) 1 =
        e7MinusculeWeight 0 + e7MinusculeWeight 1 + e7MinusculeWeight 2 +
          e7MinusculeWeight 3 - e7MinusculeWeight 6 - e7MinusculeWeight 9 by
      decide +kernel]
    exact S.sub_mem
      (S.sub_mem (S.add_mem (S.add_mem (S.add_mem (h 0) (h 1)) (h 2)) (h 3)) (h 6))
      (h 9)
  · change Pi.single (3 : Fin 7) 1 ∈ S
    rw [show Pi.single (3 : Fin 7) 1 =
        e7MinusculeWeight 0 + e7MinusculeWeight 1 + e7MinusculeWeight 2 +
          e7MinusculeWeight 3 by decide +kernel]
    exact S.add_mem (S.add_mem (S.add_mem (h 0) (h 1)) (h 2)) (h 3)
  · change Pi.single (4 : Fin 7) 1 ∈ S
    rw [show Pi.single (4 : Fin 7) 1 =
        e7MinusculeWeight 0 + e7MinusculeWeight 1 + e7MinusculeWeight 2 by
      decide +kernel]
    exact S.add_mem (S.add_mem (h 0) (h 1)) (h 2)
  · change Pi.single (5 : Fin 7) 1 ∈ S
    rw [show Pi.single (5 : Fin 7) 1 =
        e7MinusculeWeight 0 + e7MinusculeWeight 1 by decide +kernel]
    exact S.add_mem (h 0) (h 1)
  · change Pi.single (6 : Fin 7) 1 ∈ S
    rw [show Pi.single (6 : Fin 7) 1 = e7MinusculeWeight 0 by decide +kernel]
    exact h 0

end TauCeti.DynkinType
