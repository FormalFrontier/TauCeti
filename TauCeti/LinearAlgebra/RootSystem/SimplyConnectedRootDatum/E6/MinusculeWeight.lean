/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# The minuscule weight orbit of type E6

This file enumerates the Weyl orbit of the first fundamental weight of the pinned simply connected
root datum `TauCeti.DynkinType.e6SimplyConnectedRootDatum`. The twenty-seven weights are expressed
in the fundamental-weight basis `Fin 6 → ℤ`. The first weight is `ϖ₁`, and the table is closed under
the six Bourbaki-numbered simple reflections through explicit permutations of `Fin 27`.

The reflection equation is the key interface for the future 27-dimensional minuscule module: a
simple root operator can move a coordinate basis vector only when the corresponding weight pairs
to `1` or `-1`. The table records that every such pairing lies in `{-1, 0, 1}`, identifies the table
with the full Weyl orbit, and proves that its weights span the complete character lattice. The last
property is what lets the represented weight torus of an admissible minuscule lattice be a closed
immersion, rather than seeing only the index-three root lattice of the adjoint representation.

The table is *not* stable under the pinned diagram symmetry `TauCeti.graphPermE6`, which exchanges
`ϖ₁` and `ϖ₆` and so carries the weights of `V(ϖ₁)` to those of `V(ϖ₆) = V(ϖ₁)ˣ`, their negatives.
The last two sections make that exchange explicit and repair it: `e6MinusculeGraphDualPerm` is the
involution of the index set implementing it, and `e6DoubledMinusculeWeight` is the fifty-four-weight
family of `V(ϖ₁) ⊕ V(ϖ₆)`, which is stable, is still injective, and still spans. A carrier inherits
a symmetry of its numbered data only when its weight family is equivariant, the hypothesis
`wt (π i) (τ k) = wt i k` of
`TauCeti.UniversalEnvelopingAlgebra.kostantToralNumberedSymmetryIso`, which the doubled family
meets and the minuscule family alone does not.

No representation or group scheme is constructed here. This is the pinned weight-diagram input
for the type-`E₆` full-weight Chevalley--Demazure carrier in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the CFSG statement roadmap,
the doubled family being what its graph-twisted family `²E₆(q)` needs where `E₆(q)` does not.

## Main declarations

* `TauCeti.DynkinType.e6MinusculeWeight`: the twenty-seven weights in fundamental coordinates.
* `TauCeti.DynkinType.e6MinusculeReflection`: the permutation induced by a simple reflection.
* `TauCeti.DynkinType.e6MinusculeWeight_reflection`: the simple-reflection equation.
* `TauCeti.DynkinType.range_e6MinusculeWeight`: the table is exactly the Weyl orbit of `ϖ₁`.
* `TauCeti.DynkinType.span_range_e6MinusculeWeight_eq_top`: the weights span the character lattice.
* `TauCeti.DynkinType.e6MinusculeGraphDualPerm`: the involution of the index set induced by the
  diagram symmetry followed by duality, and
  `TauCeti.DynkinType.e6MinusculeWeight_e6MinusculeGraphDualPerm` its defining equation.
* `TauCeti.DynkinType.e6MinusculeWeight_comp_graphPermE6_notMem_range`: the twenty-seven
  weights are not stable under the diagram symmetry.
* `TauCeti.DynkinType.e6DoubledMinusculeWeight`: the fifty-four weights of `V(ϖ₁) ⊕ V(ϖ₆)`, with
  `TauCeti.DynkinType.e6DoubledMinusculeWeight_injective`,
  `TauCeti.DynkinType.span_range_e6DoubledMinusculeWeight_eq_top` and
  `TauCeti.DynkinType.e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm`, its equivariance for
  the diagram symmetry.

## References

The node numbering and the choice of the minuscule weight `ϖ₁` follow Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4--6*, Plate V. The minuscule-orbit description of the 27-dimensional
representation follows J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*,
§13.4, and J. C. Jantzen, *Representations of Algebraic Groups*, II.2. That the diagram
automorphism exchanges the two twenty-seven dimensional representations, and the conventions for
`²E₆(q)` that makes this relevant to, are R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

namespace TauCeti.DynkinType

open Set

/-! ## The weight table -/

/-- **The twenty-seven weights in the Weyl orbit of the type-`E₆` minuscule weight `ϖ₁`.**

Coordinates are pairings with the six Bourbaki-numbered simple coroots. The ordering begins at
`ϖ₁ = (1, 0, 0, 0, 0, 0)` and then lists weights reached successively by simple reflections; no
mathematical structure depends on the ordering. -/
def e6MinusculeWeight : Fin 27 → Fin 6 → ℤ := ![
  ![1, 0, 0, 0, 0, 0], ![-1, 0, 1, 0, 0, 0], ![0, 0, -1, 1, 0, 0],
  ![0, 1, 0, -1, 1, 0], ![0, -1, 0, 0, 1, 0], ![0, 1, 0, 0, -1, 1],
  ![0, -1, 0, 1, -1, 1], ![0, 1, 0, 0, 0, -1], ![0, 0, 1, -1, 0, 1],
  ![0, -1, 0, 1, 0, -1], ![1, 0, -1, 0, 0, 1], ![0, 0, 1, -1, 1, -1],
  ![-1, 0, 0, 0, 0, 1], ![1, 0, -1, 0, 1, -1], ![0, 0, 1, 0, -1, 0],
  ![-1, 0, 0, 0, 1, -1], ![1, 0, -1, 1, -1, 0], ![-1, 0, 0, 1, -1, 0],
  ![1, 1, 0, -1, 0, 0], ![-1, 1, 1, -1, 0, 0], ![1, -1, 0, 0, 0, 0],
  ![-1, -1, 1, 0, 0, 0], ![0, 1, -1, 0, 0, 0], ![0, -1, -1, 1, 0, 0],
  ![0, 0, 0, -1, 1, 0], ![0, 0, 0, 0, -1, 1], ![0, 0, 0, 0, 0, -1]]

/-- The twenty-seven minuscule weights are pairwise distinct. -/
theorem e6MinusculeWeight_injective : Function.Injective e6MinusculeWeight := by
  decide +kernel +revert

/-- The first weight in the table is the first fundamental weight `ϖ₁`. -/
@[simp]
theorem e6MinusculeWeight_zero : e6MinusculeWeight 0 = Pi.single 0 1 := by
  decide

/-- Every pairing of an `E₆` minuscule weight with a simple coroot is `-1`, `0`, or `1`. -/
theorem e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (a : Fin 27) (i : Fin 6) :
    e6MinusculeWeight a i = -1 ∨ e6MinusculeWeight a i = 0 ∨
      e6MinusculeWeight a i = 1 := by
  fin_cases a <;> fin_cases i <;> decide

/-! ## Simple reflections -/

private def e6MinusculeReflectionIndex : Fin 6 → Fin 27 → Fin 27 := ![
  ![1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 12, 11, 10, 15, 14, 13, 17, 16, 19, 18, 21, 20, 22, 23,
    24, 25, 26],
  ![0, 1, 2, 4, 3, 6, 5, 9, 8, 7, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 18, 19, 23, 22,
    24, 25, 26],
  ![0, 2, 1, 3, 4, 5, 6, 7, 10, 9, 8, 13, 12, 11, 16, 15, 14, 17, 18, 22, 20, 23, 19, 21,
    24, 25, 26],
  ![0, 1, 3, 2, 4, 5, 8, 7, 6, 11, 10, 9, 12, 13, 14, 15, 18, 19, 16, 17, 20, 21, 22, 24,
    23, 25, 26],
  ![0, 1, 2, 5, 6, 3, 4, 7, 8, 9, 10, 14, 12, 16, 11, 17, 13, 15, 18, 19, 20, 21, 22, 23,
    25, 24, 26],
  ![0, 1, 2, 3, 4, 7, 9, 5, 11, 6, 13, 8, 15, 10, 14, 12, 16, 17, 18, 19, 20, 21, 22, 23,
    24, 26, 25]]

private theorem e6MinusculeReflectionIndex_involutive (i : Fin 6) :
    Function.Involutive (e6MinusculeReflectionIndex i) := by
  fin_cases i <;> intro a <;> fin_cases a <;> decide

/-- **The permutation of the twenty-seven minuscule weights induced by the `i`-th simple
reflection.** -/
def e6MinusculeReflection (i : Fin 6) : Equiv.Perm (Fin 27) :=
  (e6MinusculeReflectionIndex_involutive i).toPerm

/-- Applying the same simple reflection twice fixes every index in the weight table. -/
@[simp]
theorem e6MinusculeReflection_apply_apply (i : Fin 6) (a : Fin 27) :
    e6MinusculeReflection i (e6MinusculeReflection i a) = a :=
  e6MinusculeReflectionIndex_involutive i a

private theorem e6MinusculeWeight_reflection_table (i : Fin 6) (a : Fin 27) :
    e6MinusculeWeight (e6MinusculeReflection i a) =
      e6MinusculeWeight a - e6MinusculeWeight a i • CartanMatrix.E 6 i := by
  rw [CartanMatrix.E_six_eq]
  decide +kernel +revert

/-- **The coordinate equation for a simple reflection on the minuscule weights.** Reflection in
the `i`-th simple root subtracts the pairing with the `i`-th simple coroot times that root. -/
theorem e6MinusculeWeight_reflection (i : Fin 6) (a : Fin 27) :
    e6MinusculeWeight (e6MinusculeReflection i a) =
      e6MinusculeWeight a -
        e6MinusculeWeight a i • e6Root (e6SimpleIndex i) := by
  rw [root_e6SimpleIndex]
  exact e6MinusculeWeight_reflection_table i a

/-- A simple reflection fixes a minuscule weight exactly when its simple-coroot coordinate is
zero. -/
@[simp]
theorem e6MinusculeReflection_eq_self_iff (i : Fin 6) (a : Fin 27) :
    e6MinusculeReflection i a = a ↔ e6MinusculeWeight a i = 0 := by
  constructor
  · intro h
    have hweight := congrArg e6MinusculeWeight h
    rw [e6MinusculeWeight_reflection] at hweight
    have hi := congrFun hweight i
    simp [root_e6SimpleIndex, CartanMatrix.E_six_eq] at hi
    fin_cases i <;> simp_all
  · intro h
    apply e6MinusculeWeight_injective
    rw [e6MinusculeWeight_reflection]
    simp [h]

/-- The explicit permutation agrees with reflection in the pinned simply connected root datum. -/
@[simp]
theorem e6SimplyConnectedRootDatum_reflection_e6MinusculeWeight
    (i : Fin 6) (a : Fin 27) :
    e6SimplyConnectedRootDatum.reflection (e6SimpleIndex i) (e6MinusculeWeight a) =
      e6MinusculeWeight (e6MinusculeReflection i a) := by
  rw [e6MinusculeWeight_reflection]
  simp [RootPairing.reflection_apply]

/-! ## The Weyl orbit -/

/-- A parent of every non-highest weight in the reflection graph. -/
private def e6MinusculeParent : Fin 26 → Fin 27 := ![
  0, 1, 2, 3, 3, 4, 5, 6, 6, 8, 8, 10, 10, 11, 12, 13, 15, 16, 17, 18, 19, 19, 21, 23, 24,
  25]

/-- The simple reflection carrying each parent to its child. -/
private def e6MinusculeParentNode : Fin 26 → Fin 6 := ![
  0, 2, 3, 1, 4, 4, 5, 3, 5, 2, 5, 0, 5, 4, 5, 4, 4, 3, 3, 1, 1, 2, 2, 3, 4, 5]

private theorem e6MinusculeParent_lt_succ (a : Fin 26) :
    (e6MinusculeParent a : ℕ) < (a.succ : ℕ) := by
  fin_cases a <;> decide

private theorem e6MinusculeWeight_succ_eq_reflection_parent (a : Fin 26) :
    e6MinusculeWeight a.succ =
      e6SimplyConnectedRootDatum.reflection
        (e6SimpleIndex (e6MinusculeParentNode a))
        (e6MinusculeWeight (e6MinusculeParent a)) := by
  rw [e6SimplyConnectedRootDatum_reflection_e6MinusculeWeight]
  fin_cases a <;> decide

private theorem e6MinusculeWeight_mem_orbit (a : Fin 27) :
    e6MinusculeWeight a ∈
      MulAction.orbit e6SimplyConnectedRootDatum.weylGroup
        (Pi.single 0 1 : Fin 6 → ℤ) := by
  have aux : ∀ n, ∀ hn : n < 27, e6MinusculeWeight ⟨n, hn⟩ ∈
      MulAction.orbit e6SimplyConnectedRootDatum.weylGroup
        (Pi.single 0 1 : Fin 6 → ℤ) := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hzero : n = 0
        · subst n
          -- The proof that the dependent index lies in `Fin 27` is definitionally irrelevant;
          -- expose the zero index so the public highest-weight lemma applies.
          change e6MinusculeWeight 0 ∈
            MulAction.orbit e6SimplyConnectedRootDatum.weylGroup
              (Pi.single 0 1 : Fin 6 → ℤ)
          rw [e6MinusculeWeight_zero]
          exact MulAction.mem_orbit_self _
        · let a : Fin 26 := ⟨n - 1, by omega⟩
          have hasucc : a.succ = (⟨n, hn⟩ : Fin 27) := by
            apply Fin.ext
            simp [a]
            omega
          have hparent : (e6MinusculeParent a : ℕ) < n := by
            have h := e6MinusculeParent_lt_succ a
            -- `hasucc` is an equality of `Fin` values; applying `Fin.val` exposes exactly the
            -- natural-number endpoint in `h` without changing either index.
            rw [show (a.succ : ℕ) = n from congrArg Fin.val hasucc] at h
            exact h
          rw [← hasucc, e6MinusculeWeight_succ_eq_reflection_parent]
          exact MulAction.mem_orbit_of_mem_orbit
            (RootPairing.weylGroup.ofIdx e6SimplyConnectedRootDatum
              (e6SimpleIndex (e6MinusculeParentNode a)))
            (ih (e6MinusculeParent a) hparent (e6MinusculeParent a).isLt)
  exact aux a a.isLt

/-- **The explicit table is exactly the Weyl orbit of the first fundamental weight `ϖ₁`.** -/
theorem range_e6MinusculeWeight :
    Set.range e6MinusculeWeight =
      MulAction.orbit e6SimplyConnectedRootDatum.weylGroup
        (Pi.single 0 1 : Fin 6 → ℤ) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    exact e6MinusculeWeight_mem_orbit a
  · rintro x ⟨w, rfl⟩
    obtain ⟨l, rfl⟩ := exists_wordProd_eq e6SimplyConnectedRootDatum
      e6SimplyConnectedBase w
    induction l with
    | nil =>
        refine ⟨0, ?_⟩
        simp
    | cons i l ih =>
        obtain ⟨a, ha⟩ := ih
        -- Unfold the orbit witness's coercion to the Weyl action so `ha` states the induction
        -- invariant directly in terms of `wordProd`.
        change e6MinusculeWeight a =
          wordProd e6SimplyConnectedRootDatum e6SimplyConnectedBase l •
            (Pi.single 0 1 : Fin 6 → ℤ) at ha
        let j : Fin 6 := ⟨(i : Fin 72), mem_e6SimplyConnectedBase_support.mp i.property⟩
        have hij : (i : Fin 72) = e6SimpleIndex j := Fin.ext (by simp [j])
        refine ⟨e6MinusculeReflection j a, ?_⟩
        rw [wordProd_cons]
        -- The range witness is definitionally the Weyl action; expose its product so `mul_smul`
        -- and the reflection-action API can rewrite it.
        change e6MinusculeWeight (e6MinusculeReflection j a) =
          (RootPairing.weylGroup.ofIdx e6SimplyConnectedRootDatum (i : Fin 72) *
            wordProd e6SimplyConnectedRootDatum e6SimplyConnectedBase l) •
              (Pi.single 0 1 : Fin 6 → ℤ)
        rw [mul_smul, RootPairing.weylGroup.ofIdx_smul, ← ha, hij,
          RootPairing.Equiv.reflection_smul,
          e6SimplyConnectedRootDatum_reflection_e6MinusculeWeight]

/-- The Weyl orbit of `ϖ₁` has twenty-seven elements. -/
theorem ncard_orbit_e6MinusculeWeight :
    (MulAction.orbit e6SimplyConnectedRootDatum.weylGroup
      (Pi.single 0 1 : Fin 6 → ℤ)).ncard = 27 := by
  rw [← range_e6MinusculeWeight]
  simpa using Set.ncard_range_of_injective e6MinusculeWeight_injective

/-! ## Generation of the character lattice -/

/-- **The twenty-seven minuscule weights span the full type-`E₆` character lattice.** In
particular, a diagonal torus acting with these weights is represented faithfully. -/
theorem span_range_e6MinusculeWeight_eq_top :
    Submodule.span ℤ (Set.range e6MinusculeWeight) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 6)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  let S := Submodule.span ℤ (Set.range e6MinusculeWeight)
  have h (a : Fin 27) : e6MinusculeWeight a ∈ S :=
    Submodule.subset_span (Set.mem_range_self a)
  fin_cases i
  -- In each branch `Pi.basisFun` is definitionally the corresponding `Pi.single`, while `S`
  -- unfolds to the span in the goal. The displayed equalities are explicit identities from the
  -- weight table, after which submodule closure proves membership.
  · change Pi.single (0 : Fin 6) 1 ∈ S
    rw [show Pi.single (0 : Fin 6) 1 = e6MinusculeWeight 0 by decide +kernel]
    exact h 0
  · change Pi.single (1 : Fin 6) 1 ∈ S
    rw [show Pi.single (1 : Fin 6) 1 =
        e6MinusculeWeight 3 + e6MinusculeWeight 5 + e6MinusculeWeight 9 by
      decide +kernel]
    exact S.add_mem (S.add_mem (h 3) (h 5)) (h 9)
  · change Pi.single (2 : Fin 6) 1 ∈ S
    rw [show Pi.single (2 : Fin 6) 1 =
        e6MinusculeWeight 0 + e6MinusculeWeight 1 by decide +kernel]
    exact S.add_mem (h 0) (h 1)
  · change Pi.single (3 : Fin 6) 1 ∈ S
    rw [show Pi.single (3 : Fin 6) 1 =
        e6MinusculeWeight 0 + e6MinusculeWeight 1 + e6MinusculeWeight 2 by
      decide +kernel]
    exact S.add_mem (S.add_mem (h 0) (h 1)) (h 2)
  · change Pi.single (4 : Fin 6) 1 ∈ S
    rw [show Pi.single (4 : Fin 6) 1 =
        e6MinusculeWeight 0 + e6MinusculeWeight 1 + e6MinusculeWeight 2 -
          e6MinusculeWeight 5 - e6MinusculeWeight 9 by decide +kernel]
    exact S.sub_mem (S.sub_mem (S.add_mem (S.add_mem (h 0) (h 1)) (h 2)) (h 5)) (h 9)
  · change Pi.single (5 : Fin 6) 1 ∈ S
    rw [show Pi.single (5 : Fin 6) 1 =
        e6MinusculeWeight 0 + e6MinusculeWeight 1 + e6MinusculeWeight 2 -
          e6MinusculeWeight 3 - e6MinusculeWeight 5 - 2 • e6MinusculeWeight 9 by
      decide +kernel]
    exact S.sub_mem
      (S.sub_mem (S.sub_mem (S.add_mem (S.add_mem (h 0) (h 1)) (h 2)) (h 3)) (h 5))
      (S.smul_mem 2 (h 9))

/-! ## The diagram symmetry on the weight table -/

/-- The index table of `e6MinusculeGraphDualPerm`, matching each minuscule weight with the one whose
negative is its image under the diagram symmetry. -/
private def e6MinusculeGraphDualIndex : Fin 27 → Fin 27 :=
  ![26, 25, 24, 23, 22, 21, 19, 20, 17, 18, 15, 16, 12, 13, 14, 10, 11, 8, 9, 6, 7, 5, 4, 3, 2, 1,
    0]

private theorem e6MinusculeGraphDualIndex_involutive :
    Function.Involutive e6MinusculeGraphDualIndex := fun _ => by decide +kernel +revert

/-- **The permutation of the twenty-seven minuscule weights induced by the `E₆` diagram symmetry
followed by duality.** The symmetry `TauCeti.graphPermE6` does not preserve the weight table, so
this permutation records the composite of that symmetry with duality: it matches the index `a` with
the index whose weight is the negative of the image of the `a`-th weight. -/
def e6MinusculeGraphDualPerm : Equiv.Perm (Fin 27) :=
  e6MinusculeGraphDualIndex_involutive.toPerm

/-- The graph-and-duality permutation of the minuscule weight table is an involution, as the
diagram symmetry it realizes is. -/
@[simp]
theorem e6MinusculeGraphDualPerm_apply_apply (a : Fin 27) :
    e6MinusculeGraphDualPerm (e6MinusculeGraphDualPerm a) = a :=
  e6MinusculeGraphDualIndex_involutive a

/-- The graph-and-duality permutation of the minuscule weight table is its own inverse. -/
@[simp]
theorem e6MinusculeGraphDualPerm_symm :
    e6MinusculeGraphDualPerm.symm = e6MinusculeGraphDualPerm :=
  e6MinusculeGraphDualIndex_involutive.toPerm_symm

/-- The node table of `TauCeti.graphPermE6`. The permutation itself lives in another module, so
the kernel cannot evaluate it while checking the weight table below; this table can be evaluated
and is identified with it by `graphPermE6_apply_eq_e6GraphNode`. -/
private def e6GraphNode : Fin 6 → Fin 6 := ![5, 1, 4, 3, 2, 0]

private theorem graphPermE6_apply_eq_e6GraphNode (i : Fin 6) : graphPermE6 i = e6GraphNode i := by
  fin_cases i <;> simp [e6GraphNode]

private theorem e6MinusculeWeight_e6MinusculeGraphDualIndex_apply (a : Fin 27) (i : Fin 6) :
    e6MinusculeWeight (e6MinusculeGraphDualIndex a) i = -e6MinusculeWeight a (e6GraphNode i) := by
  decide +kernel +revert

/-- **The diagram symmetry carries each minuscule weight to the negative of another one.** The
symmetry exchanges `ϖ₁` and `ϖ₆`, so on representations it carries `V(ϖ₁)` to
`V(ϖ₆) = V(ϖ₁)ˣ`, whose weights are the negatives of these. -/
theorem e6MinusculeWeight_e6MinusculeGraphDualPerm_apply (a : Fin 27) (i : Fin 6) :
    e6MinusculeWeight (e6MinusculeGraphDualPerm a) i = -e6MinusculeWeight a (graphPermE6 i) := by
  rw [graphPermE6_apply_eq_e6GraphNode]
  exact e6MinusculeWeight_e6MinusculeGraphDualIndex_apply a i

/-- The functional form of `e6MinusculeWeight_e6MinusculeGraphDualPerm_apply`. -/
theorem e6MinusculeWeight_e6MinusculeGraphDualPerm (a : Fin 27) :
    e6MinusculeWeight (e6MinusculeGraphDualPerm a) = -(e6MinusculeWeight a ∘ graphPermE6) := by
  funext i
  simpa using e6MinusculeWeight_e6MinusculeGraphDualPerm_apply a i

private theorem exists_e6MinusculeWeight_apply_ne_neg (a b : Fin 27) :
    ∃ i, e6MinusculeWeight a i ≠ -e6MinusculeWeight b i := by
  decide +kernel +revert

/-- **The diagram symmetry moves every minuscule weight off the table.** Its image is the negative
of a minuscule weight, and no minuscule weight is the negative of another; at the highest weight
`ϖ₁` this is the image `ϖ₆`, not a weight of `V(ϖ₁)`. So a carrier built from this weight family
alone does not inherit the diagram automorphism. -/
theorem e6MinusculeWeight_comp_graphPermE6_notMem_range (a : Fin 27) :
    e6MinusculeWeight a ∘ graphPermE6 ∉ range e6MinusculeWeight := by
  rintro ⟨b, hb⟩
  obtain ⟨i, hi⟩ := exists_e6MinusculeWeight_apply_ne_neg b (e6MinusculeGraphDualPerm a)
  -- The assumed witness reads `e6MinusculeWeight b i` as the image of the `a`-th weight, which the
  -- defining equation reads back as the negative of the `e6MinusculeGraphDualPerm a`-th one.
  exact hi (by simp [congrFun hb i, e6MinusculeWeight_e6MinusculeGraphDualPerm_apply a i])

/-! ## The doubled weight family -/

/-- **The fifty-four weights of the type-`E₆` representation `V(ϖ₁) ⊕ V(ϖ₆)`**, in coordinates
given by the pairings with the six Bourbaki-numbered simple coroots. The left summand carries the
twenty-seven minuscule weights and the right summand their negatives, which are the weights of the
dual representation `V(ϖ₆)`. -/
def e6DoubledMinusculeWeight : Fin 27 ⊕ Fin 27 → Fin 6 → ℤ :=
  Sum.elim e6MinusculeWeight fun a => -e6MinusculeWeight a

@[simp]
theorem e6DoubledMinusculeWeight_inl (a : Fin 27) :
    e6DoubledMinusculeWeight (.inl a) = e6MinusculeWeight a :=
  (rfl)

@[simp]
theorem e6DoubledMinusculeWeight_inr (a : Fin 27) :
    e6DoubledMinusculeWeight (.inr a) = -e6MinusculeWeight a :=
  (rfl)

/-- The doubled family is closed under negation, which exchanges its two summands. -/
theorem neg_e6DoubledMinusculeWeight (x : Fin 27 ⊕ Fin 27) :
    -e6DoubledMinusculeWeight x = e6DoubledMinusculeWeight (Equiv.sumComm _ _ x) := by
  cases x <;> simp

/-- **The fifty-four weights of `V(ϖ₁) ⊕ V(ϖ₆)` are pairwise distinct.** No minuscule weight is
the negative of another, all twenty-seven of them lying in one nontrivial coset of the root
lattice. -/
theorem e6DoubledMinusculeWeight_injective : Function.Injective e6DoubledMinusculeWeight := by
  have key (a b : Fin 27) : e6MinusculeWeight a ≠ -e6MinusculeWeight b := by
    obtain ⟨i, hi⟩ := exists_e6MinusculeWeight_apply_ne_neg a b
    exact fun h => hi (by simpa using congrFun h i)
  rintro (a | a) (b | b) h <;>
    simp only [e6DoubledMinusculeWeight_inl, e6DoubledMinusculeWeight_inr] at h
  · exact congrArg Sum.inl (e6MinusculeWeight_injective h)
  · exact absurd h (key a b)
  · exact absurd h.symm (key b a)
  · exact congrArg Sum.inr (e6MinusculeWeight_injective (neg_injective h))

/-- The doubled minuscule weight family has fifty-four distinct members. -/
theorem ncard_range_e6DoubledMinusculeWeight :
    (range e6DoubledMinusculeWeight).ncard = 54 := by
  simpa using Set.ncard_range_of_injective e6DoubledMinusculeWeight_injective

/-- **The doubled minuscule weights span the full type-`E₆` character lattice.** They include the
twenty-seven minuscule weights, which already do. -/
theorem span_range_e6DoubledMinusculeWeight_eq_top :
    Submodule.span ℤ (range e6DoubledMinusculeWeight) = ⊤ := by
  refine top_unique (span_range_e6MinusculeWeight_eq_top ▸ Submodule.span_mono ?_)
  rintro _ ⟨a, rfl⟩
  exact ⟨.inl a, rfl⟩

/-- **The permutation of the doubled index set realizing the `E₆` diagram symmetry.** It exchanges
the two summands along `e6MinusculeGraphDualPerm`, which is what makes the doubled weight family
equivariant where the minuscule family alone is not. -/
def e6DoubledMinusculeGraphPerm : Equiv.Perm (Fin 27 ⊕ Fin 27) :=
  (Equiv.sumCongr e6MinusculeGraphDualPerm e6MinusculeGraphDualPerm).trans (Equiv.sumComm _ _)

@[simp]
theorem e6DoubledMinusculeGraphPerm_inl (a : Fin 27) :
    e6DoubledMinusculeGraphPerm (.inl a) = .inr (e6MinusculeGraphDualPerm a) :=
  (rfl)

@[simp]
theorem e6DoubledMinusculeGraphPerm_inr (a : Fin 27) :
    e6DoubledMinusculeGraphPerm (.inr a) = .inl (e6MinusculeGraphDualPerm a) :=
  (rfl)

/-- The permutation realizing the diagram symmetry on the doubled index set is an involution. -/
@[simp]
theorem e6DoubledMinusculeGraphPerm_apply_apply (x : Fin 27 ⊕ Fin 27) :
    e6DoubledMinusculeGraphPerm (e6DoubledMinusculeGraphPerm x) = x := by
  cases x <;> simp

/-- The permutation realizing the diagram symmetry on the doubled index set is its own inverse. -/
@[simp]
theorem e6DoubledMinusculeGraphPerm_symm :
    e6DoubledMinusculeGraphPerm.symm = e6DoubledMinusculeGraphPerm :=
  Equiv.ext fun x => by
    rw [Equiv.symm_apply_eq, e6DoubledMinusculeGraphPerm_apply_apply]

/-- **The doubled minuscule weight family is equivariant for the `E₆` diagram symmetry.** This is
the hypothesis `wt (π i) (τ k) = wt i k` under which a numbered symmetry of a Kostant toral-closure
carrier extends to an automorphism of the carrier, and it is what
`e6MinusculeWeight_comp_graphPermE6_notMem_range` denies to the minuscule family alone. -/
theorem e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm (x : Fin 27 ⊕ Fin 27) (i : Fin 6) :
    e6DoubledMinusculeWeight (e6DoubledMinusculeGraphPerm x) i =
      e6DoubledMinusculeWeight x (graphPermE6 i) := by
  cases x <;> simp [e6MinusculeWeight_e6MinusculeGraphDualPerm_apply]

end TauCeti.DynkinType
