/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import TauCeti.GroupTheory.Commutator

/-!
# Derived words and solvable groups

The `n`th derived word evaluates a perfect binary argument tree of depth `n` by balanced
commutators: the zeroth word is one group element, and the successor word is the commutator of two
copies of the preceding word. This file proves that its values generate the `n`th derived subgroup.
Consequently, a group is solvable exactly when one derived word is identically one. It also records
the characterization of solvability for direct products via the two surjective projections and the
converse product instance.

The identity formulation is useful when a group is represented by an affine scheme: an identity
between derived words can be checked on a schematically dense family of points, while the
subgroup-valued definition of the derived series cannot be compared pointwise in that way.

## Main declarations

* `TauCeti.isSolvable_prod_iff`: `G × H` is solvable if and only if both `G` and `H` are.
* `TauCeti.DerivedWordArgs`: the recursively paired arguments of a derived word.
* `TauCeti.derivedWord`: the balanced iterated commutator word.
* `TauCeti.map_derivedWord`: derived words commute with group homomorphisms.
* `TauCeti.derivedSeries_eq_closure_range_derivedWord`: the values of the `n`th derived word
  generate the `n`th derived subgroup.
* `TauCeti.derivedWord_mem_derivedSeries`: derived-word values lie in the corresponding derived
  subgroup.
* `TauCeti.derivedSeries_eq_bot_iff_derivedWord_eq_one`: a fixed derived subgroup vanishes exactly
  when its derived word is identically one.
* `TauCeti.isSolvable_iff_exists_derivedWord_eq_one`: solvability is equivalent to a derived-word
  identity.

This is a prerequisite for descending geometric solvability along schematically dense morphisms
from smooth affine groups. That descent supplies the multiplication-image step in the construction
of the solvable radical in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open scoped commutatorElement

namespace TauCeti

/-- A direct product of groups is solvable exactly when both of its factors are. -/
@[simp]
theorem isSolvable_prod_iff {G H : Type*} [Group G] [Group H] :
    Group.IsSolvable (G × H) ↔ Group.IsSolvable G ∧ Group.IsSolvable H :=
  ⟨fun _ ↦ ⟨Group.isSolvable_of_surjective (f := MonoidHom.fst G H) fun x ↦ ⟨(x, 1), rfl⟩,
      Group.isSolvable_of_surjective (f := MonoidHom.snd G H) fun x ↦ ⟨(1, x), rfl⟩⟩,
    fun ⟨_, _⟩ ↦ inferInstance⟩

universe u v

/-- The argument trees for derived words. A tree at depth zero is one group element, and a tree at
successor depth consists of two argument trees of the preceding depth. -/
inductive DerivedWordArgs (G : Type u) : ℕ → Type u
  | leaf : G → DerivedWordArgs G 0
  | node : DerivedWordArgs G n → DerivedWordArgs G n → DerivedWordArgs G (n + 1)

namespace DerivedWordArgs

/-- Apply a function to every entry in the arguments of a derived word. -/
def map {G : Type u} {H : Type v} (f : G → H) :
    (n : ℕ) → DerivedWordArgs G n → DerivedWordArgs H n
  | 0, .leaf x => .leaf (f x)
  | _ + 1, .node x y => .node (map f _ x) (map f _ y)

@[simp]
theorem map_leaf {G : Type u} {H : Type v} (f : G → H) (x : G) :
    map f 0 (.leaf x) = .leaf (f x) :=
  (rfl)

@[simp]
theorem map_node {G : Type u} {H : Type v} (f : G → H) (n : ℕ)
    (x y : DerivedWordArgs G n) :
    map f (n + 1) (.node x y) = .node (map f n x) (map f n y) :=
  (rfl)

/-- Mapping the identity function leaves derived-word arguments unchanged. -/
@[simp]
theorem map_id {G : Type u} (n : ℕ) (x : DerivedWordArgs G n) :
    map id n x = x := by
  induction n with
  | zero =>
      obtain ⟨x⟩ := x
      rw [map_leaf, id_eq]
  | succ n ih =>
      obtain ⟨x, y⟩ := x
      rw [map_node, ih, ih]

/-- Successive maps of derived-word arguments compose pointwise. -/
theorem map_comp {G : Type u} {H : Type v} {K : Type*} (g : H → K) (f : G → H)
    (n : ℕ) (x : DerivedWordArgs G n) :
    map (g ∘ f) n x = map g n (map f n x) := by
  induction n with
  | zero =>
      obtain ⟨x⟩ := x
      rw [map_leaf, map_leaf, map_leaf, Function.comp_apply]
  | succ n ih =>
      obtain ⟨x, y⟩ := x
      rw [map_node, map_node, map_node, ih, ih]

end DerivedWordArgs

/-- Evaluate a depth-`n` argument tree by balanced commutators: a leaf evaluates to its element,
and a node to the commutator of the values of its two subtrees. Its values generate
`derivedSeries G n` (`derivedSeries_eq_closure_range_derivedWord`). -/
def derivedWord (G : Type u) [Group G] :
    (n : ℕ) → DerivedWordArgs G n → G
  | 0, .leaf x => x
  | _ + 1, .node x y => ⁅derivedWord G _ x, derivedWord G _ y⁆

@[simp]
theorem derivedWord_leaf (G : Type u) [Group G] (x : G) :
    derivedWord G 0 (.leaf x) = x :=
  (rfl)

@[simp]
theorem derivedWord_node (G : Type u) [Group G] (n : ℕ)
    (x y : DerivedWordArgs G n) :
    derivedWord G (n + 1) (.node x y) = ⁅derivedWord G n x, derivedWord G n y⁆ :=
  (rfl)

/-- Derived words commute with group homomorphisms. -/
@[simp]
theorem map_derivedWord {G : Type u} {H : Type v} {F : Type*} [Group G] [Group H]
    [FunLike F G H] [MonoidHomClass F G H] (f : F) (n : ℕ) (x : DerivedWordArgs G n) :
    f (derivedWord G n x) = derivedWord H n (DerivedWordArgs.map f n x) := by
  induction n with
  | zero =>
      obtain ⟨x⟩ := x
      rfl
  | succ n ih =>
      obtain ⟨x, y⟩ := x
      rw [DerivedWordArgs.map_node, derivedWord_node, derivedWord_node,
        map_commutatorElement, ih, ih]

/-- Conjugating a derived-word value amounts to conjugating each of its arguments. -/
private theorem conj_derivedWord (G : Type u) [Group G] (g : G) (n : ℕ)
    (x : DerivedWordArgs G n) :
    g * derivedWord G n x * g⁻¹ =
      derivedWord G n (DerivedWordArgs.map (MulAut.conj g) n x) := by
  simpa only [MulAut.conj_apply] using map_derivedWord (MulAut.conj g) n x

/-- The values of the `n`th derived word generate the `n`th derived subgroup. -/
theorem derivedSeries_eq_closure_range_derivedWord (G : Type u) [Group G] (n : ℕ) :
    derivedSeries G n = Subgroup.closure (Set.range (derivedWord G n)) := by
  induction n with
  | zero =>
      rw [derivedSeries_zero]
      apply le_antisymm
      · intro x _
        exact Subgroup.subset_closure ⟨.leaf x, rfl⟩
      · exact le_top
  | succ n ih =>
      rw [derivedSeries_succ, ih]
      apply le_antisymm
      · let N := Subgroup.closure (Set.range (derivedWord G (n + 1)))
        have hnorm : Subgroup.closure (Set.range (derivedWord G n)) ≤
            Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer_closure_iff.mpr <| by
          rintro g _ _ ⟨x, rfl⟩
          rw [conj_derivedWord]
          exact Subgroup.subset_closure ⟨_, rfl⟩
        apply commutator_closure_closure_le
        · exact hnorm
        · exact hnorm
        · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
          exact Subgroup.subset_closure ⟨.node x y, rfl⟩
      · rw [Subgroup.closure_le]
        rintro _ ⟨z, rfl⟩
        cases z with
        | node x y =>
            exact Subgroup.commutator_mem_commutator
              (Subgroup.subset_closure ⟨x, rfl⟩)
              (Subgroup.subset_closure ⟨y, rfl⟩)

/-- Every value of the `n`th derived word belongs to the `n`th derived subgroup. -/
theorem derivedWord_mem_derivedSeries (G : Type u) [Group G] (n : ℕ)
    (x : DerivedWordArgs G n) :
    derivedWord G n x ∈ derivedSeries G n := by
  rw [derivedSeries_eq_closure_range_derivedWord]
  exact Subgroup.subset_closure ⟨x, rfl⟩

/-- The `n`th derived subgroup is trivial exactly when the `n`th derived word is identically
one. -/
theorem derivedSeries_eq_bot_iff_derivedWord_eq_one (G : Type u) [Group G] (n : ℕ) :
    derivedSeries G n = ⊥ ↔ ∀ x : DerivedWordArgs G n, derivedWord G n x = 1 := by
  constructor
  · intro hn x
    exact Subgroup.mem_bot.mp (hn ▸ derivedWord_mem_derivedSeries G n x)
  · intro hn
    rw [derivedSeries_eq_closure_range_derivedWord, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    exact hn x

/-- A group is solvable exactly when some derived word is identically one. -/
theorem isSolvable_iff_exists_derivedWord_eq_one (G : Type u) [Group G] :
    Group.IsSolvable G ↔ ∃ n : ℕ, ∀ x : DerivedWordArgs G n, derivedWord G n x = 1 := by
  rw [Group.isSolvable_def]
  simp only [derivedSeries_eq_bot_iff_derivedWord_eq_one]

end TauCeti
