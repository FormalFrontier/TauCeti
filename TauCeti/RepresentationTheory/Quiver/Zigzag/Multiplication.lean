/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basis

/-!
# The multiplication table of a zigzag algebra

The zigzag relation quotient `TauCeti.nonisolatedZigzagQuotient` of a simple graph `G` is spanned by
the vertex idempotents `e_i`, the oriented edges `a_d` of the darts of `G`, and the volume classes
`x_i`; `TauCeti.zigzagBasis` shows these are a basis when no vertex is isolated. This file computes
every product of two of them, which is what makes the algebra explicit.

The table is short. The idempotents are orthogonal and act as the local units they are; an arrow is
absorbed by the idempotent at its head on the left and by the one at its tail on the right; a volume
class is absorbed by the idempotent at its base on either side. Two arrows multiply to a volume
class exactly when the later factor is the reverse dart of the earlier one, since a length-two path
survives the relations only if it returns to its source. Everything else vanishes: a product landing
in path length at least three is killed by the long generators, and a product of two paths that do
not meet is already zero in the path algebra.

In Tau Ceti's *later-factor-first* convention the product `a_d * a_e` traverses `e` first, so it is
nonzero exactly when `e = d.symm`, and then it is the volume class at `d.snd`, the vertex where the
composite begins and ends.

All the statements are unconditional: at an isolated vertex the volume class is the junk value `0`,
and each identity below degenerates to a true statement about `0` there.

## Main results

* `TauCeti.zigzagMk_ofArrow_mul_ofArrow_symm` and `TauCeti.zigzagMk_ofArrow_mul_ofArrow_of_ne`: two
  arrows multiply to a volume class when the second is the reverse of the first, and to zero
  otherwise.
* `TauCeti.zigzagMk_ofArrow_mul`: left multiplication by an arrow reads off two coordinates in the
  vertex-arrow-volume basis.
* `TauCeti.zigzagMk_vertexIdempotent_mul_zigzagVolume` and its three companions: the idempotent at
  the base of a volume class is a two-sided unit for it, and the other idempotents kill it.
* `TauCeti.zigzagMk_ofArrow_mul_zigzagVolume`, `TauCeti.zigzagVolume_mul_zigzagMk_ofArrow` and
  `TauCeti.zigzagVolume_mul_zigzagVolume`: every product reaching path length three vanishes.

## References

This is the multiplication table asked for by the first clause of Layer 2 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*,
Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- The volume class of a vertex with no neighbour is zero: it carries no backtrack. This is the
form of `TauCeti.zigzagVolume_eq_zero_of_isIsolated` that the case splits below produce. -/
private theorem zigzagVolume_eq_zero_of_not_exists_adj {i : V} (h : ¬∃ j, G.Adj i j) :
    zigzagVolume k G i = 0 :=
  zigzagVolume_eq_zero_of_isIsolated k G fun w hw => h ⟨w, hw⟩

/-! ### Products of vertex idempotents -/

/-- A vertex idempotent is idempotent in the zigzag quotient. -/
@[simp]
theorem zigzagMk_vertexIdempotent_mul_self (i : V) :
    zigzagMk k G (vertexIdempotent k (vertex G i)) * zigzagMk k G (vertexIdempotent k (vertex G i))
      = zigzagMk k G (vertexIdempotent k (vertex G i)) := by
  rw [← map_mul, vertexIdempotent_mul_self]

/-- Distinct vertex idempotents are orthogonal in the zigzag quotient. -/
@[simp]
theorem zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne {i j : V} (h : i ≠ j) :
    zigzagMk k G (vertexIdempotent k (vertex G i)) * zigzagMk k G (vertexIdempotent k (vertex G j))
      = 0 := by
  rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne ((vertex_injective G).ne h),
    map_zero]

/-! ### Products of a vertex idempotent and an arrow -/

/-- The vertex idempotent at the head of a dart is a left unit for its arrow. -/
theorem zigzagMk_vertexIdempotent_mul_ofArrow (d : G.Dart) :
    zigzagMk k G (vertexIdempotent k (vertex G d.snd)) * zigzagMk k G (ofArrow (arrow G d.adj))
      = zigzagMk k G (ofArrow (arrow G d.adj)) := by
  rw [← map_mul, vertexIdempotent_mul_ofArrow]

/-- A vertex idempotent away from the head of a dart kills its arrow on the left. -/
theorem zigzagMk_vertexIdempotent_mul_ofArrow_of_ne {v : V} (d : G.Dart) (h : v ≠ d.snd) :
    zigzagMk k G (vertexIdempotent k (vertex G v)) * zigzagMk k G (ofArrow (arrow G d.adj))
      = 0 := by
  rw [← map_mul, vertexIdempotent_mul_ofArrow_of_ne _ _ d.adj h, map_zero]

/-- The vertex idempotent at the tail of a dart is a right unit for its arrow. -/
theorem zigzagMk_ofArrow_mul_vertexIdempotent (d : G.Dart) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagMk k G (vertexIdempotent k (vertex G d.fst))
      = zigzagMk k G (ofArrow (arrow G d.adj)) := by
  rw [← map_mul, ofArrow_mul_vertexIdempotent]

/-- A vertex idempotent away from the tail of a dart kills its arrow on the right. -/
theorem zigzagMk_ofArrow_mul_vertexIdempotent_of_ne {v : V} (d : G.Dart) (h : v ≠ d.fst) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagMk k G (vertexIdempotent k (vertex G v))
      = 0 := by
  rw [← map_mul, ofArrow_mul_vertexIdempotent_of_ne _ _ d.adj h, map_zero]

/-! ### Products of a vertex idempotent and a volume class -/

/-- The vertex idempotent at the base of a volume class is a left unit for it. -/
@[simp]
theorem zigzagMk_vertexIdempotent_mul_zigzagVolume (i : V) :
    zigzagMk k G (vertexIdempotent k (vertex G i)) * zigzagVolume k G i = zigzagVolume k G i := by
  rcases em (∃ j, G.Adj i j) with ⟨j, h⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G h, ← map_mul, vertexIdempotent_mul_backtrackElem]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, mul_zero]

/-- A vertex idempotent away from the base of a volume class kills it on the left. -/
@[simp]
theorem zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne {v i : V} (h : v ≠ i) :
    zigzagMk k G (vertexIdempotent k (vertex G v)) * zigzagVolume k G i = 0 := by
  rcases em (∃ j, G.Adj i j) with ⟨j, hj⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj, ← map_mul,
      vertexIdempotent_mul_backtrackElem_of_ne _ _ hj h, map_zero]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, mul_zero]

/-- The vertex idempotent at the base of a volume class is a right unit for it. -/
@[simp]
theorem zigzagVolume_mul_zigzagMk_vertexIdempotent (i : V) :
    zigzagVolume k G i * zigzagMk k G (vertexIdempotent k (vertex G i)) = zigzagVolume k G i := by
  rcases em (∃ j, G.Adj i j) with ⟨j, h⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G h, ← map_mul, backtrackElem_mul_vertexIdempotent]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, zero_mul]

/-- A vertex idempotent away from the base of a volume class kills it on the right. -/
@[simp]
theorem zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne {v i : V} (h : v ≠ i) :
    zigzagVolume k G i * zigzagMk k G (vertexIdempotent k (vertex G v)) = 0 := by
  rcases em (∃ j, G.Adj i j) with ⟨j, hj⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj, ← map_mul,
      backtrackElem_mul_vertexIdempotent_of_ne _ _ hj h, map_zero]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, zero_mul]

/-! ### Products of two arrows -/

/-- **Traversing a dart and returning is its volume class.** In the later-factor-first convention
the reverse dart is traversed first, so the composite is the backtrack based at the head of `d`. -/
theorem zigzagMk_ofArrow_mul_ofArrow_symm (d : G.Dart) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagMk k G (ofArrow (arrow G d.symm.adj))
      = zigzagVolume k G d.snd := by
  have key : (ofArrow (arrow G d.adj) : pathAlgebra k (DoubledQuiver G))
      * ofArrow (arrow G d.symm.adj) = backtrackElem G k d.symm.adj :=
    ofArrow_symm_mul_ofArrow G k d.symm.adj
  rw [← map_mul, key, zigzagMk_backtrackElem_eq_zigzagVolume]
  -- the backtrack is based at the tail of the reverse dart, which is the head of `d`
  simp

/-- **Two arrows that are not reverse to one another multiply to zero.** Either they do not meet, in
which case the product already vanishes in the path algebra, or they meet and the composite is a
length-two path with distinct endpoints, which the zigzag relations kill. -/
theorem zigzagMk_ofArrow_mul_ofArrow_of_ne {d e : G.Dart} (h : e ≠ d.symm) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagMk k G (ofArrow (arrow G e.adj)) = 0 := by
  obtain ⟨⟨i, j⟩, hd⟩ := d
  obtain ⟨⟨a, b⟩, he⟩ := e
  rcases eq_or_ne b i with rfl | hbi
  · have hne : a ≠ j := fun hab => h (SimpleGraph.Dart.ext _ _ (by simp [hab]))
    rw [← map_mul]
    exact (zigzagMk_eq_zero_iff k G).2 (quadraticZigzagIdeal_le_zigzagIdeal k G
      (ofArrow_mul_ofArrow_mem_quadraticZigzagIdeal k G he hd hne))
  · rw [← map_mul, ofArrow_mul_ofArrow_of_ne G k he hd (Ne.symm hbi), map_zero]

/-! ### Products reaching path length three -/

/-- A product of two path classes vanishes when their total path length is at least three. -/
theorem zigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le
    (x y : Quiver.TotalPath (DoubledQuiver G))
    (h : 3 ≤ x.2.2.length + y.2.2.length) :
    zigzagMk k G (ofPath x * ofPath y) = 0 := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  rcases eq_or_ne d a with rfl | hda
  · rw [ofPath_mul_ofPath_of_comp]
    exact zigzagMk_ofPath_eq_zero_of_three_le k G _
      (by simpa only [_root_.Quiver.Path.length_comp, Nat.add_comm] using h)
  · rw [ofPath_mul_ofPath_of_not_composable hda, map_zero]

/-- An arrow times a volume class vanishes: the composite has path length three. -/
theorem zigzagMk_ofArrow_mul_zigzagVolume (d : G.Dart) (i : V) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagVolume k G i = 0 := by
  rcases em (∃ j, G.Adj i j) with ⟨j, hj⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj, ← map_mul, backtrackElem_eq_ofPath,
      ofArrow_eq_ofPath_arrowPath]
    exact zigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G _ _
      (by simp [length_backtrackPath, length_arrowPath])
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, mul_zero]

/-- A volume class times an arrow vanishes: the composite has path length three. -/
theorem zigzagVolume_mul_zigzagMk_ofArrow (i : V) (d : G.Dart) :
    zigzagVolume k G i * zigzagMk k G (ofArrow (arrow G d.adj)) = 0 := by
  rcases em (∃ j, G.Adj i j) with ⟨j, hj⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj, ← map_mul, backtrackElem_eq_ofPath,
      ofArrow_eq_ofPath_arrowPath]
    exact zigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G _ _
      (by simp [length_backtrackPath, length_arrowPath])
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, zero_mul]

/-- Two volume classes multiply to zero: they either do not meet or compose to path length four. -/
@[simp]
theorem zigzagVolume_mul_zigzagVolume (i j : V) :
    zigzagVolume k G i * zigzagVolume k G j = 0 := by
  rcases em (∃ l, G.Adj i l) with ⟨l, hl⟩ | hn
  · rcases em (∃ m, G.Adj j m) with ⟨m, hm⟩ | hn'
    · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hl,
        zigzagVolume_eq_zigzagMk_backtrackElem k G hm, ← map_mul, backtrackElem_eq_ofPath,
        backtrackElem_eq_ofPath]
      exact zigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G _ _
        (by simp [length_backtrackPath])
    · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn', mul_zero]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, zero_mul]

/-! ### Left multiplication by an arrow -/

section

variable {k G}

/-- **Left multiplication by an arrow reads off two coordinates.**  Multiplying by the arrow of a
dart `d` keeps only the idempotent at the tail of `d`, which returns the arrow itself, and the
reverse arrow, which returns the volume class at the head of `d`. -/
theorem zigzagMk_ofArrow_mul (hns : ∀ i : V, ∃ j, G.Adj i j) (d : G.Dart)
    (x : nonisolatedZigzagQuotient k G) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * x =
      (zigzagBasis k G hns).coord (.inl d.fst) x • zigzagBasis k G hns (.inr (.inl d)) +
        (zigzagBasis k G hns).coord (.inr (.inl d.symm)) x •
          zigzagBasis k G hns (.inr (.inr d.snd)) := by
  classical
  have key : LinearMap.mulLeft k (zigzagMk k G (ofArrow (arrow G d.adj))) =
      LinearMap.smulRight ((zigzagBasis k G hns).coord (.inl d.fst))
          (zigzagBasis k G hns (.inr (.inl d))) +
        LinearMap.smulRight ((zigzagBasis k G hns).coord (.inr (.inl d.symm)))
          (zigzagBasis k G hns (.inr (.inr d.snd))) := by
    refine (zigzagBasis k G hns).ext fun b => ?_
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.mulLeft_apply,
      zigzagBasis_coord_apply]
    rcases b with j | e | j
    · rcases eq_or_ne j d.fst with rfl | hj
      · rw [ite_eq_left rfl, ite_eq_right (by simp)]
        simp only [zigzagBasis_apply, zigzagBasisFun_inl, zigzagBasisFun_inr_inl,
          zigzagBasisFun_inr_inr, one_smul, zero_smul, add_zero]
        exact zigzagMk_ofArrow_mul_vertexIdempotent k G d
      · rw [ite_eq_right (by simpa using hj), ite_eq_right (by simp)]
        simp only [zigzagBasis_apply, zigzagBasisFun_inl, zigzagBasisFun_inr_inl,
          zigzagBasisFun_inr_inr, zero_smul, add_zero]
        exact zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G d hj
    · rcases eq_or_ne e d.symm with rfl | he
      · rw [ite_eq_right (by simp), ite_eq_left rfl]
        simp only [zigzagBasis_apply, zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr,
          one_smul, zero_smul, zero_add]
        exact zigzagMk_ofArrow_mul_ofArrow_symm k G d
      · rw [ite_eq_right (by simp), ite_eq_right (by simpa using he)]
        simp only [zigzagBasis_apply, zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr,
          zero_smul, add_zero]
        exact zigzagMk_ofArrow_mul_ofArrow_of_ne k G he
    · rw [ite_eq_right (by simp), ite_eq_right (by simp)]
      simp only [zigzagBasis_apply, zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr,
        zero_smul, add_zero]
      exact zigzagMk_ofArrow_mul_zigzagVolume k G d j
  simpa only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.mulLeft_apply]
    using congrArg (fun f => f x) key

end

end TauCeti
