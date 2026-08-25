/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Fintype.BigOperators
public import TauCeti.LowDimTopology.Plumbing.Characteristic
public import TauCeti.LowDimTopology.Plumbing.NegativeDefinite
public import TauCeti.LowDimTopology.Plumbing.Weight.Sublevel

/-!
# Blowing up a plumbing graph along an edge

This file adds the second of Neumann's plumbing moves: blowing up a plumbing graph along an edge.
Given a plumbing graph `P` on vertex type `V` and two adjacent vertices `u` and `v` with edge
witness `h : P.toSimpleGraph.Adj u v`, the edge blow-up `P.blowUpEdge u v h` is the plumbing
graph on `Option V` obtained by adjoining a new exceptional vertex `none` with framing `-1`,
joining `none` to both `some u` and `some v`, removing the direct edge between `some u` and
`some v`, and decreasing the framings of both `some u` and `some v` by one.

Geometrically this corresponds to blowing up a point of intersection of the two spheres `u` and `v`
inside the plumbed four-manifold. The smooth boundary three-manifold is unchanged; the exceptional
divisor in the four-manifold is a `-1`-sphere intersecting the proper transforms of `u` and `v`
transversely at one point each, so the new vertex `none` has framing `-1` and degree two. In
Neumann's calculus, the reverse operation is blowing down a `-1`-framed vertex of degree two.

The core of the file is the lattice-level and weight-level content:

1. **The total-transform lattice identification:**
   The linear equivalence
   `blowUpEdgeEquiv u v : ((V → ℤ) × ℤ) ≃ₗ[ℤ] (Option V → ℤ)`
   sends `(x, s)` to `a ↦ a.elim (x u + x v + s) x`. On basis vectors, the old basis spheres `e_u`
   and `e_v` map to their total transforms `e_u + e_none` and `e_v + e_none`, every other basis
   sphere `e_w` maps to `e_w`, and `(0, 1)` maps to the exceptional class `e_none`.

2. **Orthogonal splitting of the intersection form:**
   Under `blowUpEdgeEquiv`, the blown-up intersection form splits as the orthogonal direct sum of
   the original intersection form on `V` with the rank-one form `⟨-1⟩` on the exceptional class:
   `⟨(x, s), (y, t)⟩ = ⟨x, y⟩ - s * t`.
   Consequently, the edge blow-up is negative definite if and only if `P` is negative definite.

3. **Dual identification of covectors and characteristic covectors:**
   The dual equivalence `blowUpEdgeCovectorEquiv u v : ((V → ℤ) × ℤ) ≃ₗ[ℤ] (Option V → ℤ)` pairs
   against total transforms via `⟨k', φ(x, s)⟩ = ⟨k, x⟩ + ε * s`. It is characteristic for the
   blow-up exactly when `k` is characteristic for `P` and `ε` is odd (`blowUpEdgeCharacteristic`).
   The canonical characteristic covector of the edge blow-up is the canonical one of `P` carrying
   `-1` on the exceptional class.

4. **Weight splitting and infimum invariance:**
   Under `blowUpEdgeCharacteristic`, the characteristic weight satisfies
   `2 χ_{k'}(φ(x, s)) = 2 χ_k(x) + s * (s - ε)`.
   For a unit exceptional value `δ ∈ ℤˣ` (such as `δ = -1` for the canonical covector), the term
   `s * (s - δ)` is nonnegative for all integers `s` and vanishes precisely at `s ∈ {0, δ}`.
   Consequently, the infimum of the characteristic weight (and for negative-definite plumbings, the
   minimal characteristic weight that serves as numerical input to the `d`-invariant) is invariant
   under the edge blow-up move.

## Main definitions

* `TauCeti.PlumbingGraph.blowUpEdge`: the blow-up of a plumbing graph along an edge.
* `TauCeti.PlumbingGraph.blowUpEdgeEquiv`: the total-transform identification of the blown-up
  lattice with `(V → ℤ) × ℤ`.
* `TauCeti.PlumbingGraph.blowUpEdgeCovectorEquiv`: the total-transform identification of covectors,
  dual to `blowUpEdgeEquiv`.
* `TauCeti.PlumbingGraph.blowUpEdgeCharacteristic`: the characteristic covector of the edge blow-up
  determined by a characteristic covector of `P` and an odd value on the exceptional class.

## Main results

* `TauCeti.PlumbingGraph.blowUpEdge_weight_none`: the new vertex has framing `-1`.
* `TauCeti.PlumbingGraph.blowUpEdge_degree_none`: the new vertex has degree two, matching (together
  with framing `-1`) the local configuration of Neumann's degree-two blow-down move.
* `TauCeti.PlumbingGraph.intersectionForm_blowUpEdgeEquiv`: the blown-up intersection form is the
  orthogonal direct sum of the original form with `⟨-1⟩`.
* `TauCeti.PlumbingGraph.sum_blowUpEdgeCovectorEquiv_mul_blowUpEdgeEquiv`: duality of the two
  total-transform identifications.
* `TauCeti.PlumbingGraph.isCharacteristicVector_blowUpEdgeCovectorEquiv_iff`: the characteristic
  covectors of the edge blow-up are parametrized by pairs of a characteristic covector of `P`
  and an odd exceptional value.
* `TauCeti.PlumbingGraph.isNegativeDefinite_blowUpEdge_iff`: the edge blow-up preserves and reflects
  negative-definiteness.
* `TauCeti.PlumbingGraph.two_mul_characteristicWeight_blowUpEdgeCharacteristic`: the characteristic
  weight splits into the old weight plus `s * (s - ε) / 2`.
* `TauCeti.PlumbingGraph.sInfCharacteristicWeight_blowUpEdgeCharacteristic` and
  `TauCeti.PlumbingGraph.sInfCharacteristicWeight_canonicalCharacteristic_blowUpEdge`: the infimum
  of the characteristic weight is invariant under the edge blow-up move.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
whose programme is "Plumbing trees/graphs and their lattices; Némethi's lattice (co)homology …;
invariance under **Neumann moves**; … `d`-invariant analogues". The plumbing calculus is
W. Neumann, *A calculus for plumbing applied to the topology of complex surface singularities and
degenerating complex curves*, Trans. Amer. Math. Soc. **268** (1981), 299--344; the weight
conventions and the behaviour of `χ_k` under blowing up follow Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Sections 2--3, after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

open Matrix

namespace TauCeti

/-! ### Arithmetic of the exceptional multiplicity -/

/-- Two consecutive integers have nonnegative product: no integer lies strictly between `t - 1`
and `t`. -/
private theorem zero_le_mul_sub_one (t : ℤ) : 0 ≤ t * (t - 1) := by
  rcases le_or_gt t 0 with ht | ht
  · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -t) (by omega : (0 : ℤ) ≤ 1 - t)]
  · exact mul_nonneg (by omega) (by omega)

/-- The exceptional term of a unit exceptional value is nonnegative: rescaling by the unit turns
`s * (s - δ)` into a product of consecutive integers. -/
private theorem zero_le_mul_sub_units (δ : ℤˣ) (s : ℤ) : 0 ≤ s * (s - (δ : ℤ)) := by
  have hδ : (δ : ℤ) * (δ : ℤ) = 1 := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num
  have hEq : ((δ : ℤ) * s) * ((δ : ℤ) * s - 1) = s * (s - (δ : ℤ)) := by
    linear_combination (s * s) * hδ
  rw [← hEq]
  exact zero_le_mul_sub_one _

namespace PlumbingGraph

variable {V : Type*}

/-! ### The total-transform lattice identification -/

/-- The total-transform identification of the edge-blown-up plumbing lattice.

A pair `(x, s)` consisting of a lattice point `x` of the original plumbing and a multiple `s` of
the exceptional class is sent to the lattice point of the edge blow-up whose coordinate at the new
vertex `none` is `x u + x v + s` and whose coordinate at an old vertex `some w` is `x w`. On basis
vectors this is `e_u ↦ e_u + e_none`, `e_v ↦ e_v + e_none`, `e_w ↦ e_w` for `w ∉ {u, v}`, and
`(0, 1) ↦ e_none`.

The map depends only on the endpoints `u` and `v` of the blown-up edge. -/
def blowUpEdgeEquiv (u v : V) : ((V → ℤ) × ℤ) ≃ₗ[ℤ] (Option V → ℤ) where
  toFun p a := a.elim (p.1 u + p.1 v + p.2) p.1
  map_add' p q := by
    funext a
    cases a with
    | none =>
        simp only [Option.elim_none, Prod.fst_add, Prod.snd_add, Pi.add_apply]
        ring
    | some w => rfl
  map_smul' c p := by
    funext a
    cases a with
    | none =>
        simp only [Option.elim_none, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring
    | some w => rfl
  invFun y := (fun w => y (some w), y none - y (some u) - y (some v))
  left_inv p := by
    rw [Prod.ext_iff]
    refine ⟨funext fun w => rfl, ?_⟩
    simp only [Option.elim_none, Option.elim_some]
    ring
  right_inv y := by
    funext a
    cases a with
    | none =>
        simp only [Option.elim_none]
        ring
    | some w => rfl

/-- The coordinate of a lifted lattice point at the new vertex. -/
@[simp]
theorem blowUpEdgeEquiv_apply_none (u v : V) (x : V → ℤ) (s : ℤ) :
    blowUpEdgeEquiv u v (x, s) none = x u + x v + s :=
  (rfl)

/-- The coordinate of a lifted lattice point at an old vertex. -/
@[simp]
theorem blowUpEdgeEquiv_apply_some (u v : V) (x : V → ℤ) (s : ℤ) (w : V) :
    blowUpEdgeEquiv u v (x, s) (some w) = x w :=
  (rfl)

/-- The inverse identification reads off the old coordinates and the exceptional multiplicity. -/
@[simp]
theorem blowUpEdgeEquiv_symm_apply (u v : V) (y : Option V → ℤ) :
    (blowUpEdgeEquiv u v).symm y =
      (fun w => y (some w), y none - y (some u) - y (some v)) :=
  (rfl)

/-- The pair `(0, 1)` is the exceptional class, the basis vector at the new vertex. -/
theorem blowUpEdgeEquiv_zero_one [DecidableEq V] (u v : V) :
    blowUpEdgeEquiv u v (0, 1) = Pi.single (none : Option V) (1 : ℤ) := by
  funext a
  cases a with
  | none => simp
  | some w => simp

/-! ### The edge blow-up construction -/

/-- The adjacency relation of the edge blow-up: the new vertex `none` is joined to `some u` and
`some v`, the direct edge between `some u` and `some v` is removed, and all other adjacencies are
preserved. -/
private def BlowUpEdgeAdj (P : PlumbingGraph V) (u v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some w => w = u ∨ w = v
  | some w, none => w = u ∨ w = v
  | some w, some w' => P.toSimpleGraph.Adj w w' ∧ ¬((w = u ∧ w' = v) ∨ (w = v ∧ w' = u))

private instance decidableBlowUpEdgeAdj [DecidableEq V] (P : PlumbingGraph V) (u v : V) :
    DecidableRel (P.BlowUpEdgeAdj u v)
  | none, none => inferInstanceAs (Decidable False)
  | none, some w => inferInstanceAs (Decidable (w = u ∨ w = v))
  | some w, none => inferInstanceAs (Decidable (w = u ∨ w = v))
  | some w, some w' =>
      inferInstanceAs (Decidable (P.toSimpleGraph.Adj w w' ∧
        ¬((w = u ∧ w' = v) ∨ (w = v ∧ w' = u))))

/-- The edge blow-up adjacency relation is symmetric. -/
private theorem blowUpEdgeAdj_symm (P : PlumbingGraph V) (u v : V) :
    Std.Symm (P.BlowUpEdgeAdj u v) :=
  ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact ⟨(h.1 : P.toSimpleGraph.Adj a b).symm, fun hbad => h.2 (by tauto)⟩⟩

/-- The edge blow-up adjacency relation is irreflexive. -/
private theorem blowUpEdgeAdj_irrefl (P : PlumbingGraph V) (u v : V) :
    Std.Irrefl (P.BlowUpEdgeAdj u v) :=
  ⟨by
    rintro (_ | a) h
    · exact h
    · exact P.toSimpleGraph.irrefl (h.1 : P.toSimpleGraph.Adj a a)⟩

/-- The blow-up of a plumbing graph along an edge `_h : P.toSimpleGraph.Adj u v`: adjoin a new
exceptional vertex `none` with framing `-1`, connect it to `some u` and `some v`, remove the direct
edge between `some u` and `some v`, and decrease the framings of `some u` and `some v` by one. -/
def blowUpEdge [DecidableEq V] (P : PlumbingGraph V) (u v : V) (_h : P.toSimpleGraph.Adj u v) :
    PlumbingGraph (Option V) where
  toSimpleGraph :=
    { Adj := P.BlowUpEdgeAdj u v
      symm := P.blowUpEdgeAdj_symm u v
      loopless := P.blowUpEdgeAdj_irrefl u v }
  decidableAdj := P.decidableBlowUpEdgeAdj u v
  weight a := a.elim (-1) fun w => if w = u ∨ w = v then P.weight w - 1 else P.weight w

variable [DecidableEq V] (P : PlumbingGraph V)

/-- The new vertex is joined exactly to `some u` and `some v`. -/
@[simp]
theorem blowUpEdge_adj_none_some (u v : V) (_h : P.toSimpleGraph.Adj u v) (w : V) :
    (P.blowUpEdge u v _h).toSimpleGraph.Adj none (some w) ↔ w = u ∨ w = v :=
  Iff.rfl

/-- The new vertex is joined exactly to `some u` and `some v`. -/
@[simp]
theorem blowUpEdge_adj_some_none (u v : V) (_h : P.toSimpleGraph.Adj u v) (w : V) :
    (P.blowUpEdge u v _h).toSimpleGraph.Adj (some w) none ↔ w = u ∨ w = v :=
  Iff.rfl

/-- Adjacency between old vertices in the edge blow-up: the edge between `u` and `v` is removed,
and all other adjacencies are retained. -/
@[simp]
theorem blowUpEdge_adj_some_some (u v : V) (_h : P.toSimpleGraph.Adj u v) (w w' : V) :
    (P.blowUpEdge u v _h).toSimpleGraph.Adj (some w) (some w') ↔
      P.toSimpleGraph.Adj w w' ∧ ¬((w = u ∧ w' = v) ∨ (w = v ∧ w' = u)) :=
  Iff.rfl

/-- The direct edge between `some u` and `some v` is removed by the edge blow-up. -/
theorem blowUpEdge_not_adj_some_some_of_edge (u v : V) (_h : P.toSimpleGraph.Adj u v) :
    ¬ (P.blowUpEdge u v _h).toSimpleGraph.Adj (some u) (some v) := by
  simp

/-- The new vertex is `-1`-framed. -/
@[simp]
theorem blowUpEdge_weight_none (u v : V) (_h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v _h).weight none = -1 :=
  (rfl)

/-- The framings of the old vertices in the edge blow-up, with `u` and `v` dropped by one. -/
@[simp]
theorem blowUpEdge_weight_some (u v : V) (_h : P.toSimpleGraph.Adj u v) (w : V) :
    (P.blowUpEdge u v _h).weight (some w) =
      if w = u ∨ w = v then P.weight w - 1 else P.weight w :=
  (rfl)

/-- Blowing up along the edge drops the framing of `u` by one. -/
theorem blowUpEdge_weight_some_u (u v : V) (_h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v _h).weight (some u) = P.weight u - 1 := by
  simp

/-- Blowing up along the edge drops the framing of `v` by one. -/
theorem blowUpEdge_weight_some_v (u v : V) (_h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v _h).weight (some v) = P.weight v - 1 := by
  simp

/-- Blowing up along the edge leaves the framings of other vertices alone. -/
theorem blowUpEdge_weight_some_of_ne (u v : V) (_h : P.toSimpleGraph.Adj u v)
    {w : V} (hu : w ≠ u) (hv : w ≠ v) :
    (P.blowUpEdge u v _h).weight (some w) = P.weight w := by
  simp [hu, hv]

/-- The new vertex has exactly two neighbours, `some u` and `some v`. -/
theorem blowUpEdge_neighborSet_none (u v : V) (_h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v _h).toSimpleGraph.neighborSet none = {some u, some v} := by
  ext a
  cases a with
  | none => simp
  | some w => simp

/-- The new vertex has degree two. Together with framing `-1`, this is the local configuration
removed by Neumann's degree-two blow-down move. -/
theorem blowUpEdge_degree_none [Fintype V] (u v : V) (h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v h).toSimpleGraph.degree none = 2 := by
  have hne : u ≠ v := h.ne
  have hne' : (some u : Option V) ≠ some v := by simpa using hne
  have hset : (P.blowUpEdge u v h).toSimpleGraph.neighborFinset none = {some u, some v} := by
    ext a
    cases a with
    | none => simp
    | some w => simp
  rw [SimpleGraph.degree, hset, Finset.card_pair hne']

/-- The exceptional sphere has self-intersection `-1`. -/
@[simp 1100]
theorem blowUpEdge_intersectionMatrix_none_none (u v : V) (_h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v _h).intersectionMatrix none none = -1 := by
  rw [intersectionMatrix_diag, blowUpEdge_weight_none]

/-- The exceptional sphere meets `some u` and `some v` once and other spheres not at all. -/
@[simp]
theorem blowUpEdge_intersectionMatrix_none_some (u v : V) (_h : P.toSimpleGraph.Adj u v)
    (w : V) :
    (P.blowUpEdge u v _h).intersectionMatrix none (some w) =
      if w = u ∨ w = v then 1 else 0 := by
  rw [(P.blowUpEdge u v _h).intersectionMatrix_apply_of_ne
    (by simp : (none : Option V) ≠ some w)]
  simp

/-- The exceptional sphere meets `some u` and `some v` once and other spheres not at all. -/
@[simp]
theorem blowUpEdge_intersectionMatrix_some_none (u v : V) (_h : P.toSimpleGraph.Adj u v)
    (w : V) :
    (P.blowUpEdge u v _h).intersectionMatrix (some w) none =
      if w = u ∨ w = v then 1 else 0 := by
  rw [(P.blowUpEdge u v _h).intersectionMatrix_apply_of_ne
    (by simp : (some w : Option V) ≠ none)]
  simp

/-- Between old vertices the intersection matrix changes by subtracting the rank-one correction
`[w ∈ {u, v}] * [w' ∈ {u, v}]`. -/
@[simp]
theorem blowUpEdge_intersectionMatrix_some_some (u v : V) (h : P.toSimpleGraph.Adj u v)
    (w w' : V) :
    (P.blowUpEdge u v h).intersectionMatrix (some w) (some w') =
      P.intersectionMatrix w w' -
        (if w = u ∨ w = v then (1 : ℤ) else 0) * (if w' = u ∨ w' = v then (1 : ℤ) else 0) := by
  rcases eq_or_ne w w' with rfl | hne
  · rw [intersectionMatrix_diag, intersectionMatrix_diag, blowUpEdge_weight_some]
    by_cases hcases : w = u ∨ w = v <;> simp [hcases]
  · rw [(P.blowUpEdge u v h).intersectionMatrix_apply_of_ne (by simpa using hne),
      P.intersectionMatrix_apply_of_ne hne]
    simp only [blowUpEdge_adj_some_some]
    have hprod : ((if w = u ∨ w = v then (1 : ℤ) else 0) *
        (if w' = u ∨ w' = v then (1 : ℤ) else 0)) =
        if (w = u ∧ w' = v) ∨ (w = v ∧ w' = u) then 1 else 0 := by
      by_cases h1 : (w = u ∧ w' = v) ∨ (w = v ∧ w' = u)
      · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      · have hnot : ¬((w = u ∨ w = v) ∧ (w' = u ∨ w' = v)) := by
          rintro ⟨hw, hw'⟩
          rcases hw with rfl | rfl <;> rcases hw' with rfl | rfl
          · exact hne rfl
          · exact h1 (Or.inl ⟨rfl, rfl⟩)
          · exact h1 (Or.inr ⟨rfl, rfl⟩)
          · exact hne rfl
        have hleft : (if w = u ∨ w = v then (1 : ℤ) else 0) *
            (if w' = u ∨ w' = v then (1 : ℤ) else 0) = 0 := by
          by_cases hw : w = u ∨ w = v
          · have hw' : ¬(w' = u ∨ w' = v) := fun hbad => hnot ⟨hw, hbad⟩
            simp [hw, hw']
          · simp [hw]
        simp [h1, hleft]
    rw [hprod]
    by_cases hadj : P.toSimpleGraph.Adj w w'
    · simp only [hadj, true_and, ite_true]
      by_cases hpair : (w = u ∧ w' = v) ∨ (w = v ∧ w' = u)
      · simp [hpair]
      · simp [hpair]
    · simp only [hadj, false_and, ite_false]
      have hnotpair : ¬((w = u ∧ w' = v) ∨ (w = v ∧ w' = u)) := by
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hadj h
        · exact hadj h.symm
      simp [hnotpair]

/-! ### The covectors of an edge blow-up -/

/-- The total-transform identification of the covectors of the edge blow-up.

A pair `(k, ε)` is sent to the covector taking value `ε` at `none` and `k w - [w ∈ {u, v}] ε` at
`some w`. This is dual to `blowUpEdgeEquiv`. -/
def blowUpEdgeCovectorEquiv (u v : V) : ((V → ℤ) × ℤ) ≃ₗ[ℤ] (Option V → ℤ) where
  toFun p a := a.elim p.2 fun w => p.1 w - if w = u ∨ w = v then p.2 else 0
  map_add' p q := by
    funext a
    cases a with
    | none => rfl
    | some w =>
        simp only [Option.elim_some, Prod.fst_add, Prod.snd_add, Pi.add_apply]
        split_ifs <;> ring
  map_smul' c p := by
    funext a
    cases a with
    | none => rfl
    | some w =>
        simp only [Option.elim_some, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        split_ifs <;> ring
  invFun k := (fun w => k (some w) + (if w = u ∨ w = v then k none else 0), k none)
  left_inv p := by
    rw [Prod.ext_iff]
    refine ⟨funext fun w => ?_, rfl⟩
    simp only [Option.elim_some, Option.elim_none]
    split_ifs <;> ring
  right_inv k := by
    funext a
    cases a with
    | none => rfl
    | some w =>
        simp only [Option.elim_some]
        split_ifs <;> ring

/-- The value of a lifted covector on the exceptional class. -/
@[simp]
theorem blowUpEdgeCovectorEquiv_apply_none (u v : V) (k : V → ℤ) (ε : ℤ) :
    blowUpEdgeCovectorEquiv u v (k, ε) none = ε :=
  (rfl)

/-- The value of a lifted covector at an old vertex. -/
@[simp]
theorem blowUpEdgeCovectorEquiv_apply_some (u v : V) (k : V → ℤ) (ε : ℤ) (w : V) :
    blowUpEdgeCovectorEquiv u v (k, ε) (some w) =
      k w - if w = u ∨ w = v then ε else 0 :=
  (rfl)

/-- The inverse identification reads off the value on the exceptional class and undoes the
correction at `u` and `v`. -/
@[simp]
theorem blowUpEdgeCovectorEquiv_symm_apply (u v : V) (k : Option V → ℤ) :
    (blowUpEdgeCovectorEquiv u v).symm k =
      (fun w => k (some w) + (if w = u ∨ w = v then k none else 0), k none) :=
  (rfl)

/-- The canonical characteristic covector of the edge blow-up is the canonical characteristic
covector of `P` carrying `-1` on the exceptional class. -/
@[simp]
theorem blowUpEdgeCovectorEquiv_canonicalCharacteristic (u v : V)
    (_h : P.toSimpleGraph.Adj u v) :
    blowUpEdgeCovectorEquiv u v (P.canonicalCharacteristic, -1) =
      (P.blowUpEdge u v _h).canonicalCharacteristic := by
  funext a
  cases a with
  | none => simp
  | some w =>
      simp only [blowUpEdgeCovectorEquiv_apply_some, canonicalCharacteristic_apply,
        blowUpEdge_weight_some]
      split_ifs <;> ring

/-- A lifted covector is characteristic for the edge blow-up exactly when the original covector is
characteristic for `P` and the exceptional value is odd. -/
@[simp]
theorem isCharacteristicVector_blowUpEdgeCovectorEquiv_iff (u v : V)
    (_h : P.toSimpleGraph.Adj u v) (k : V → ℤ) (ε : ℤ) :
    (P.blowUpEdge u v _h).IsCharacteristicVector (blowUpEdgeCovectorEquiv u v (k, ε)) ↔
      P.IsCharacteristicVector k ∧ Odd ε := by
  simp only [isCharacteristicVector_iff, Int.ModEq, Int.odd_iff]
  constructor
  · intro hchar
    have hnone := hchar none
    rw [blowUpEdgeCovectorEquiv_apply_none, blowUpEdge_weight_none] at hnone
    refine ⟨fun w => ?_, by omega⟩
    have hw := hchar (some w)
    rw [blowUpEdgeCovectorEquiv_apply_some, blowUpEdge_weight_some] at hw
    split_ifs at hw <;> omega
  · rintro ⟨hk, hε⟩ a
    cases a with
    | none => rw [blowUpEdgeCovectorEquiv_apply_none, blowUpEdge_weight_none]; omega
    | some w =>
        have hw := hk w
        rw [blowUpEdgeCovectorEquiv_apply_some, blowUpEdge_weight_some]
        split_ifs <;> omega

/-- Every characteristic covector of an edge blow-up is the lift of a characteristic covector of
`P` carrying an odd value on the exceptional class. -/
theorem exists_blowUpEdgeCovectorEquiv_eq (u v : V) (h : P.toSimpleGraph.Adj u v)
    (k : (P.blowUpEdge u v h).characteristicVectors) :
    ∃ (l : P.characteristicVectors) (ε : ℤ), Odd ε ∧
      blowUpEdgeCovectorEquiv u v (l.val, ε) = k.val := by
  obtain ⟨p, hp⟩ := (blowUpEdgeCovectorEquiv u v).surjective k.val
  obtain ⟨hl, hε⟩ :=
    (P.isCharacteristicVector_blowUpEdgeCovectorEquiv_iff u v h p.1 p.2).mp (hp ▸ k.property)
  exact ⟨⟨p.1, hl⟩, p.2, hε, hp⟩

/-- The characteristic covector of the edge blow-up determined by a characteristic covector `k` of
`P` and an odd value `ε` on the exceptional class. -/
def blowUpEdgeCharacteristic (u v : V) (h : P.toSimpleGraph.Adj u v)
    (k : P.characteristicVectors) (ε : ℤ) (hε : Odd ε) :
    (P.blowUpEdge u v h).characteristicVectors :=
  ⟨blowUpEdgeCovectorEquiv u v (k.val, ε),
    (P.isCharacteristicVector_blowUpEdgeCovectorEquiv_iff u v h k.val ε).mpr ⟨k.property, hε⟩⟩

/-- The underlying covector of `blowUpEdgeCharacteristic` is the lift of the underlying
covector. -/
@[simp]
theorem blowUpEdgeCharacteristic_val (u v : V) (h : P.toSimpleGraph.Adj u v)
    (k : P.characteristicVectors) (ε : ℤ) (hε : Odd ε) :
    (P.blowUpEdgeCharacteristic u v h k ε hε).val =
      blowUpEdgeCovectorEquiv u v (k.val, ε) :=
  (rfl)

/-- The canonical characteristic covector of an edge blow-up is the canonical characteristic
covector of `P` with `-1` on the exceptional class. -/
@[simp]
theorem blowUpEdgeCharacteristic_canonicalCharacteristic (u v : V)
    (h : P.toSimpleGraph.Adj u v) :
    P.blowUpEdgeCharacteristic u v h
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ (-1)
          (by norm_num) =
      ⟨(P.blowUpEdge u v h).canonicalCharacteristic,
        (P.blowUpEdge u v h).isCharacteristicVector_canonicalCharacteristic⟩ := by
  refine Subtype.ext ?_
  rw [blowUpEdgeCharacteristic_val]
  simpa using P.blowUpEdgeCovectorEquiv_canonicalCharacteristic u v h

/-! ### Lattice splitting and intersection form -/

section Lattice

variable [Fintype V]

/-- Sum of a function supported on two distinct elements `u` and `v`. -/
private theorem sum_ite_or_eq (u v : V) (hne : u ≠ v) (f : V → ℤ) :
    ∑ w : V, (if w = u ∨ w = v then f w else 0) = f u + f v := by
  have h_cases : ∀ w : V, (if w = u ∨ w = v then f w else 0) =
      (if w = u then f w else 0) + (if w = v then f w else 0) := by
    intro w
    by_cases hwu : w = u
    · subst hwu; simp [hne]
    · by_cases hwv : w = v
      · subst hwv; simp [hwu]
      · simp [hwu, hwv]
  simp_rw [h_cases, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ u f, Finset.sum_ite_eq' Finset.univ v f]
  simp

/-- The `none`-coordinate of the image of a lifted lattice point under the edge-blown-up
intersection matrix. -/
private theorem blowUpEdge_mulVec_apply_none (u v : V) (h : P.toSimpleGraph.Adj u v)
    (y : V → ℤ) (t : ℤ) :
    ((P.blowUpEdge u v h).intersectionMatrix *ᵥ blowUpEdgeEquiv u v (y, t)) none = -t := by
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_option]
  simp only [blowUpEdge_intersectionMatrix_none_none, blowUpEdge_intersectionMatrix_none_some,
    blowUpEdgeEquiv_apply_none, blowUpEdgeEquiv_apply_some, ite_mul, one_mul, zero_mul]
  rw [sum_ite_or_eq u v h.ne y]
  ring

/-- The `some`-coordinates of the image of a lifted lattice point under the edge-blown-up
intersection matrix. -/
private theorem blowUpEdge_mulVec_apply_some (u v : V) (h : P.toSimpleGraph.Adj u v)
    (y : V → ℤ) (t : ℤ) (w : V) :
    ((P.blowUpEdge u v h).intersectionMatrix *ᵥ blowUpEdgeEquiv u v (y, t)) (some w) =
      (P.intersectionMatrix *ᵥ y) w + (if w = u ∨ w = v then t else 0) := by
  have hsplit : ∀ w' : V,
      (P.intersectionMatrix w w' -
          (if w = u ∨ w = v then (1 : ℤ) else 0) * (if w' = u ∨ w' = v then (1 : ℤ) else 0)) *
            y w' =
        P.intersectionMatrix w w' * y w' -
          (if w = u ∨ w = v then (1 : ℤ) else 0) *
            ((if w' = u ∨ w' = v then (1 : ℤ) else 0) * y w') := by
    intro w'
    ring
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_option]
  simp only [blowUpEdge_intersectionMatrix_some_none, blowUpEdge_intersectionMatrix_some_some,
    blowUpEdgeEquiv_apply_none, blowUpEdgeEquiv_apply_some, hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.mulVec_apply_eq_sum]
  have hsum : ∑ w' : V, (if w' = u ∨ w' = v then (1 : ℤ) else 0) * y w' = y u + y v := by
    simp_rw [ite_mul, one_mul, zero_mul]
    exact sum_ite_or_eq u v h.ne y
  rw [hsum]
  split_ifs <;> ring

/-- **The edge blow-up splits the intersection form.** Under the total-transform identification
`blowUpEdgeEquiv`, the intersection form of the edge blow-up is the orthogonal direct sum of the
intersection form of `P` with the rank-one form `⟨-1⟩` spanned by the exceptional class. -/
theorem intersectionForm_blowUpEdgeEquiv (u v : V) (h : P.toSimpleGraph.Adj u v)
    (x y : V → ℤ) (s t : ℤ) :
    (P.blowUpEdge u v h).intersectionForm (blowUpEdgeEquiv u v (x, s))
        (blowUpEdgeEquiv u v (y, t)) =
      P.intersectionForm x y - s * t := by
  have hdotOpt : ∀ u' z : Option V → ℤ, u' ⬝ᵥ z = ∑ a, u' a * z a := fun _ _ => rfl
  have hdotV : ∀ u' z : V → ℤ, u' ⬝ᵥ z = ∑ a, u' a * z a := fun _ _ => rfl
  have hterm : ∀ w : V,
      x w * ((P.intersectionMatrix *ᵥ y) w + (if w = u ∨ w = v then t else 0)) =
        x w * (P.intersectionMatrix *ᵥ y) w + (if w = u ∨ w = v then x w * t else 0) := by
    intro w
    split_ifs <;> ring
  rw [(P.blowUpEdge u v h).intersectionForm_apply,
    ← Matrix.toBilin'_apply (P.blowUpEdge u v h).intersectionMatrix, Matrix.toBilin'_apply',
    P.intersectionForm_apply, ← Matrix.toBilin'_apply P.intersectionMatrix x y,
    Matrix.toBilin'_apply', hdotOpt, hdotV, Fintype.sum_option]
  simp only [blowUpEdgeEquiv_apply_none, blowUpEdgeEquiv_apply_some,
    P.blowUpEdge_mulVec_apply_none u v h y t, P.blowUpEdge_mulVec_apply_some u v h y t, hterm]
  rw [Finset.sum_add_distrib, sum_ite_or_eq u v h.ne fun w => x w * t]
  ring

/-- The two total-transform identifications are dual to one another: the pairing of the lifted
covector `(k, ε)` against the lifted lattice point `(x, s)` is `⟨k, x⟩ + ε * s`. -/
theorem sum_blowUpEdgeCovectorEquiv_mul_blowUpEdgeEquiv (u v : V) (hne : u ≠ v)
    (k x : V → ℤ) (ε s : ℤ) :
    ∑ a, blowUpEdgeCovectorEquiv u v (k, ε) a * blowUpEdgeEquiv u v (x, s) a =
      (∑ w, k w * x w) + ε * s := by
  rw [Fintype.sum_option]
  simp only [blowUpEdgeCovectorEquiv_apply_none, blowUpEdgeCovectorEquiv_apply_some,
    blowUpEdgeEquiv_apply_none, blowUpEdgeEquiv_apply_some, sub_mul, ite_mul, zero_mul]
  rw [Finset.sum_sub_distrib, sum_ite_or_eq u v hne fun w => ε * x w]
  ring

/-- The exceptional class has self-intersection `-1`. -/
theorem intersectionForm_blowUpEdge_single_none_self (u v : V) (h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v h).intersectionForm (Pi.single (none : Option V) (1 : ℤ))
        (Pi.single (none : Option V) (1 : ℤ)) = -1 := by
  rw [(P.blowUpEdge u v h).intersectionForm_single,
    P.blowUpEdge_intersectionMatrix_none_none u v h]

/-- The exceptional class is orthogonal to every total transform. -/
theorem intersectionForm_blowUpEdgeEquiv_single_none (u v : V) (h : P.toSimpleGraph.Adj u v)
    (x : V → ℤ) :
    (P.blowUpEdge u v h).intersectionForm (blowUpEdgeEquiv u v (x, 0))
        (Pi.single (none : Option V) (1 : ℤ)) = 0 := by
  rw [← blowUpEdgeEquiv_zero_one u v, P.intersectionForm_blowUpEdgeEquiv u v h x 0 0 1]
  simp

end Lattice

/-- **Blowing up along an edge preserves and reflects negative-definiteness.** -/
@[grind =]
theorem isNegativeDefinite_blowUpEdge_iff [Finite V] (u v : V)
    (h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v h).IsNegativeDefinite ↔ P.IsNegativeDefinite := by
  obtain ⟨_⟩ := nonempty_fintype V
  rw [isNegativeDefinite_iff_forall_intersectionForm_self_neg,
    isNegativeDefinite_iff_forall_intersectionForm_self_neg]
  constructor
  · intro hdef x hx
    have hne : blowUpEdgeEquiv u v (x, (0 : ℤ)) ≠ 0 := by
      intro hzero
      refine hx (funext fun w => ?_)
      simpa using congrFun hzero (some w)
    have hlt := hdef _ hne
    rw [P.intersectionForm_blowUpEdgeEquiv u v h x x 0 0] at hlt
    simpa using hlt
  · intro hdef y hy
    obtain ⟨⟨x, s⟩, rfl⟩ : ∃ p, blowUpEdgeEquiv u v p = y :=
      ⟨(blowUpEdgeEquiv u v).symm y, (blowUpEdgeEquiv u v).apply_symm_apply y⟩
    rw [P.intersectionForm_blowUpEdgeEquiv u v h x x s s]
    rcases eq_or_ne x 0 with rfl | hx0
    · have hs : s ≠ 0 := fun hs0 => hy (by simp [hs0])
      have h0 : P.intersectionForm 0 0 = 0 := by simp
      rw [h0]
      linarith [mul_self_pos.mpr hs]
    · linarith [hdef x hx0, mul_self_nonneg s]

/-! ### The characteristic weight function of an edge blow-up -/

section Weight

variable [Fintype V]

/-- The characteristic-weight numerator of an edge blow-up in total-transform coordinates. -/
theorem characteristicWeightNumerator_blowUpEdgeCovectorEquiv (u v : V)
    (h : P.toSimpleGraph.Adj u v) (k x : V → ℤ) (ε s : ℤ) :
    (P.blowUpEdge u v h).characteristicWeightNumerator (blowUpEdgeCovectorEquiv u v (k, ε))
        (blowUpEdgeEquiv u v (x, s)) =
      P.characteristicWeightNumerator k x + ε * s - s * s := by
  rw [characteristicWeightNumerator_def, characteristicWeightNumerator_def,
    sum_blowUpEdgeCovectorEquiv_mul_blowUpEdgeEquiv u v h.ne,
    P.intersectionForm_blowUpEdgeEquiv u v h x x s s]
  ring

/-- **The weight function of an edge blow-up splits.** In total-transform coordinates:
`2 χ_{k'}(φ(x, s)) = 2 χ_k(x) + s * (s - ε)`. -/
theorem two_mul_characteristicWeight_blowUpEdgeCharacteristic (u v : V)
    (h : P.toSimpleGraph.Adj u v) (k : P.characteristicVectors) (ε : ℤ)
    (hε : Odd ε) (x : V → ℤ) (s : ℤ) :
    2 * (P.blowUpEdge u v h).characteristicWeight
        (P.blowUpEdgeCharacteristic u v h k ε hε)
        (blowUpEdgeEquiv u v (x, s)) =
      2 * P.characteristicWeight k x + s * (s - ε) := by
  rw [two_mul_characteristicWeight, blowUpEdgeCharacteristic_val,
    P.characteristicWeightNumerator_blowUpEdgeCovectorEquiv u v h]
  linear_combination -P.two_mul_characteristicWeight k x

/-- The total transform preserves the characteristic weight: at exceptional multiplicity `0` the
weight of the edge blow-up is the weight of `P`. -/
@[simp]
theorem characteristicWeight_blowUpEdgeCharacteristic_zero (u v : V)
    (h : P.toSimpleGraph.Adj u v) (k : P.characteristicVectors) (ε : ℤ)
    (hε : Odd ε) (x : V → ℤ) :
    (P.blowUpEdge u v h).characteristicWeight
        (P.blowUpEdgeCharacteristic u v h k ε hε)
        (blowUpEdgeEquiv u v (x, 0)) = P.characteristicWeight k x := by
  have h' := P.two_mul_characteristicWeight_blowUpEdgeCharacteristic u v h k ε hε x 0
  rw [zero_mul, add_zero] at h'
  omega

/-- The edge-blown-up weight agrees with the old weight exactly at the exceptional multiplicities
`0` and `ε`. -/
@[simp]
theorem characteristicWeight_blowUpEdgeCharacteristic_eq_iff (u v : V)
    (h : P.toSimpleGraph.Adj u v) (k : P.characteristicVectors) (ε : ℤ)
    (hε : Odd ε) (x : V → ℤ) (s : ℤ) :
    (P.blowUpEdge u v h).characteristicWeight
        (P.blowUpEdgeCharacteristic u v h k ε hε)
        (blowUpEdgeEquiv u v (x, s)) = P.characteristicWeight k x ↔ s = 0 ∨ s = ε := by
  have h' := P.two_mul_characteristicWeight_blowUpEdgeCharacteristic u v h k ε hε x s
  constructor
  · intro he
    have hzero : s * (s - ε) = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hs | hs
    · exact Or.inl hs
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · rw [zero_mul, add_zero] at h'
      omega
    · rw [sub_self, mul_zero, add_zero] at h'
      omega

/-- **The edge blow-up does not lower the weight.** -/
theorem characteristicWeight_le_blowUpEdgeCharacteristic (u v : V)
    (h : P.toSimpleGraph.Adj u v) (k : P.characteristicVectors) (δ : ℤˣ)
    (x : V → ℤ) (s : ℤ) :
    P.characteristicWeight k x ≤
      (P.blowUpEdge u v h).characteristicWeight
        (P.blowUpEdgeCharacteristic u v h k (δ : ℤ) (by
          rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num))
        (blowUpEdgeEquiv u v (x, s)) := by
  have hδ : Odd ((δ : ℤ)) := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num
  have h' := P.two_mul_characteristicWeight_blowUpEdgeCharacteristic u v h k (δ : ℤ) hδ x s
  have hnn := zero_le_mul_sub_units δ s
  linarith

/-- **The infimum of the characteristic weight is an edge-blow-up invariant.** -/
theorem sInfCharacteristicWeight_blowUpEdgeCharacteristic (u v : V)
    (h : P.toSimpleGraph.Adj u v) (k : P.characteristicVectors) (δ : ℤˣ) :
    (P.blowUpEdge u v h).sInfCharacteristicWeight
        (P.blowUpEdgeCharacteristic u v h k (δ : ℤ) (by
          rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num)) =
      P.sInfCharacteristicWeight k := by
  have hδ : Odd ((δ : ℤ)) := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num
  rw [sInfCharacteristicWeight_def, sInfCharacteristicWeight_def]
  refine csInf_eq_csInf_of_forall_exists_le ?_ ?_
  · rintro _ ⟨y, rfl⟩
    obtain ⟨⟨x, s⟩, rfl⟩ := (blowUpEdgeEquiv u v).surjective y
    exact ⟨P.characteristicWeight k x, ⟨x, rfl⟩,
      P.characteristicWeight_le_blowUpEdgeCharacteristic u v h k δ x s⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, ⟨blowUpEdgeEquiv u v (x, 0), rfl⟩,
      (P.characteristicWeight_blowUpEdgeCharacteristic_zero u v h k (δ : ℤ) hδ x).le⟩

/-- The infimum of the canonical characteristic weight is unchanged by the edge-blow-up move. -/
theorem sInfCharacteristicWeight_canonicalCharacteristic_blowUpEdge (u v : V)
    (h : P.toSimpleGraph.Adj u v) :
    (P.blowUpEdge u v h).sInfCharacteristicWeight
        ⟨(P.blowUpEdge u v h).canonicalCharacteristic,
          (P.blowUpEdge u v h).isCharacteristicVector_canonicalCharacteristic⟩ =
      P.sInfCharacteristicWeight
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ := by
  rw [← P.blowUpEdgeCharacteristic_canonicalCharacteristic u v h]
  simpa using P.sInfCharacteristicWeight_blowUpEdgeCharacteristic u v h
    ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ (-1)

end Weight

end PlumbingGraph

/-! ### Self-validating example on the `A₂` plumbing -/

/-- The unique edge of the `A₂` plumbing. -/
private theorem a2Plumbing_adj_zero_one : a2Plumbing.toSimpleGraph.Adj 0 1 := by
  by_contra h
  have hM := a2Plumbing.intersectionMatrix_apply_of_ne (by decide : (0 : Fin 2) ≠ 1)
  rw [a2Plumbing_intersectionMatrix] at hM
  simp [h] at hM

/-- A self-validating check on the `A₂` plumbing that the characteristic weight at exceptional
multiplicity `1` over the origin is `1`. -/
example :
    (a2Plumbing.blowUpEdge 0 1 a2Plumbing_adj_zero_one).characteristicWeight
        (a2Plumbing.blowUpEdgeCharacteristic 0 1 a2Plumbing_adj_zero_one
          ⟨a2Plumbing.canonicalCharacteristic,
            a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩ (-1) (by norm_num))
        (PlumbingGraph.blowUpEdgeEquiv 0 1 (0, 1)) = 1 := by
  have h := a2Plumbing.two_mul_characteristicWeight_blowUpEdgeCharacteristic 0 1
    a2Plumbing_adj_zero_one
    ⟨a2Plumbing.canonicalCharacteristic,
      a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩ (-1) (by norm_num) 0 1
  rw [PlumbingGraph.characteristicWeight_zero] at h
  simp only [PlumbingGraph.blowUpEdgeCharacteristic_canonicalCharacteristic] at h ⊢
  omega

/-- A self-validating check on the `A₂` plumbing of the equality locus for the edge blow-up:
at exceptional multiplicity `-1`, the blown-up weight agrees with the weight downstairs (`0`). -/
example :
    (a2Plumbing.blowUpEdge 0 1 a2Plumbing_adj_zero_one).characteristicWeight
        (a2Plumbing.blowUpEdgeCharacteristic 0 1 a2Plumbing_adj_zero_one
          ⟨a2Plumbing.canonicalCharacteristic,
            a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩ (-1) (by norm_num))
        (PlumbingGraph.blowUpEdgeEquiv 0 1 (0, -1)) = 0 := by
  have h := (a2Plumbing.characteristicWeight_blowUpEdgeCharacteristic_eq_iff 0 1
    a2Plumbing_adj_zero_one
    ⟨a2Plumbing.canonicalCharacteristic,
      a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩ (-1) (by norm_num) 0 (-1)).mpr
      (Or.inr (by norm_num))
  rwa [PlumbingGraph.characteristicWeight_zero] at h

end TauCeti
