/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.FiniteType
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Relations

/-!
# The vertex, arrow and volume basis of a zigzag algebra

The zigzag relation quotient `TauCeti.nonisolatedZigzagQuotient` of a finite simple graph `G` kills
every length-two path whose endpoints differ, identifies all the backtracks based at one vertex,
and kills every path of length at least three. What survives is spanned by the vertex idempotents,
the oriented edges, and one *volume* class per vertex. This file proves that these classes are a
basis whenever `G` has no isolated vertex, and reads off the dimension `2|V| + 2|E|`.

Spanning is immediate from the relations. Independence is the substantive half, and is proved by
exhibiting a coordinate map. The path algebra is free on the paths of the doubled quiver, so a
`k`-linear map out of it may be prescribed on paths: send a path of length at most one to itself, a
length-two path returning to its source to a fixed backtrack there, and everything else to `0`.
Sandwiching a relator between two basis paths either produces a path of length at least three or,
when both outer paths are trivial, the relator itself, so this map kills the relation ideal. It
therefore separates the candidate basis classes, which it sends to distinct basis paths.

The hypothesis is that every vertex has a neighbour: an isolated vertex carries no backtrack, so
its volume class does not exist. For a preconnected graph with at least two vertices the hypothesis
is automatic, which is the form the roadmap's dimension count takes.

## Main definitions

* `TauCeti.zigzagVolume`: the volume class of a vertex, the common image of its backtracks.
* `TauCeti.ZigzagBasisIndex`: one index per vertex, carrying its idempotent, one per dart, carrying
  its arrow, and one more per vertex, carrying its volume class.
* `TauCeti.zigzagBasisFun`: the vertex, arrow and volume family.
* `TauCeti.zigzagBasis`: that family, as a basis of the zigzag relation quotient.

## Main results

* `TauCeti.linearIndependent_zigzagBasisFun` and `TauCeti.span_range_zigzagBasisFun_eq_top`: the
  family is independent and spans.
* `TauCeti.finrank_nonisolatedZigzagQuotient`: the dimension is `2|V| + 2|E|`.
* `TauCeti.finrank_nonisolatedZigzagQuotient_of_preconnected`: the same count for a preconnected
  graph with at least two vertices.

## References

This is the first two clauses of Layer 2 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, whose
target signatures `zigzagBasis` and `finrank_zigzagAlgebra` appear in
`TauCetiRoadmap/ZigzagPreprojective/Suggested.lean`. See Huerfano--Khovanov, *A category for the
adjoint representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag
algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

/-! ### A chosen backtrack at each vertex -/

open scoped Classical in
/-- A chosen backtrack loop at a vertex. An isolated vertex has none, and the trivial path is used
as a junk value there. -/
private noncomputable def volumeLoop (i : V) :
    _root_.Quiver.Path (vertex G i) (vertex G i) :=
  if h : ∃ j, G.Adj i j then backtrackPath G h.choose_spec else _root_.Quiver.Path.nil

/-- The chosen backtrack at a vertex, as an indexed path of the doubled quiver. -/
private noncomputable def volumePath (i : V) : Quiver.TotalPath (DoubledQuiver G) :=
  ⟨vertex G i, vertex G i, volumeLoop G i⟩

private theorem volumePath_fst (i : V) : (volumePath G i).1 = vertex G i := (rfl)

private theorem length_volumeLoop {i j : V} (h : G.Adj i j) : (volumeLoop G i).length = 2 := by
  rw [volumeLoop, dite_eq_left (⟨j, h⟩ : ∃ j, G.Adj i j)]
  exact length_backtrackPath G _

/-- A chosen dart out of each vertex of a graph with no isolated vertex. -/
private noncomputable def volumeDart (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) : G.Dart :=
  ⟨(i, (hns i).choose), (hns i).choose_spec⟩

/-- The chosen backtrack at a vertex is the backtrack along the chosen dart out of it. -/
private theorem ofPath_volumePath_eq_backtrackElem (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    (ofPath (volumePath G i) : pathAlgebra k (DoubledQuiver G))
      = backtrackElem G k (volumeDart G hns i).adj := by
  rw [volumePath, volumeLoop, dite_eq_left (hns i), backtrackElem_eq_ofPath]
  rfl

/-! ### Volume classes -/

variable [Finite V]

open scoped Classical in
/-- The volume class of a vertex of a simple graph: the common image in the zigzag relation
quotient of all the backtracks based at that vertex, which `TauCeti.zigzagMk_backtrackElem_eq`
shows is independent of the incident edge chosen. It is the junk value `0` on an isolated vertex,
which carries no backtrack. -/
noncomputable def zigzagVolume (i : V) : nonisolatedZigzagQuotient k G :=
  if h : ∃ j, G.Adj i j then zigzagMk k G (backtrackElem G k h.choose_spec) else 0

/-- The volume class of a vertex is the class of any backtrack based there. -/
theorem zigzagVolume_eq_zigzagMk_backtrackElem {i j : V} (h : G.Adj i j) :
    zigzagVolume k G i = zigzagMk k G (backtrackElem G k h) := by
  rw [zigzagVolume, dite_eq_left (⟨j, h⟩ : ∃ j, G.Adj i j)]
  exact zigzagMk_backtrackElem_eq k G _ h

/-- The class of a backtrack is the volume class of its base vertex. This is the direction
automation can use: both endpoints are determined by the adjacency on the left-hand side. -/
@[simp]
theorem zigzagMk_backtrackElem_eq_zigzagVolume {i j : V} (h : G.Adj i j) :
    zigzagMk k G (backtrackElem G k h) = zigzagVolume k G i :=
  (zigzagVolume_eq_zigzagMk_backtrackElem k G h).symm

/-- The volume class of an isolated vertex is the junk value `0`: it carries no backtrack. -/
@[simp]
theorem zigzagVolume_eq_zero_of_isIsolated {i : V} (h : G.IsIsolated i) :
    zigzagVolume k G i = 0 := by
  rw [zigzagVolume, dite_eq_right fun hi => SimpleGraph.exists_adj_iff_not_isIsolated.mp hi h]

private theorem zigzagMk_ofPath_volumePath {i j : V} (h : G.Adj i j) :
    zigzagMk k G (ofPath (volumePath G i)) = zigzagVolume k G i := by
  have hex : ∃ j, G.Adj i j := ⟨j, h⟩
  rw [volumePath, volumeLoop, dite_eq_left hex, zigzagVolume, dite_eq_left hex,
    backtrackElem_eq_ofPath]

/-! ### The vertex, arrow and volume family -/

/-- The basis indices of a zigzag algebra: a vertex, carrying its idempotent, an oriented edge,
carrying its arrow, and a vertex again, carrying its volume class. The three blocks are
represented by paths of length zero, one and two respectively. -/
abbrev ZigzagBasisIndex : Type _ := V ⊕ G.Dart ⊕ V

/-- The vertex, arrow and volume family of a zigzag algebra: the class of a vertex idempotent, the
class of the arrow of a dart, and the volume class of a vertex. -/
noncomputable def zigzagBasisFun : ZigzagBasisIndex G → nonisolatedZigzagQuotient k G
  | .inl i => zigzagMk k G (vertexIdempotent k (vertex G i))
  | .inr (.inl d) => zigzagMk k G (ofArrow (arrow G d.adj))
  | .inr (.inr i) => zigzagVolume k G i

@[simp]
theorem zigzagBasisFun_inl (i : V) :
    zigzagBasisFun k G (.inl i) = zigzagMk k G (vertexIdempotent k (vertex G i)) := (rfl)

@[simp]
theorem zigzagBasisFun_inr_inl (d : G.Dart) :
    zigzagBasisFun k G (.inr (.inl d)) = zigzagMk k G (ofArrow (arrow G d.adj)) := (rfl)

@[simp]
theorem zigzagBasisFun_inr_inr (i : V) :
    zigzagBasisFun k G (.inr (.inr i)) = zigzagVolume k G i := (rfl)

/-- The indexed path underlying each member of the basis family: the trivial path at a vertex, the
arrow of a dart, and the chosen backtrack at a vertex. -/
private noncomputable def zigzagBasisPath :
    ZigzagBasisIndex G → Quiver.TotalPath (DoubledQuiver G)
  | .inl i => ⟨vertex G i, vertex G i, _root_.Quiver.Path.nil⟩
  | .inr (.inl d) => ⟨vertex G d.fst, vertex G d.snd, arrowPath G d.adj⟩
  | .inr (.inr i) => volumePath G i

private theorem zigzagMk_ofPath_zigzagBasisPath (hns : ∀ i : V, ∃ j, G.Adj i j)
    (b : ZigzagBasisIndex G) :
    zigzagMk k G (ofPath (zigzagBasisPath G b)) = zigzagBasisFun k G b := by
  rcases b with i | d | i
  · simp only [zigzagBasisPath, zigzagBasisFun_inl, vertexIdempotent_eq_single, ofPath_eq_single]
  · simp only [zigzagBasisPath, zigzagBasisFun_inr_inl, ofArrow_eq_ofPath_arrowPath]
  · obtain ⟨j, h⟩ := hns i
    simp only [zigzagBasisPath]
    exact zigzagMk_ofPath_volumePath k G h

/-! ### The coordinate map -/

open scoped Classical in
/-- The value on a basis path of the coordinate map used to separate the basis classes: a path of
length at most one goes to itself, a length-two path returning to its source goes to the chosen
backtrack there, and every other path dies. -/
private noncomputable def shortCoord (x : Quiver.TotalPath (DoubledQuiver G)) :
    pathAlgebra k (DoubledQuiver G) :=
  if x.2.2.length ≤ 1 then ofPath x
  else if x.2.2.length = 2 ∧ x.2.1 = x.1 then ofPath (volumePath G ((vertexEquiv G).symm x.1))
  else 0

/-- The coordinate map of the zigzag relations: the `k`-linear extension of `shortCoord`. -/
private noncomputable def shortProj :
    pathAlgebra k (DoubledQuiver G) →ₗ[k] pathAlgebra k (DoubledQuiver G) :=
  liftLinear k (shortCoord k G)

private theorem shortProj_ofPath_of_length_le_one {a b : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (hp : p.length ≤ 1) :
    shortProj k G (ofPath ⟨a, b, p⟩) = ofPath ⟨a, b, p⟩ := by
  rw [shortProj, liftLinear_ofPath, shortCoord, ite_eq_left hp]

private theorem shortProj_ofPath_eq_zero_of_three_le {a b : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (hp : 3 ≤ p.length) :
    shortProj k G (ofPath ⟨a, b, p⟩) = 0 := by
  rw [shortProj, liftLinear_ofPath, shortCoord,
    ite_eq_right (Nat.not_le.mpr (by omega : 1 < p.length)),
    ite_eq_right fun h => by
      have h2 : p.length = 2 := h.1
      omega]

private theorem shortProj_ofPath_eq_zero_of_ne {a b : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (hp : p.length = 2) (hne : b ≠ a) :
    shortProj k G (ofPath ⟨a, b, p⟩) = 0 := by
  rw [shortProj, liftLinear_ofPath, shortCoord,
    ite_eq_right (Nat.not_le.mpr (by omega : 1 < p.length)), ite_eq_right fun h => hne h.2]

private theorem shortProj_ofPath_of_loop {a : DoubledQuiver G} (p : _root_.Quiver.Path a a)
    (hp : p.length = 2) :
    shortProj k G (ofPath ⟨a, a, p⟩) = ofPath (volumePath G ((vertexEquiv G).symm a)) := by
  rw [shortProj, liftLinear_ofPath, shortCoord,
    ite_eq_right (Nat.not_le.mpr (by omega : 1 < p.length)), ite_eq_left ⟨hp, rfl⟩]

private theorem shortProj_ofPath_zigzagBasisPath (b : ZigzagBasisIndex G) :
    shortProj k G (ofPath (zigzagBasisPath G b)) = ofPath (zigzagBasisPath G b) := by
  rcases b with i | d | i
  · exact shortProj_ofPath_of_length_le_one k G _ (by simp)
  · exact shortProj_ofPath_of_length_le_one k G _ (by simp)
  · simp only [zigzagBasisPath]
    by_cases h : ∃ j, G.Adj i j
    · obtain ⟨j, hj⟩ := h
      refine (shortProj_ofPath_of_loop k G (volumeLoop G i) (length_volumeLoop G hj)).trans ?_
      rw [vertexEquiv_symm_vertex]
    · rw [volumePath, volumeLoop, dite_eq_right h]
      exact shortProj_ofPath_of_length_le_one k G _ (by simp)

/-! ### The coordinate map kills the relation ideal -/

/-- A path of length at least two, sandwiched between two composable paths of positive total
length, is killed by the coordinate map: the composite has length at least three. -/
private theorem shortProj_sandwich_of_pos {a b c e : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r : _root_.Quiver.Path c a) (q : _root_.Quiver.Path e c)
    (hr : 2 ≤ r.length) (hpq : 0 < p.length + q.length) :
    shortProj k G (ofPath ⟨a, b, p⟩ * ofPath ⟨c, a, r⟩ * ofPath ⟨e, c, q⟩) = 0 := by
  rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp]
  refine shortProj_ofPath_eq_zero_of_three_le k G _ ?_
  rw [_root_.Quiver.Path.length_comp, _root_.Quiver.Path.length_comp]
  omega

/-- Sandwiching a path between composable paths of length zero reduces to the middle path. -/
private theorem shortProj_sandwich_of_length_zero {a b c e : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r : _root_.Quiver.Path c a) (q : _root_.Quiver.Path e c)
    (hp : p.length = 0) (hq : q.length = 0) :
    shortProj k G (ofPath ⟨a, b, p⟩ * ofPath ⟨c, a, r⟩ * ofPath ⟨e, c, q⟩) =
      shortProj k G (ofPath ⟨c, a, r⟩) := by
  obtain rfl := p.eq_of_length_zero hp
  obtain rfl := p.eq_nil_of_length_zero hp
  obtain rfl := q.eq_of_length_zero hq
  obtain rfl := q.eq_nil_of_length_zero hq
  rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp,
    _root_.Quiver.Path.comp_nil, _root_.Quiver.Path.nil_comp]

/-- Sandwiching between two paths a path of length at least two that the coordinate map already
kills is again killed by the coordinate map. -/
private theorem shortProj_sandwich_ofPath {a b c d e f : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r : _root_.Quiver.Path c d) (q : _root_.Quiver.Path e f)
    (hr : 2 ≤ r.length) (hzero : shortProj k G (ofPath ⟨c, d, r⟩) = 0) :
    shortProj k G (ofPath ⟨a, b, p⟩ * ofPath ⟨c, d, r⟩ * ofPath ⟨e, f, q⟩) = 0 := by
  by_cases hda : d = a
  · subst hda
    by_cases hfc : f = c
    · subst hfc
      rcases Nat.eq_zero_or_pos (p.length + q.length) with hlen | hlen
      · have hp : p.length = 0 := by omega
        have hq : q.length = 0 := by omega
        rw [shortProj_sandwich_of_length_zero k G p r q hp hq, hzero]
      · exact shortProj_sandwich_of_pos k G p r q hr hlen
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_not_composable hfc, map_zero]
  · rw [ofPath_mul_ofPath_of_not_composable hda, zero_mul, map_zero]

/-- Sandwiching between two paths the difference of two length-two loops at one vertex is killed
by the coordinate map: the two loops have the same coordinate. -/
private theorem shortProj_sandwich_sub {a b c e f : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r₁ r₂ : _root_.Quiver.Path c c)
    (q : _root_.Quiver.Path e f) (h₁ : r₁.length = 2) (h₂ : r₂.length = 2) :
    shortProj k G
      (ofPath ⟨a, b, p⟩ * (ofPath ⟨c, c, r₁⟩ - ofPath ⟨c, c, r₂⟩) * ofPath ⟨e, f, q⟩) = 0 := by
  rw [mul_sub, sub_mul, map_sub]
  by_cases hca : c = a
  · subst hca
    by_cases hfc : f = c
    · subst hfc
      rcases Nat.eq_zero_or_pos (p.length + q.length) with hlen | hlen
      · have hp : p.length = 0 := by omega
        have hq : q.length = 0 := by omega
        rw [shortProj_sandwich_of_length_zero k G p r₁ q hp hq,
          shortProj_sandwich_of_length_zero k G p r₂ q hp hq,
          shortProj_ofPath_of_loop k G r₁ h₁, shortProj_ofPath_of_loop k G r₂ h₂, sub_self]
      · rw [shortProj_sandwich_of_pos k G p r₁ q h₁.ge hlen,
          shortProj_sandwich_of_pos k G p r₂ q h₂.ge hlen, sub_zero]
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp,
        ofPath_mul_ofPath_of_not_composable hfc, ofPath_mul_ofPath_of_not_composable hfc]
      simp
  · rw [ofPath_mul_ofPath_of_not_composable hca, ofPath_mul_ofPath_of_not_composable hca]
    simp

private theorem shortProj_ofPath_mul_relator_mul_ofPath {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) (pu pv : Quiver.TotalPath (DoubledQuiver G)) :
    shortProj k G (ofPath pu * x * ofPath pv) = 0 := by
  obtain ⟨a, b, p⟩ := pu
  obtain ⟨e, f, q⟩ := pv
  cases hx with
  | quadratic hq =>
    cases hq with
    | nonreturn r hlen hij =>
      exact shortProj_sandwich_ofPath k G p r q hlen.ge
        (shortProj_ofPath_eq_zero_of_ne k G r hlen (Ne.symm hij))
    | equal_backtracks r₁ r₂ hr₁ hr₂ => exact shortProj_sandwich_sub k G p r₁ r₂ q hr₁ hr₂
  | long_path z hz =>
    obtain ⟨c, d, r⟩ := z
    exact shortProj_sandwich_ofPath k G p r q (Nat.le_of_succ_le hz)
      (shortProj_ofPath_eq_zero_of_three_le k G r hz)

private theorem shortProj_mul_relator_mul {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) (u v : pathAlgebra k (DoubledQuiver G)) :
    shortProj k G (u * x * v) = 0 := by
  induction u using PathAlgebra.induction_linear with
  | zero => simp
  | add u₁ u₂ hu₁ hu₂ => rw [add_mul, add_mul, map_add, hu₁, hu₂, add_zero]
  | single pu cu =>
    induction v using PathAlgebra.induction_linear with
    | zero => simp
    | add v₁ v₂ hv₁ hv₂ => rw [mul_add, map_add, hv₁, hv₂, add_zero]
    | single pv cv =>
      rw [single_eq_smul_ofPath, single_eq_smul_ofPath, smul_mul_assoc, smul_mul_assoc,
        mul_smul_comm, map_smul, map_smul, shortProj_ofPath_mul_relator_mul_ofPath k G hx,
        smul_zero, smul_zero]

private theorem shortProj_eq_zero_of_mem_zigzagIdeal {x : pathAlgebra k (DoubledQuiver G)}
    (hx : x ∈ zigzagIdeal k G) : shortProj k G x = 0 := by
  rw [zigzagIdeal_eq_span, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨w, hw, v, -, rfl⟩ := hy
    obtain ⟨u, -, r, hr, rfl⟩ := hw
    exact shortProj_mul_relator_mul k G hr u v
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | neg y _ hy => rw [map_neg, hy, neg_zero]

/-! ### The basis -/

omit [Finite V] in
/-- The paths underlying the basis family are the trivial paths, the arrows of the darts, and the
backtracks along the chosen darts, so their independence is the independence of the vertex
idempotents, the oriented edges and the backtracks, reindexed along an injection. -/
private theorem linearIndependent_ofPath_zigzagBasisPath (hns : ∀ i : V, ∃ j, G.Adj i j) :
    LinearIndependent k fun b : ZigzagBasisIndex G =>
      (ofPath (zigzagBasisPath G b) : pathAlgebra k (DoubledQuiver G)) := by
  have hfam : (fun b : ZigzagBasisIndex G =>
      (ofPath (zigzagBasisPath G b) : pathAlgebra k (DoubledQuiver G)))
      = Sum.elim (fun v : V => (vertexIdempotent k (vertex G v) : pathAlgebra k (DoubledQuiver G)))
          (Sum.elim (fun d : G.Dart => (ofArrow (arrow G d.adj) : pathAlgebra k (DoubledQuiver G)))
            fun d : G.Dart => backtrackElem G k d.adj) ∘
        Sum.map id (Sum.map id (volumeDart G hns)) := by
    funext b
    rcases b with i | d | i
    · simp [zigzagBasisPath, vertexIdempotent_eq_single, ofPath_eq_single]
    · simp [zigzagBasisPath, arrowPath_eq_toPath]
    · exact ofPath_volumePath_eq_backtrackElem k G hns i
  have hdart : Function.Injective (volumeDart G hns) :=
    fun _ _ h => congrArg (fun d : G.Dart => d.toProd.1) h
  rw [hfam]
  exact (linearIndependent_vertexIdempotent_ofArrow_backtrackElem G k).comp _
    (Sum.map_injective.2 ⟨Function.injective_id,
      Sum.map_injective.2 ⟨Function.injective_id, hdart⟩⟩)

/-- **The vertex, arrow and volume classes are independent.** -/
theorem linearIndependent_zigzagBasisFun (hns : ∀ i : V, ∃ j, G.Adj i j) :
    LinearIndependent k (zigzagBasisFun k G) := by
  rw [linearIndependent_iff]
  intro l hl
  have hcomp : zigzagBasisFun k G = ⇑(zigzagMk k G).toLinearMap ∘
      fun b : ZigzagBasisIndex G => (ofPath (zigzagBasisPath G b)) := by
    funext b
    rw [Function.comp_apply, AlgHom.toLinearMap_apply,
      zigzagMk_ofPath_zigzagBasisPath k G hns b]
  rw [hcomp, ← Finsupp.apply_linearCombination, AlgHom.toLinearMap_apply] at hl
  have hzero := shortProj_eq_zero_of_mem_zigzagIdeal k G ((zigzagMk_eq_zero_iff k G).mp hl)
  rw [Finsupp.apply_linearCombination] at hzero
  refine linearIndependent_iff.mp (linearIndependent_ofPath_zigzagBasisPath k G hns) l ?_
  rw [← hzero]
  exact congrArg (fun f => Finsupp.linearCombination k f l)
    (funext fun b => (shortProj_ofPath_zigzagBasisPath k G b).symm)

/-- **The vertex, arrow and volume classes span.** -/
theorem span_range_zigzagBasisFun_eq_top :
    Submodule.span k (Set.range (zigzagBasisFun k G)) = ⊤ := by
  have key : ∀ x : Quiver.TotalPath (DoubledQuiver G),
      zigzagMk k G (ofPath x) ∈ Submodule.span k (Set.range (zigzagBasisFun k G)) := by
    rintro ⟨a, b, p⟩
    obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
      ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = vertex G j :=
      ⟨(vertexEquiv G).symm b, (vertexEquiv_symm_apply G b).symm⟩
    rcases Nat.lt_or_ge p.length 3 with hlt | hge
    · have hcases : p.length = 0 ∨ p.length = 1 ∨ p.length = 2 := by omega
      rcases hcases with hp | hp | hp
      · obtain rfl : i = j := (vertex_inj G).mp (p.eq_of_length_zero hp)
        obtain rfl : p = _root_.Quiver.Path.nil := p.eq_nil_of_length_zero hp
        refine Submodule.subset_span ⟨.inl i, ?_⟩
        rw [zigzagBasisFun_inl, vertexIdempotent_eq_single, ofPath_eq_single]
      · obtain ⟨h, rfl⟩ := exists_eq_arrowPath G p hp
        refine Submodule.subset_span ⟨.inr (.inl ⟨(i, j), h⟩), ?_⟩
        rw [zigzagBasisFun_inr_inl, ofArrow_eq_ofPath_arrowPath]
      · rcases eq_or_ne i j with rfl | hij
        · obtain ⟨j', h, rfl⟩ := exists_eq_backtrackPath G p hp
          refine Submodule.subset_span ⟨.inr (.inr i), ?_⟩
          rw [zigzagBasisFun_inr_inr, zigzagVolume_eq_zigzagMk_backtrackElem k G h,
            backtrackElem_eq_ofPath]
        · rw [zigzagMk_ofPath_eq_zero_of_ne k G p hp ((vertex_injective G).ne hij)]
          exact Submodule.zero_mem _
    · rw [zigzagMk_ofPath_eq_zero_of_three_le k G ⟨_, _, p⟩ hge]
      exact Submodule.zero_mem _
  -- the images of *all* the basis paths span the quotient, the quotient map being onto
  have htop : Submodule.span k (Set.range fun x : Quiver.TotalPath (DoubledQuiver G) =>
      (zigzagMk k G).toLinearMap (ofPath x)) = ⊤ := by
    have hsurj : Function.Surjective ⇑(zigzagMk k G).toLinearMap := fun y => by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨f, zigzagMk_apply k G f⟩
    have hmap : Submodule.map (zigzagMk k G).toLinearMap ⊤ = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
    rw [← hmap, ← (pathAlgebraBasis k (DoubledQuiver G)).span_eq, Submodule.map_span,
      coe_pathAlgebraBasis, ← Set.range_comp]
    rfl
  rw [eq_top_iff, ← htop]
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun x => SetLike.mem_coe.2 (key x))

/-- **The basis of a zigzag algebra.** For a finite simple graph with no isolated vertex the vertex
idempotents, the oriented edges, and the volume classes are a basis of the zigzag relation
quotient. The three blocks are represented by paths of length `0`, `1` and `2`; the path grading
itself is not formalised in this repository, so homogeneity is not stated here. -/
noncomputable def zigzagBasis (hns : ∀ i : V, ∃ j, G.Adj i j) :
    Module.Basis (ZigzagBasisIndex G) k (nonisolatedZigzagQuotient k G) :=
  Module.Basis.mk (linearIndependent_zigzagBasisFun k G hns)
    (span_range_zigzagBasisFun_eq_top k G).ge

@[simp]
theorem zigzagBasis_apply (hns : ∀ i : V, ∃ j, G.Adj i j) (b : ZigzagBasisIndex G) :
    zigzagBasis k G hns b = zigzagBasisFun k G b :=
  Module.Basis.mk_apply _ _ _

/-- The volume class of a vertex with a neighbour is nonzero, whatever the rest of the graph does:
its chosen backtrack survives the coordinate map. -/
theorem zigzagVolume_ne_zero [Nontrivial k] {i j : V} (h : G.Adj i j) :
    zigzagVolume k G i ≠ 0 := by
  have hne : (ofPath (volumePath G i) : pathAlgebra k (DoubledQuiver G)) ≠ 0 := by
    simpa using (pathAlgebraBasis k (DoubledQuiver G)).ne_zero (volumePath G i)
  intro hvol
  rw [zigzagVolume_eq_zigzagMk_backtrackElem k G h, zigzagMk_eq_zero_iff] at hvol
  have hproj := shortProj_eq_zero_of_mem_zigzagIdeal k G hvol
  rw [backtrackElem_eq_ofPath, shortProj_ofPath_of_loop k G (backtrackPath G h)
    (length_backtrackPath G h), vertexEquiv_symm_vertex] at hproj
  exact hne hproj

/-! ### The dimension -/

/-- **The dimension of a zigzag algebra.** A finite simple graph with no isolated vertex has
`dim Z(G) = 2|V| + 2|E|`: two classes at each vertex and two arrows over each edge. -/
theorem finrank_nonisolatedZigzagQuotient [Nontrivial k] [Fintype V] [DecidableRel G.Adj]
    (hns : ∀ i : V, ∃ j, G.Adj i j) :
    Module.finrank k (nonisolatedZigzagQuotient k G)
      = 2 * Fintype.card V + 2 * G.edgeFinset.card := by
  rw [Module.finrank_eq_card_basis (zigzagBasis k G hns)]
  simp only [ZigzagBasisIndex, Fintype.card_sum, G.dart_card_eq_twice_card_edges]
  ring

/-- **The dimension of the zigzag algebra of a preconnected graph.** For a preconnected graph with
at least two vertices, `dim Z(G) = 2|V| + 2|E|`: preconnectedness leaves no isolated vertex. -/
theorem finrank_nonisolatedZigzagQuotient_of_preconnected [Nontrivial k] [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] (hconn : G.Preconnected) :
    Module.finrank k (nonisolatedZigzagQuotient k G)
      = 2 * Fintype.card V + 2 * G.edgeFinset.card :=
  finrank_nonisolatedZigzagQuotient k G fun i =>
    SimpleGraph.exists_adj_iff_not_isIsolated.mpr (hconn.not_isIsolated i)

end TauCeti
