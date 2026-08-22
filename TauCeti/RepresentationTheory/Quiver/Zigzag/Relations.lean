/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.RepresentationTheory.Quiver.Zigzag.PathAlgebra

/-!
# The zigzag relations and their quadratic presentation

The zigzag algebra of a simple graph `G` is the path algebra of the doubled quiver
`TauCeti.DoubledQuiver G` modulo the *uniform* relation family: every length-two path whose
endpoints differ, the difference of any two length-two backtracks based at one vertex, and every
path of length at least three. This file introduces those relators, the two-sided ideal they span,
and the resulting quotient algebra with its universal property.

The long-path generators are convenient rather than necessary: the main result below shows that
for a connected graph with at least three vertices they are already consequences of the two
quadratic families, so the algebra really is quadratic there. The proof is the usual local one.
A length-three path either contains a length-two subpath with distinct endpoints, in which case it
already lies in the quadratic ideal, or it is an arrow following a backtrack. Backtrack
independence lets that backtrack be moved onto any incident edge, and connectedness with at least
three vertices produces a third vertex adjacent to one of the two vertices involved; moving the
backtrack there exposes a length-two subpath with distinct endpoints.

The graphs excluded by the hypotheses are exactly those the roadmap treats separately: the
one-vertex graph, whose zigzag algebra is the dual numbers rather than a relation quotient, and
the two-vertex graph `A₂`, whose zigzag algebra is genuinely radical-cube-zero and not quadratic.

## Main definitions

* `TauCeti.IsQuadraticZigzagRelator`: the two quadratic relation families.
* `TauCeti.IsZigzagRelator`: the uniform relation family, adding the long paths.
* `TauCeti.zigzagIdeal` and `TauCeti.quadraticZigzagIdeal`: the two-sided ideals they span, with
  `TauCeti.zigzagIdeal_eq_span` and `TauCeti.quadraticZigzagIdeal_eq_span` recording the spans.
* `TauCeti.nonisolatedZigzagQuotient`: the relation quotient, with quotient map
  `TauCeti.zigzagMk` and universal property `TauCeti.zigzagLift`.

## Main results

* `TauCeti.zigzagIdeal_eq_quadraticZigzagIdeal`: for a connected graph with at least three
  vertices the long-path generators are redundant.
* `TauCeti.zigzagLiftOfQuadratic`: consequently an algebra map killing the quadratic relators
  factors through the zigzag quotient.
* `TauCeti.zigzagMk_ofPath_eq_zero_of_ne`, `TauCeti.zigzagMk_backtrackElem_eq` and
  `TauCeti.zigzagMk_ofPath_eq_zero_of_three_le`: the defining relations in the quotient.

## References

This is the relation-quotient clause of Layer 0 and the redundancy theorem of Layer 1 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`; the relator names follow the target-signature
prototype in `TauCetiRoadmap/ZigzagPreprojective/Suggested.lean`. See Huerfano--Khovanov,
*A category for the adjoint representation*, Section 3.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

/-! ### The relators -/

/-- The quadratic zigzag relators of a simple graph: the length-two paths whose endpoints differ,
and the differences of two length-two paths returning to a common source. By
`TauCeti.DoubledQuiver.exists_eq_backtrackPath` the latter are exactly the differences of two
backtracks based at one vertex. -/
inductive IsQuadraticZigzagRelator (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) :
    pathAlgebra k (DoubledQuiver G) → Prop
  | nonreturn {i j : DoubledQuiver G} (p : _root_.Quiver.Path i j) (length_eq : p.length = 2)
      (different_endpoints : i ≠ j) : IsQuadraticZigzagRelator k G (ofPath ⟨i, j, p⟩)
  | equal_backtracks {i : DoubledQuiver G} (p q : _root_.Quiver.Path i i)
      (p_length : p.length = 2) (q_length : q.length = 2) :
      IsQuadraticZigzagRelator k G (ofPath ⟨i, i, p⟩ - ofPath ⟨i, i, q⟩)

/-- The uniform zigzag relators of a simple graph: the quadratic relators together with every path
of length at least three. The long generators make the quotient radical-cube-zero for every graph,
including the two-vertex graph `A₂` where they are not consequences of the quadratic relators. -/
inductive IsZigzagRelator (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) :
    pathAlgebra k (DoubledQuiver G) → Prop
  | quadratic {x : pathAlgebra k (DoubledQuiver G)} (h : IsQuadraticZigzagRelator k G x) :
      IsZigzagRelator k G x
  | long_path (x : Quiver.TotalPath (DoubledQuiver G)) (three_le : 3 ≤ x.2.2.length) :
      IsZigzagRelator k G (ofPath x)

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

/-! ### The relation ideals -/

variable [Finite V]

/-- The two-sided ideal spanned by the quadratic zigzag relators. -/
noncomputable def quadraticZigzagIdeal : TwoSidedIdeal (pathAlgebra k (DoubledQuiver G)) :=
  TwoSidedIdeal.span {x | IsQuadraticZigzagRelator k G x}

/-- The two-sided ideal spanned by the uniform zigzag relators. -/
noncomputable def zigzagIdeal : TwoSidedIdeal (pathAlgebra k (DoubledQuiver G)) :=
  TwoSidedIdeal.span {x | IsZigzagRelator k G x}

/-- The defining span of the quadratic relation ideal. The body of a definition is not visible
outside its own module, so this records it for the callers that reason about the span itself. -/
theorem quadraticZigzagIdeal_eq_span :
    quadraticZigzagIdeal k G = TwoSidedIdeal.span {x | IsQuadraticZigzagRelator k G x} := (rfl)

/-- The defining span of the uniform relation ideal. The body of a definition is not visible
outside its own module, so this records it for the callers that reason about the span itself. -/
theorem zigzagIdeal_eq_span :
    zigzagIdeal k G = TwoSidedIdeal.span {x | IsZigzagRelator k G x} := (rfl)

/-- Every quadratic relator lies in the ideal it spans. -/
theorem mem_quadraticZigzagIdeal_of_isQuadraticZigzagRelator
    {x : pathAlgebra k (DoubledQuiver G)} (hx : IsQuadraticZigzagRelator k G x) :
    x ∈ quadraticZigzagIdeal k G :=
  TwoSidedIdeal.subset_span hx

/-- Every uniform relator lies in the ideal it spans. -/
theorem mem_zigzagIdeal_of_isZigzagRelator {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) : x ∈ zigzagIdeal k G :=
  TwoSidedIdeal.subset_span hx

/-- The quadratic relators are among the uniform ones, so their ideal is contained in the uniform
one. The reverse inclusion is the redundancy theorem below, and needs hypotheses on the graph. -/
theorem quadraticZigzagIdeal_le_zigzagIdeal :
    quadraticZigzagIdeal k G ≤ zigzagIdeal k G :=
  TwoSidedIdeal.span_mono fun _ hx => IsZigzagRelator.quadratic hx

/-! ### Membership of the short products -/

/-- A length-two path whose endpoints differ is a quadratic relator, written as a product of two
oriented edges. -/
theorem ofArrow_mul_ofArrow_mem_quadraticZigzagIdeal {i j l : V} (h : G.Adj i j) (h' : G.Adj j l)
    (hne : i ≠ l) :
    (ofArrow (arrow G h') * ofArrow (arrow G h) : pathAlgebra k (DoubledQuiver G))
      ∈ quadraticZigzagIdeal k G := by
  rw [ofArrow_mul_ofArrow]
  refine mem_quadraticZigzagIdeal_of_isQuadraticZigzagRelator k G
    (IsQuadraticZigzagRelator.nonreturn _ ?_ ?_)
  · simp [_root_.Quiver.Path.length_comp]
  · simpa using hne

/-- Two backtracks based at the same vertex differ by a quadratic relator. -/
theorem backtrackElem_sub_backtrackElem_mem_quadraticZigzagIdeal {i j j' : V} (h : G.Adj i j)
    (h' : G.Adj i j') :
    backtrackElem G k h - backtrackElem G k h' ∈ quadraticZigzagIdeal k G := by
  rw [backtrackElem_eq_ofPath, backtrackElem_eq_ofPath]
  exact mem_quadraticZigzagIdeal_of_isQuadraticZigzagRelator k G
    (IsQuadraticZigzagRelator.equal_backtracks _ _ (by simp) (by simp))

/-- Left multiples of the backtracks at a vertex all lie in the quadratic ideal together. -/
private theorem mul_backtrackElem_mem_of_mem {a : pathAlgebra k (DoubledQuiver G)} {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j')
    (hmem : a * backtrackElem G k h' ∈ quadraticZigzagIdeal k G) :
    a * backtrackElem G k h ∈ quadraticZigzagIdeal k G := by
  have hsub := (quadraticZigzagIdeal k G).mul_mem_left a _
    (backtrackElem_sub_backtrackElem_mem_quadraticZigzagIdeal k G h h')
  have hadd := (quadraticZigzagIdeal k G).add_mem hsub hmem
  rwa [mul_sub, sub_add_cancel] at hadd

/-- Right multiples of the backtracks at a vertex all lie in the quadratic ideal together. -/
private theorem backtrackElem_mul_mem_of_mem {a : pathAlgebra k (DoubledQuiver G)} {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j')
    (hmem : backtrackElem G k h' * a ∈ quadraticZigzagIdeal k G) :
    backtrackElem G k h * a ∈ quadraticZigzagIdeal k G := by
  have hsub := (quadraticZigzagIdeal k G).mul_mem_right _ a
    (backtrackElem_sub_backtrackElem_mem_quadraticZigzagIdeal k G h h')
  have hadd := (quadraticZigzagIdeal k G).add_mem hsub hmem
  rwa [sub_mul, sub_add_cancel] at hadd

/-! ### The redundancy of the long relators -/

/-- In a connected graph with at least three vertices, any two vertices have a neighbour outside
the pair they form. This is the local hypothesis that makes the zigzag relations quadratic; it is
what fails for the one-edge graph `A₂`. -/
private theorem exists_adj_thirdVertex (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) (i m : V) :
    ∃ n : V, n ≠ i ∧ n ≠ m ∧ (G.Adj i n ∨ G.Adj m n) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨w, hwi, hwm⟩ : ∃ w : V, w ≠ i ∧ w ≠ m := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset V) ⊆ {i, m} := by
      intro v _
      rcases eq_or_ne v i with rfl | hv
      · simp
      · simp [hcon v hv]
    have hle := Finset.card_le_card hsub
    have h2 : ({i, m} : Finset V).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨p⟩ := hconn.preconnected i w
  obtain ⟨d, -, hd, hd'⟩ :=
    p.exists_boundary_dart ({i, m} : Set V) (by simp) (by simp [hwi, hwm])
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hd hd'
  refine ⟨d.snd, hd'.1, hd'.2, ?_⟩
  rcases hd with hfst | hfst
  · exact Or.inl (by rw [← hfst]; exact d.adj)
  · exact Or.inr (by rw [← hfst]; exact d.adj)

/-- The heart of the redundancy theorem: an oriented edge out of `i` followed by a backtrack at `i`
lies in the quadratic ideal. -/
private theorem ofArrow_mul_backtrackElem_mem (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) {i j m : V} (hj : G.Adj i j) (hm : G.Adj i m) :
    (ofArrow (arrow G hm) * backtrackElem G k hj : pathAlgebra k (DoubledQuiver G))
      ∈ quadraticZigzagIdeal k G := by
  refine mul_backtrackElem_mem_of_mem k G hj hm ?_
  obtain ⟨n, hni, hnm, hn⟩ := exists_adj_thirdVertex G hconn hcard i m
  rcases hn with hin | hmn
  · -- Move the backtrack at `i` onto the edge to `n`; then `n → i → m` does not return.
    refine mul_backtrackElem_mem_of_mem k G hm hin ?_
    rw [backtrackElem_eq_ofPath, backtrackPath_eq_comp, ← ofArrow_mul_ofArrow, ← mul_assoc]
    exact (quadraticZigzagIdeal k G).mul_mem_right _ _
      (ofArrow_mul_ofArrow_mem_quadraticZigzagIdeal k G hin.symm hm hnm)
  · -- Regroup to a backtrack at `m`, move it onto the edge to `n`; then `i → m → n` does not
    -- return.
    have hregroup : (ofArrow (arrow G hm) * backtrackElem G k hm :
        pathAlgebra k (DoubledQuiver G)) = backtrackElem G k hm.symm * ofArrow (arrow G hm) := by
      rw [backtrackElem_eq_ofPath, backtrackPath_eq_comp, ← ofArrow_mul_ofArrow, ← mul_assoc,
        ← ofArrow_symm_mul_ofArrow G k hm.symm]
    rw [hregroup]
    refine backtrackElem_mul_mem_of_mem k G hm.symm hmn ?_
    rw [backtrackElem_eq_ofPath, backtrackPath_eq_comp, ← ofArrow_mul_ofArrow, mul_assoc]
    exact (quadraticZigzagIdeal k G).mul_mem_left _ _
      (ofArrow_mul_ofArrow_mem_quadraticZigzagIdeal k G hm hmn hni.symm)

/-- Extending a length-two path by one arrow lands in the quadratic ideal. -/
private theorem ofArrow_mul_ofPath_mem (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) {a c b : DoubledQuiver G} (q : _root_.Quiver.Path a c)
    (hq : q.length = 2) (e : c ⟶ b) :
    (ofArrow e * ofPath ⟨a, c, q⟩ : pathAlgebra k (DoubledQuiver G))
      ∈ quadraticZigzagIdeal k G := by
  obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
    ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
  obtain ⟨l, rfl⟩ : ∃ l, c = vertex G l :=
    ⟨(vertexEquiv G).symm c, (vertexEquiv_symm_apply G c).symm⟩
  obtain ⟨m, rfl⟩ : ∃ m, b = vertex G m :=
    ⟨(vertexEquiv G).symm b, (vertexEquiv_symm_apply G b).symm⟩
  obtain ⟨j, h₁, h₂, rfl⟩ := exists_eq_comp_arrowPath G q hq
  have h₃ : G.Adj l m := (nonempty_hom_iff G).mp ⟨e⟩
  obtain rfl : e = arrow G h₃ := Subsingleton.elim _ _
  rw [← ofArrow_mul_ofArrow]
  rcases eq_or_ne i l with rfl | hil
  · have h₂_eq : arrow G h₂ = arrow G h₁.symm := Subsingleton.elim _ _
    rw [h₂_eq, ofArrow_symm_mul_ofArrow]
    exact ofArrow_mul_backtrackElem_mem k G hconn hcard h₁ h₃
  · exact (quadraticZigzagIdeal k G).mul_mem_left _ _
      (ofArrow_mul_ofArrow_mem_quadraticZigzagIdeal k G h₁ h₂ hil)

/-- Every path of length at least three lies in the quadratic ideal. -/
private theorem ofPath_mem_quadraticZigzagIdeal (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) {a b : DoubledQuiver G} (p : _root_.Quiver.Path a b)
    (hp : 3 ≤ p.length) :
    (ofPath ⟨a, b, p⟩ : pathAlgebra k (DoubledQuiver G)) ∈ quadraticZigzagIdeal k G := by
  induction p with
  | nil => simp at hp
  | cons q e ih =>
    rw [_root_.Quiver.Path.length_cons] at hp
    rw [← _root_.Quiver.Path.comp_toPath_eq_cons, ← ofPath_mul_ofPath_of_comp e.toPath q,
      ← ofArrow_eq_ofPath]
    rcases lt_or_ge q.length 3 with hlt | hge
    · exact ofArrow_mul_ofPath_mem k G hconn hcard q (by omega) e
    · exact (quadraticZigzagIdeal k G).mul_mem_left _ _ (ih hge)

/-- **The zigzag relations are quadratic.** For a connected graph with at least three vertices the
long-path generators are consequences of the two quadratic families, so the uniform and the purely
quadratic relation ideals agree.

The hypotheses are sharp for the roadmap's low-rank conventions. On the one-edge graph `A₂` the
doubled quiver has no length-two path with distinct endpoints and only one backtrack at each
vertex, so every quadratic relator is already zero and the quadratic ideal is `⊥`, while the
uniform ideal kills the length-three paths. -/
theorem zigzagIdeal_eq_quadraticZigzagIdeal (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) : zigzagIdeal k G = quadraticZigzagIdeal k G := by
  refine le_antisymm ?_ (quadraticZigzagIdeal_le_zigzagIdeal k G)
  rw [zigzagIdeal, TwoSidedIdeal.span_le]
  rintro x hx
  rw [SetLike.mem_coe]
  induction hx with
  | quadratic h => exact mem_quadraticZigzagIdeal_of_isQuadraticZigzagRelator k G h
  | long_path y hy =>
    obtain ⟨a, b, p⟩ := y
    exact ofPath_mem_quadraticZigzagIdeal k G hconn hcard p hy

/-! ### The relation quotient -/

/-- The zigzag relation quotient of a simple graph: the path algebra of the doubled quiver modulo
the uniform relation ideal.

This is the algebra of a *connected graph with an edge*: on a graph with an isolated vertex it is
not the intended zigzag algebra, whose singleton components carry the dual numbers instead. The
componentwise public definition is built from this quotient elsewhere. -/
noncomputable abbrev nonisolatedZigzagQuotient : Type _ :=
  pathAlgebra k (DoubledQuiver G) ⧸ (zigzagIdeal k G).asIdeal

/-- The quotient map from the path algebra of the doubled quiver onto the zigzag quotient. -/
noncomputable def zigzagMk :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] nonisolatedZigzagQuotient k G :=
  Ideal.Quotient.mkₐ k _

/-- The quotient map is the ring-theoretic quotient map of the relation ideal. -/
theorem zigzagMk_apply (x : pathAlgebra k (DoubledQuiver G)) :
    zigzagMk k G x = Ideal.Quotient.mk (zigzagIdeal k G).asIdeal x := (rfl)

/-- The kernel of the quotient map is the relation ideal. -/
@[simp]
theorem zigzagMk_eq_zero_iff {x : pathAlgebra k (DoubledQuiver G)} :
    zigzagMk k G x = 0 ↔ x ∈ zigzagIdeal k G := by
  rw [zigzagMk_apply, Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal]

/-- Every uniform relator dies in the zigzag quotient. -/
theorem zigzagMk_eq_zero_of_isZigzagRelator {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) : zigzagMk k G x = 0 :=
  (zigzagMk_eq_zero_iff k G).mpr (mem_zigzagIdeal_of_isZigzagRelator k G hx)

/-- A length-two path whose endpoints differ dies in the zigzag quotient. -/
@[simp]
theorem zigzagMk_ofPath_eq_zero_of_ne {i j : DoubledQuiver G} (p : _root_.Quiver.Path i j)
    (hp : p.length = 2) (hij : i ≠ j) : zigzagMk k G (ofPath ⟨i, j, p⟩) = 0 :=
  zigzagMk_eq_zero_of_isZigzagRelator k G
    (IsZigzagRelator.quadratic (IsQuadraticZigzagRelator.nonreturn p hp hij))

/-- A path of length at least three dies in the zigzag quotient. -/
@[simp]
theorem zigzagMk_ofPath_eq_zero_of_three_le (x : Quiver.TotalPath (DoubledQuiver G))
    (hx : 3 ≤ x.2.2.length) : zigzagMk k G (ofPath x) = 0 :=
  zigzagMk_eq_zero_of_isZigzagRelator k G (IsZigzagRelator.long_path x hx)

/-- The backtracks based at a vertex all have the same image in the zigzag quotient: this common
value is the volume element of the vertex. -/
theorem zigzagMk_backtrackElem_eq {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j') :
    zigzagMk k G (backtrackElem G k h) = zigzagMk k G (backtrackElem G k h') := by
  rw [← sub_eq_zero, ← map_sub]
  refine zigzagMk_eq_zero_of_isZigzagRelator k G (IsZigzagRelator.quadratic ?_)
  rw [backtrackElem_eq_ofPath, backtrackElem_eq_ofPath]
  exact IsQuadraticZigzagRelator.equal_backtracks _ _ (by simp) (by simp)

section Lift

variable {B : Type*} [Ring B] [Algebra k B]

/-- An algebra map killing every uniform relator kills the whole relation ideal. -/
theorem zigzagIdeal_le_ker (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsZigzagRelator k G x → f x = 0) : zigzagIdeal k G ≤ TwoSidedIdeal.ker f := by
  rw [zigzagIdeal, TwoSidedIdeal.span_le]
  exact fun x hx => (TwoSidedIdeal.mem_ker f).mpr (hf x hx)

/-- The universal property of the zigzag quotient: an algebra map out of the path algebra which
kills every uniform relator factors through the quotient. -/
noncomputable def zigzagLift (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsZigzagRelator k G x → f x = 0) : nonisolatedZigzagQuotient k G →ₐ[k] B :=
  Ideal.Quotient.liftₐ _ f fun _ ha =>
    (TwoSidedIdeal.mem_ker f).mp <| zigzagIdeal_le_ker k G f hf (TwoSidedIdeal.mem_asIdeal.mp ha)

@[simp]
theorem zigzagLift_zigzagMk (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsZigzagRelator k G x → f x = 0) (x : pathAlgebra k (DoubledQuiver G)) :
    zigzagLift k G f hf (zigzagMk k G x) = f x := by
  rw [zigzagMk_apply, zigzagLift, Ideal.Quotient.liftₐ_apply]
  exact Ideal.Quotient.lift_mk _ _ _

/-- The lift is the unique algebra map whose composite with the quotient map is `f`. -/
theorem zigzagLift_unique (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsZigzagRelator k G x → f x = 0)
    (g : nonisolatedZigzagQuotient k G →ₐ[k] B)
    (hg : ∀ x, g (zigzagMk k G x) = f x) : g = zigzagLift k G f hf := by
  apply Ideal.Quotient.algHom_ext k
  ext x
  exact (hg x).trans (zigzagLift_zigzagMk k G f hf x).symm

/-- On a connected graph with at least three vertices an algebra map killing the quadratic
relators already kills the whole relation ideal. -/
theorem zigzagIdeal_le_ker_of_quadratic (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsQuadraticZigzagRelator k G x → f x = 0) :
    zigzagIdeal k G ≤ TwoSidedIdeal.ker f := by
  rw [zigzagIdeal_eq_quadraticZigzagIdeal k G hconn hcard, quadraticZigzagIdeal,
    TwoSidedIdeal.span_le]
  exact fun x hx => (TwoSidedIdeal.mem_ker f).mpr (hf x hx)

/-- For a connected graph with at least three vertices only the quadratic relations need to be
checked: an algebra map killing them factors through the zigzag quotient. -/
noncomputable def zigzagLiftOfQuadratic (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsQuadraticZigzagRelator k G x → f x = 0) :
    nonisolatedZigzagQuotient k G →ₐ[k] B :=
  zigzagLift k G f fun _ hx =>
    (TwoSidedIdeal.mem_ker f).mp <|
      zigzagIdeal_le_ker_of_quadratic k G hconn hcard f hf
        (mem_zigzagIdeal_of_isZigzagRelator k G hx)

@[simp]
theorem zigzagLiftOfQuadratic_zigzagMk (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsQuadraticZigzagRelator k G x → f x = 0)
    (x : pathAlgebra k (DoubledQuiver G)) :
    zigzagLiftOfQuadratic k G hconn hcard f hf (zigzagMk k G x) = f x := by
  rw [zigzagLiftOfQuadratic, zigzagLift_zigzagMk]

/-- The quadratic lift is the unique algebra map whose composite with the quotient map is `f`. -/
theorem zigzagLiftOfQuadratic_unique (hconn : G.Connected)
    (hcard : 3 ≤ Nat.card V) (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsQuadraticZigzagRelator k G x → f x = 0)
    (g : nonisolatedZigzagQuotient k G →ₐ[k] B)
    (hg : ∀ x, g (zigzagMk k G x) = f x) :
    g = zigzagLiftOfQuadratic k G hconn hcard f hf := by
  apply Ideal.Quotient.algHom_ext k
  ext x
  exact (hg x).trans (zigzagLiftOfQuadratic_zigzagMk k G hconn hcard f hf x).symm

end Lift

end TauCeti
