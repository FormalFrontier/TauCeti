/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import TauCeti.LowDimTopology.Plumbing.NegativeDefinite

/-!
# Blowing up a plumbing graph at a vertex

This file adds the first of Neumann's plumbing moves: blowing up a plumbing graph at one of its
vertices. Given a plumbing graph `P` and a vertex `v`, the blow-up `P.blowUpVertex v` is the
plumbing graph on `Option V` obtained by adjoining a new vertex `none` with framing `-1`, joining
it to `some v`, and decreasing the framing of `some v` by one. Geometrically this blows up a point
on the sphere `v` inside the plumbed four-manifold, an operation that does not change the plumbed
three-manifold at the boundary; the corresponding blow-down is Neumann's move on a `-1`-framed
vertex, and the new vertex here indeed has framing `-1` and degree one.

The point of the file is the lattice-level content. The map

`blowUpVertexEquiv v : (V → ℤ) × ℤ ≃ₗ[ℤ] (Option V → ℤ)`,
`(x, s) ↦ fun a => a.elim (x v + s) x`,

sends the basis sphere `e_v` of the old lattice to the *proper transform* `e_v + e_none` and every
other basis sphere `e_w` to `e_w`, while `(0, 1)` is the exceptional class `e_none`. Under this
identification the blown-up intersection form becomes the orthogonal direct sum of the old
intersection form with the rank-one form `⟨-1⟩`:

`⟨(x, s), (y, t)⟩ = ⟨x, y⟩ - s * t`.

Everything else follows: the exceptional class has square `-1`, it is orthogonal to the image of
the old lattice, and the blow-up is negative definite exactly when `P` is. That last statement is
what makes the blow-up usable in Lane L: negative-definiteness is the standing hypothesis of
lattice homology, so a move that leaves it in place is a move along which the invariant can be
compared.

Nothing about lattice homology itself is proved here; the invariance of lattice homology under the
Neumann moves is a separate (later) target, and this file supplies the move together with the fact
that it preserves the hypothesis under which the invariant is defined.

## Main definitions

* `TauCeti.PlumbingGraph.BlowUpVertexAdj`: the adjacency relation of the blow-up.
* `TauCeti.PlumbingGraph.blowUpVertex`: the blow-up of a plumbing graph at a vertex.
* `TauCeti.PlumbingGraph.blowUpVertexEquiv`: the proper-transform identification of the blown-up
  lattice with `(V → ℤ) × ℤ`.

## Main results

* `TauCeti.PlumbingGraph.blowUpVertex_degree_none`: the new vertex has degree one, so together
  with its framing `-1` it is a blow-down candidate in Neumann's calculus.
* `TauCeti.PlumbingGraph.intersectionForm_blowUpVertexEquiv`: the blown-up intersection form is
  the orthogonal direct sum of the original one with `⟨-1⟩`.
* `TauCeti.PlumbingGraph.intersectionForm_single_none_self` and
  `TauCeti.PlumbingGraph.intersectionForm_blowUpVertexEquiv_single_none`: the exceptional class has
  square `-1` and is orthogonal to the image of the original lattice.
* `TauCeti.PlumbingGraph.blowUpVertex_isNegativeDefinite_iff`: the blow-up is negative definite
  exactly when the original plumbing is.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
whose programme is "Plumbing trees/graphs and their lattices; Némethi's lattice (co)homology …;
invariance under **Neumann moves**": the move itself and its compatibility with the
negative-definiteness hypothesis are the prerequisites for stating that invariance. The plumbing
calculus is W. Neumann, *A calculus for plumbing applied to the topology of complex surface
singularities and degenerating complex curves*, Trans. Amer. Math. Soc. **268** (1981), 299--344;
the lattice conventions follow Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

@[expose] public section

open Matrix

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*}

/-- The proper-transform identification of the blown-up plumbing lattice.

A pair `(x, s)` consisting of a lattice point `x` of the original plumbing and a multiple `s` of
the exceptional class is sent to the lattice point of the blow-up whose coordinate at the new
vertex `none` is `x v + s` and whose coordinate at an old vertex `some w` is `x w`. On basis
vectors this is `e_v ↦ e_v + e_none` (the proper transform of the blown-up sphere), `e_w ↦ e_w`
for `w ≠ v`, and `(0, 1) ↦ e_none`; see `blowUpVertexEquiv_zero_one`.

The map depends only on the blown-up vertex, not on the framings or the edges. -/
def blowUpVertexEquiv (v : V) : ((V → ℤ) × ℤ) ≃ₗ[ℤ] (Option V → ℤ) where
  toFun p a := a.elim (p.1 v + p.2) p.1
  map_add' p q := by
    funext a
    cases a with
    | none =>
        change (p.1 + q.1) v + (p.2 + q.2) = p.1 v + p.2 + (q.1 v + q.2)
        simp only [Pi.add_apply]
        ring
    | some w => rfl
  map_smul' c p := by
    funext a
    cases a with
    | none =>
        change (c • p.1) v + c • p.2 = c • (p.1 v + p.2)
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    | some w => rfl
  invFun y := (fun w => y (some w), y none - y (some v))
  left_inv p := by
    rw [Prod.ext_iff]
    refine ⟨funext fun w => rfl, ?_⟩
    change p.1 v + p.2 - p.1 v = p.2
    ring
  right_inv y := by
    funext a
    cases a with
    | none =>
        change y (some v) + (y none - y (some v)) = y none
        ring
    | some w => rfl

/-- The coordinate of a lifted lattice point at the new vertex. -/
@[simp]
theorem blowUpVertexEquiv_apply_none (v : V) (x : V → ℤ) (s : ℤ) :
    blowUpVertexEquiv v (x, s) none = x v + s :=
  rfl

/-- The coordinate of a lifted lattice point at an old vertex. -/
@[simp]
theorem blowUpVertexEquiv_apply_some (v : V) (x : V → ℤ) (s : ℤ) (w : V) :
    blowUpVertexEquiv v (x, s) (some w) = x w :=
  rfl

/-- The inverse identification reads off the old coordinates and the exceptional multiplicity. -/
@[simp]
theorem blowUpVertexEquiv_symm_apply (v : V) (y : Option V → ℤ) :
    (blowUpVertexEquiv v).symm y = (fun w => y (some w), y none - y (some v)) :=
  rfl

/-- The pair `(0, 1)` is the exceptional class, the basis vector at the new vertex. -/
theorem blowUpVertexEquiv_zero_one [DecidableEq V] (v : V) :
    blowUpVertexEquiv v (0, 1) = Pi.single (none : Option V) (1 : ℤ) := by
  funext a
  cases a with
  | none => simp
  | some w => simp

/-- The adjacency relation of the blow-up of a plumbing graph at a vertex: the new vertex `none`
is joined exactly to `some v`, and the old vertices keep their adjacencies. -/
def BlowUpVertexAdj (P : PlumbingGraph V) (v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some w => w = v
  | some w, none => w = v
  | some w, some w' => P.toSimpleGraph.Adj w w'

instance decidableBlowUpVertexAdj [DecidableEq V] (P : PlumbingGraph V) (v : V) :
    DecidableRel (P.BlowUpVertexAdj v)
  | none, none => inferInstanceAs (Decidable False)
  | none, some w => inferInstanceAs (Decidable (w = v))
  | some w, none => inferInstanceAs (Decidable (w = v))
  | some w, some w' => inferInstanceAs (Decidable (P.toSimpleGraph.Adj w w'))

/-- The blow-up adjacency relation is symmetric. -/
theorem blowUpVertexAdj_symm (P : PlumbingGraph V) (v : V) :
    Std.Symm (P.BlowUpVertexAdj v) :=
  ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact (h : P.toSimpleGraph.Adj a b).symm⟩

/-- The blow-up adjacency relation is irreflexive. -/
theorem blowUpVertexAdj_irrefl (P : PlumbingGraph V) (v : V) :
    Std.Irrefl (P.BlowUpVertexAdj v) :=
  ⟨by
    rintro (_ | a) h
    · exact h
    · exact P.toSimpleGraph.irrefl (h : P.toSimpleGraph.Adj a a)⟩

/-- The blow-up of a plumbing graph at a vertex `v`: adjoin a new vertex `none` with framing `-1`,
join it to `some v`, and drop the framing of `some v` by one.

This is the plumbing move corresponding to blowing up a point on the sphere `v`; the plumbed
three-manifold at the boundary is unchanged, while the plumbed four-manifold gains a `-1`-sphere.
-/
def blowUpVertex [DecidableEq V] (P : PlumbingGraph V) (v : V) : PlumbingGraph (Option V) where
  toSimpleGraph :=
    { Adj := P.BlowUpVertexAdj v
      symm := P.blowUpVertexAdj_symm v
      loopless := P.blowUpVertexAdj_irrefl v }
  decidableAdj := P.decidableBlowUpVertexAdj v
  weight a := a.elim (-1) fun w => if w = v then P.weight w - 1 else P.weight w

variable [DecidableEq V] (P : PlumbingGraph V) (v : V)

/-- The new vertex carries no loop. -/
@[simp]
theorem blowUpVertex_adj_none_none : ¬ (P.blowUpVertex v).toSimpleGraph.Adj none none :=
  not_false

/-- The new vertex is joined exactly to the blown-up vertex. -/
@[simp]
theorem blowUpVertex_adj_none_some (w : V) :
    (P.blowUpVertex v).toSimpleGraph.Adj none (some w) ↔ w = v :=
  Iff.rfl

/-- The new vertex is joined exactly to the blown-up vertex. -/
@[simp]
theorem blowUpVertex_adj_some_none (w : V) :
    (P.blowUpVertex v).toSimpleGraph.Adj (some w) none ↔ w = v :=
  Iff.rfl

/-- The blow-up keeps all adjacencies between old vertices. -/
@[simp]
theorem blowUpVertex_adj_some_some (w w' : V) :
    (P.blowUpVertex v).toSimpleGraph.Adj (some w) (some w') ↔ P.toSimpleGraph.Adj w w' :=
  Iff.rfl

/-- The new vertex is `-1`-framed. -/
@[simp]
theorem blowUpVertex_weight_none : (P.blowUpVertex v).weight none = -1 :=
  rfl

/-- The framings of the old vertices, with the blown-up one dropped by a unit. -/
@[simp]
theorem blowUpVertex_weight_some (w : V) :
    (P.blowUpVertex v).weight (some w) = if w = v then P.weight w - 1 else P.weight w :=
  rfl

/-- Blowing up drops the framing of the blown-up vertex by a unit. -/
theorem blowUpVertex_weight_some_self :
    (P.blowUpVertex v).weight (some v) = P.weight v - 1 := by
  simp

/-- Blowing up leaves the framings of the other vertices alone. -/
theorem blowUpVertex_weight_some_of_ne {w : V} (h : w ≠ v) :
    (P.blowUpVertex v).weight (some w) = P.weight w := by
  simp [h]

/-- The new vertex has exactly one neighbour, the blown-up vertex. -/
theorem blowUpVertex_neighborSet_none :
    (P.blowUpVertex v).toSimpleGraph.neighborSet none = {some v} := by
  ext a
  cases a with
  | none => simp
  | some w => simp

/-- The new vertex has degree one. Together with its framing `-1` this is exactly the local
configuration that Neumann's blow-down move removes. -/
theorem blowUpVertex_degree_none [Fintype V] :
    (P.blowUpVertex v).toSimpleGraph.degree none = 1 := by
  have h : (P.blowUpVertex v).toSimpleGraph.neighborFinset none = {some v} := by
    ext a
    cases a with
    | none => simp
    | some w => simp
  rw [SimpleGraph.degree, h, Finset.card_singleton]

/-- The exceptional sphere has self-intersection `-1`. -/
@[simp]
theorem blowUpVertex_intersectionMatrix_none_none :
    (P.blowUpVertex v).intersectionMatrix none none = -1 := by
  rw [intersectionMatrix_diag, blowUpVertex_weight_none]

/-- The exceptional sphere meets the proper transform once and the other spheres not at all. -/
@[simp]
theorem blowUpVertex_intersectionMatrix_none_some (w : V) :
    (P.blowUpVertex v).intersectionMatrix none (some w) = if w = v then 1 else 0 := by
  rw [(P.blowUpVertex v).intersectionMatrix_apply_of_ne (by simp : (none : Option V) ≠ some w)]
  simp

/-- The exceptional sphere meets the proper transform once and the other spheres not at all. -/
@[simp]
theorem blowUpVertex_intersectionMatrix_some_none (w : V) :
    (P.blowUpVertex v).intersectionMatrix (some w) none = if w = v then 1 else 0 := by
  rw [(P.blowUpVertex v).intersectionMatrix_apply_of_ne (by simp : (some w : Option V) ≠ none)]
  simp

/-- Between old vertices the intersection matrix changes only in the diagonal entry of the
blown-up vertex, which drops by a unit. -/
theorem blowUpVertex_intersectionMatrix_some_some (w w' : V) :
    (P.blowUpVertex v).intersectionMatrix (some w) (some w') =
      P.intersectionMatrix w w' -
        (if w = v then (1 : ℤ) else 0) * (if w' = v then (1 : ℤ) else 0) := by
  rcases eq_or_ne w w' with rfl | hne
  · rw [intersectionMatrix_diag, intersectionMatrix_diag, blowUpVertex_weight_some]
    by_cases h : w = v <;> simp [h]
  · have hzero : (if w = v then (1 : ℤ) else 0) * (if w' = v then (1 : ℤ) else 0) = 0 := by
      by_cases h1 : w = v
      · by_cases h2 : w' = v
        · exact absurd (h1.trans h2.symm) hne
        · simp [h2]
      · simp [h1]
    rw [(P.blowUpVertex v).intersectionMatrix_apply_of_ne (by simpa using hne),
      P.intersectionMatrix_apply_of_ne hne, hzero, sub_zero]
    simp only [blowUpVertex_adj_some_some]

section Lattice

variable [Fintype V]

/-- The coordinate of an indicator-weighted sum at the marked index. -/
private theorem sum_ite_one_mul (y : V → ℤ) (v : V) :
    ∑ w : V, (if w = v then (1 : ℤ) else 0) * y w = y v := by
  have hterm : ∀ w : V, (if w = v then (1 : ℤ) else 0) * y w = if w = v then y w else 0 := by
    intro w
    split_ifs <;> simp
  simp only [hterm]
  simp

/-- The `none`-coordinate of the image of a lifted lattice point under the blown-up intersection
matrix: the exceptional class is orthogonal to the proper transforms, so only the exceptional
multiplicity survives. -/
private theorem blowUpVertex_mulVec_apply_none (y : V → ℤ) (t : ℤ) :
    ((P.blowUpVertex v).intersectionMatrix *ᵥ blowUpVertexEquiv v (y, t)) none = -t := by
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_option]
  simp only [blowUpVertex_intersectionMatrix_none_none, blowUpVertex_intersectionMatrix_none_some,
    blowUpVertexEquiv_apply_none, blowUpVertexEquiv_apply_some]
  rw [sum_ite_one_mul y v]
  ring

/-- The `some`-coordinates of the image of a lifted lattice point under the blown-up intersection
matrix. -/
private theorem blowUpVertex_mulVec_apply_some (y : V → ℤ) (t : ℤ) (w : V) :
    ((P.blowUpVertex v).intersectionMatrix *ᵥ blowUpVertexEquiv v (y, t)) (some w) =
      (P.intersectionMatrix *ᵥ y) w + (if w = v then t else 0) := by
  have hsplit : ∀ w' : V,
      (P.intersectionMatrix w w' -
          (if w = v then (1 : ℤ) else 0) * (if w' = v then (1 : ℤ) else 0)) * y w' =
        P.intersectionMatrix w w' * y w' -
          (if w = v then (1 : ℤ) else 0) * ((if w' = v then (1 : ℤ) else 0) * y w') := by
    intro w'
    ring
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_option]
  simp only [blowUpVertex_intersectionMatrix_some_none, blowUpVertex_intersectionMatrix_some_some,
    blowUpVertexEquiv_apply_none, blowUpVertexEquiv_apply_some, hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ite_one_mul y v,
    Matrix.mulVec_apply_eq_sum]
  by_cases h : w = v
  · simp [h]
    ring
  · simp [h]

/-- **The blow-up splits the intersection form.** Under the proper-transform identification
`blowUpVertexEquiv`, the intersection form of the blow-up is the orthogonal direct sum of the
intersection form of `P` with the rank-one form `⟨-1⟩` spanned by the exceptional class. -/
theorem intersectionForm_blowUpVertexEquiv (x y : V → ℤ) (s t : ℤ) :
    (P.blowUpVertex v).intersectionForm (blowUpVertexEquiv v (x, s))
        (blowUpVertexEquiv v (y, t)) =
      P.intersectionForm x y - s * t := by
  have hdotOpt : ∀ u z : Option V → ℤ, u ⬝ᵥ z = ∑ a, u a * z a := fun _ _ => rfl
  have hdotV : ∀ u z : V → ℤ, u ⬝ᵥ z = ∑ a, u a * z a := fun _ _ => rfl
  have hterm : ∀ w : V,
      x w * ((P.intersectionMatrix *ᵥ y) w + (if w = v then t else 0)) =
        x w * (P.intersectionMatrix *ᵥ y) w + (if w = v then x w * t else 0) := by
    intro w
    split_ifs <;> ring
  rw [(P.blowUpVertex v).intersectionForm_apply,
    ← Matrix.toBilin'_apply (P.blowUpVertex v).intersectionMatrix, Matrix.toBilin'_apply',
    P.intersectionForm_apply, ← Matrix.toBilin'_apply P.intersectionMatrix x y,
    Matrix.toBilin'_apply', hdotOpt, hdotV, Fintype.sum_option]
  simp only [blowUpVertexEquiv_apply_none, blowUpVertexEquiv_apply_some,
    P.blowUpVertex_mulVec_apply_none v y t, P.blowUpVertex_mulVec_apply_some v y t, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v fun w => x w * t]
  simp only [Finset.mem_univ, if_true]
  ring

/-- The exceptional class has self-intersection `-1`. -/
theorem intersectionForm_single_none_self :
    (P.blowUpVertex v).intersectionForm (Pi.single (none : Option V) (1 : ℤ))
        (Pi.single (none : Option V) (1 : ℤ)) = -1 := by
  rw [(P.blowUpVertex v).intersectionForm_single, blowUpVertex_intersectionMatrix_none_none]

/-- The exceptional class is orthogonal to every proper transform, so the splitting of
`intersectionForm_blowUpVertexEquiv` really is orthogonal. -/
theorem intersectionForm_blowUpVertexEquiv_single_none (x : V → ℤ) :
    (P.blowUpVertex v).intersectionForm (blowUpVertexEquiv v (x, 0))
        (Pi.single (none : Option V) (1 : ℤ)) = 0 := by
  rw [← blowUpVertexEquiv_zero_one v, P.intersectionForm_blowUpVertexEquiv v x 0 0 1]
  simp

end Lattice

/-- **Blowing up at a vertex preserves and reflects negative-definiteness.** The blown-up
intersection form is the old one plus a `⟨-1⟩` summand, so it is negative definite exactly when
the old one is. Since negative-definiteness is the standing hypothesis of lattice homology, the
blow-up move stays inside the class of plumbings the theory applies to. -/
theorem blowUpVertex_isNegativeDefinite_iff [Finite V] :
    (P.blowUpVertex v).IsNegativeDefinite ↔ P.IsNegativeDefinite := by
  obtain ⟨_⟩ := nonempty_fintype V
  rw [isNegativeDefinite_iff_forall_intersectionForm_self_neg,
    isNegativeDefinite_iff_forall_intersectionForm_self_neg]
  constructor
  · intro h x hx
    have hne : blowUpVertexEquiv v (x, (0 : ℤ)) ≠ 0 := by
      intro hzero
      refine hx (funext fun w => ?_)
      simpa using congrFun hzero (some w)
    have hlt := h _ hne
    rw [P.intersectionForm_blowUpVertexEquiv v x x 0 0] at hlt
    simpa using hlt
  · intro h y hy
    obtain ⟨⟨x, s⟩, rfl⟩ : ∃ p, blowUpVertexEquiv v p = y :=
      ⟨(blowUpVertexEquiv v).symm y, (blowUpVertexEquiv v).apply_symm_apply y⟩
    rw [P.intersectionForm_blowUpVertexEquiv v x x s s]
    rcases eq_or_ne x 0 with rfl | hx0
    · have hs : s ≠ 0 := fun hs0 => hy (by simp [hs0])
      have h0 : P.intersectionForm 0 0 = 0 := by simp
      rw [h0]
      linarith [mul_self_pos.mpr hs]
    · linarith [h x hx0, mul_self_nonneg s]

end PlumbingGraph

end TauCeti
