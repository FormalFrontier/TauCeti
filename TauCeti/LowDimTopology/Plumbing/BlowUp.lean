/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import TauCeti.LowDimTopology.Plumbing.Characteristic
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

sends the basis sphere `e_v` of the old lattice to the *total transform* (pullback) `e_v + e_none`
and every other basis sphere `e_w` to `e_w`, while `(0, 1)` is the exceptional class `e_none`.
Beware the standard distinction: it is the basis vector `e_v = Pi.single (some v) 1` of the
*blown-up* lattice, of square `P.weight v - 1` and meeting `e_none` once, that is the *proper
transform* of the sphere `v`; the total transform is the sum of that proper transform and the
exceptional class, it is the image `blowUpVertexEquiv v (e_v, 0)` of the old basis sphere, and it
keeps the old square `P.weight v` and is orthogonal to `e_none`. Under this identification the
blown-up intersection form becomes the orthogonal direct sum of the old intersection form with the
rank-one form `⟨-1⟩`:

`⟨(x, s), (y, t)⟩ = ⟨x, y⟩ - s * t`.

Everything else follows: the exceptional class has square `-1`, it is orthogonal to the image of
the old lattice, and the blow-up is negative definite exactly when `P` is. That last statement is
what makes the blow-up usable in Lane L: negative-definiteness is the standing hypothesis of
lattice homology, so a move that leaves it in place is a move along which the invariant can be
compared.

The covector side of the same splitting is `blowUpCovectorEquiv`, the identification dual to
`blowUpVertexEquiv`: a covector `k` of `P` together with a value `ε` on the exceptional class
becomes the covector of the blow-up whose pairing against a total transform is

`⟨k', φ(x, s)⟩ = ⟨k, x⟩ + ε * s`.

It is characteristic for the blow-up exactly when `k` is characteristic for `P` and `ε` is odd,
and every characteristic covector of the blow-up arises this way, so `blowUpCharacteristic`
parametrizes them completely; the canonical characteristic covector of the blow-up is the
canonical one of `P` carrying `-1`, the adjunction value of the exceptional class.

Nothing about lattice homology itself is proved here; the invariance of lattice homology under the
Neumann moves is a separate (later) target, and this file supplies the move together with the fact
that it preserves the hypothesis under which the invariant is defined.

## Main definitions

* `TauCeti.PlumbingGraph.blowUpVertex`: the blow-up of a plumbing graph at a vertex.
* `TauCeti.PlumbingGraph.blowUpVertexEquiv`: the total-transform identification of the blown-up
  lattice with `(V → ℤ) × ℤ`.
* `TauCeti.PlumbingGraph.blowUpCovectorEquiv`: the total-transform identification of the covectors
  of the blow-up with pairs `(k, ε)`, dual to `blowUpVertexEquiv`.
* `TauCeti.PlumbingGraph.blowUpCharacteristic`: the characteristic covector of the blow-up
  determined by a characteristic covector of `P` and an odd value on the exceptional class.

## Main results

* `TauCeti.PlumbingGraph.blowUpVertex_degree_none`: the new vertex has degree one, so together
  with its framing `-1` it is a blow-down candidate in Neumann's calculus.
* `TauCeti.PlumbingGraph.intersectionForm_blowUpVertexEquiv`: the blown-up intersection form is
  the orthogonal direct sum of the original one with `⟨-1⟩`.
* `TauCeti.PlumbingGraph.sum_blowUpCovectorEquiv_mul_blowUpVertexEquiv`: the two total-transform
  identifications are dual to one another.
* `TauCeti.PlumbingGraph.isCharacteristicVector_blowUpCovectorEquiv_iff` and
  `TauCeti.PlumbingGraph.exists_blowUpCovectorEquiv_eq`: the characteristic covectors of the
  blow-up are exactly the pairs of a characteristic covector of `P` with an odd exceptional value.
* `TauCeti.PlumbingGraph.blowUpCovectorEquiv_canonicalCharacteristic`: the canonical characteristic
  covector of the blow-up is the canonical one of `P` with exceptional value `-1`.
* `TauCeti.PlumbingGraph.intersectionForm_single_none_self` and
  `TauCeti.PlumbingGraph.intersectionForm_blowUpVertexEquiv_single_none`: the exceptional class has
  square `-1` and is orthogonal to the image of the original lattice.
* `TauCeti.PlumbingGraph.isNegativeDefinite_blowUpVertex_iff`: the blow-up is negative definite
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

public section

open Matrix

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*}

/-! ### Implementation notes

The bodies of `blowUpVertexEquiv` and `blowUpVertex` stay unexposed, and the raw adjacency
relation behind the blow-up is `private`: consumers work through the coordinate, adjacency and
weight lemmas rather than through the definitions. Those defining equations are proved by a
parenthesised `(rfl)`, which keeps them ordinary propositional lemmas instead of implicitly
`@[defeq]` ones; an exported `@[defeq]` theorem would have to expose every definition it unfolds.
-/

/-- The total-transform identification of the blown-up plumbing lattice.

A pair `(x, s)` consisting of a lattice point `x` of the original plumbing and a multiple `s` of
the exceptional class is sent to the lattice point of the blow-up whose coordinate at the new
vertex `none` is `x v + s` and whose coordinate at an old vertex `some w` is `x w`. On basis
vectors this is `e_v ↦ e_v + e_none` (the total transform, or pullback, of the blown-up sphere),
`e_w ↦ e_w` for `w ≠ v`, and `(0, 1) ↦ e_none`; see `blowUpVertexEquiv_zero_one`. The proper
transform of the blown-up sphere is instead the basis vector `Pi.single (some v) 1`, the image of
`(e_v, -1)`; unlike the total transform it meets the exceptional class once.

The map depends only on the blown-up vertex, not on the framings or the edges. -/
def blowUpVertexEquiv (v : V) : ((V → ℤ) × ℤ) ≃ₗ[ℤ] (Option V → ℤ) where
  toFun p a := a.elim (p.1 v + p.2) p.1
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
  invFun y := (fun w => y (some w), y none - y (some v))
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
theorem blowUpVertexEquiv_apply_none (v : V) (x : V → ℤ) (s : ℤ) :
    blowUpVertexEquiv v (x, s) none = x v + s :=
  (rfl)

/-- The coordinate of a lifted lattice point at an old vertex. -/
@[simp]
theorem blowUpVertexEquiv_apply_some (v : V) (x : V → ℤ) (s : ℤ) (w : V) :
    blowUpVertexEquiv v (x, s) (some w) = x w :=
  (rfl)

/-- The inverse identification reads off the old coordinates and the exceptional multiplicity. -/
@[simp]
theorem blowUpVertexEquiv_symm_apply (v : V) (y : Option V → ℤ) :
    (blowUpVertexEquiv v).symm y = (fun w => y (some w), y none - y (some v)) :=
  (rfl)

/-- The pair `(0, 1)` is the exceptional class, the basis vector at the new vertex. -/
theorem blowUpVertexEquiv_zero_one [DecidableEq V] (v : V) :
    blowUpVertexEquiv v (0, 1) = Pi.single (none : Option V) (1 : ℤ) := by
  funext a
  cases a with
  | none => simp
  | some w => simp

/-- The adjacency relation of the blow-up of a plumbing graph at a vertex: the new vertex `none`
is joined exactly to `some v`, and the old vertices keep their adjacencies.

This is internal to the construction of `blowUpVertex`; consumers use the adjacency lemmas
`blowUpVertex_adj_none_some`, `blowUpVertex_adj_some_none` and `blowUpVertex_adj_some_some`. -/
private def BlowUpVertexAdj (P : PlumbingGraph V) (v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some w => w = v
  | some w, none => w = v
  | some w, some w' => P.toSimpleGraph.Adj w w'

private instance decidableBlowUpVertexAdj [DecidableEq V] (P : PlumbingGraph V) (v : V) :
    DecidableRel (P.BlowUpVertexAdj v)
  | none, none => inferInstanceAs (Decidable False)
  | none, some w => inferInstanceAs (Decidable (w = v))
  | some w, none => inferInstanceAs (Decidable (w = v))
  | some w, some w' => inferInstanceAs (Decidable (P.toSimpleGraph.Adj w w'))

/-- The blow-up adjacency relation is symmetric. -/
private theorem blowUpVertexAdj_symm (P : PlumbingGraph V) (v : V) :
    Std.Symm (P.BlowUpVertexAdj v) :=
  ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact (h : P.toSimpleGraph.Adj a b).symm⟩

/-- The blow-up adjacency relation is irreflexive. -/
private theorem blowUpVertexAdj_irrefl (P : PlumbingGraph V) (v : V) :
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
  (rfl)

/-- The framings of the old vertices, with the blown-up one dropped by a unit. -/
@[simp]
theorem blowUpVertex_weight_some (w : V) :
    (P.blowUpVertex v).weight (some w) = if w = v then P.weight w - 1 else P.weight w :=
  (rfl)

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

/-- The exceptional sphere has self-intersection `-1`. This is not a `simp` lemma: the simp set
already rewrites the left-hand side through `intersectionMatrix_diag` and
`blowUpVertex_weight_none`. -/
theorem blowUpVertex_intersectionMatrix_none_none :
    (P.blowUpVertex v).intersectionMatrix none none = -1 := by
  rw [intersectionMatrix_diag, blowUpVertex_weight_none]

/-- The exceptional sphere meets the proper transform `Pi.single (some v) 1` once and the other
spheres not at all. -/
@[simp]
theorem blowUpVertex_intersectionMatrix_none_some (w : V) :
    (P.blowUpVertex v).intersectionMatrix none (some w) = if w = v then 1 else 0 := by
  rw [(P.blowUpVertex v).intersectionMatrix_apply_of_ne (by simp : (none : Option V) ≠ some w)]
  simp

/-- The exceptional sphere meets the proper transform `Pi.single (some v) 1` once and the other
spheres not at all. -/
@[simp]
theorem blowUpVertex_intersectionMatrix_some_none (w : V) :
    (P.blowUpVertex v).intersectionMatrix (some w) none = if w = v then 1 else 0 := by
  rw [(P.blowUpVertex v).intersectionMatrix_apply_of_ne (by simp : (some w : Option V) ≠ none)]
  simp

/-- Between old vertices the intersection matrix changes only in the diagonal entry of the
blown-up vertex, which drops by a unit. -/
@[simp]
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

/-! ### The covectors of a blow-up

The lattice of the blow-up is identified with `(V → ℤ) × ℤ` by the total transform
`blowUpVertexEquiv`. This section records the dual identification of its covectors, and the
resulting parametrization of the characteristic covectors of a blow-up.
-/

/-- The total-transform identification of the covectors of the blow-up.

A pair `(k, ε)` consisting of a covector `k` of the original plumbing lattice and the value `ε`
on the exceptional class is sent to the covector of the blow-up taking the value `ε` at the new
vertex `none` and `k w - [w = v] ε` at an old vertex `some w`. This is the identification dual to
`blowUpVertexEquiv`: `sum_blowUpCovectorEquiv_mul_blowUpVertexEquiv` says the pairing of
`blowUpCovectorEquiv v (k, ε)` against the total transform of `(x, s)` is `⟨k, x⟩ + ε * s`, so
`k` is the restriction of the covector to the image of the old lattice and `ε` is its value on
the exceptional class.

Beware that the old coordinates are *not* simply retained: the value at `some v` is corrected by
`ε`, because the basis vector `Pi.single (some v) 1` of the blow-up is the proper transform of the
sphere `v`, not its total transform. -/
def blowUpCovectorEquiv (v : V) : ((V → ℤ) × ℤ) ≃ₗ[ℤ] (Option V → ℤ) where
  toFun p a := a.elim p.2 fun w => p.1 w - if w = v then p.2 else 0
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
  invFun k := (fun w => k (some w) + (if w = v then k none else 0), k none)
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
theorem blowUpCovectorEquiv_apply_none (k : V → ℤ) (ε : ℤ) :
    blowUpCovectorEquiv v (k, ε) none = ε :=
  (rfl)

/-- The value of a lifted covector at an old vertex, corrected at the blown-up vertex. -/
@[simp]
theorem blowUpCovectorEquiv_apply_some (k : V → ℤ) (ε : ℤ) (w : V) :
    blowUpCovectorEquiv v (k, ε) (some w) = k w - if w = v then ε else 0 :=
  (rfl)

/-- At the blown-up vertex the lifted covector is corrected by the exceptional value. -/
theorem blowUpCovectorEquiv_apply_some_self (k : V → ℤ) (ε : ℤ) :
    blowUpCovectorEquiv v (k, ε) (some v) = k v - ε := by
  simp

/-- Away from the blown-up vertex the lifted covector keeps its old values. -/
theorem blowUpCovectorEquiv_apply_some_of_ne (k : V → ℤ) (ε : ℤ) {w : V} (h : w ≠ v) :
    blowUpCovectorEquiv v (k, ε) (some w) = k w := by
  simp [h]

/-- The inverse identification reads off the value on the exceptional class and undoes the
correction at the blown-up vertex. -/
@[simp]
theorem blowUpCovectorEquiv_symm_apply (k : Option V → ℤ) :
    (blowUpCovectorEquiv v).symm k =
      (fun w => k (some w) + (if w = v then k none else 0), k none) :=
  (rfl)

/-- The canonical characteristic covector of the blow-up is the canonical characteristic covector
of `P` carrying the value `-1` on the exceptional class.

This is the adjunction formula for a blow-up: the exceptional sphere has square `-1`, so
`K(E) + E · E = -2` forces `K(E) = -1`. -/
theorem blowUpCovectorEquiv_canonicalCharacteristic :
    blowUpCovectorEquiv v (P.canonicalCharacteristic, -1) =
      (P.blowUpVertex v).canonicalCharacteristic := by
  funext a
  cases a with
  | none => simp
  | some w =>
      simp only [blowUpCovectorEquiv_apply_some, canonicalCharacteristic_apply,
        blowUpVertex_weight_some]
      split_ifs <;> ring

/-- A lifted covector is characteristic for the blow-up exactly when the covector it lifts is
characteristic for `P` and its value on the exceptional class is odd.

Oddness is the parity condition at the new `-1`-framed vertex; at an old vertex the correction
`[w = v] ε` and the framing drop `[w = v]` cancel modulo two precisely because `ε` is odd. -/
@[simp]
theorem isCharacteristicVector_blowUpCovectorEquiv_iff (k : V → ℤ) (ε : ℤ) :
    (P.blowUpVertex v).IsCharacteristicVector (blowUpCovectorEquiv v (k, ε)) ↔
      P.IsCharacteristicVector k ∧ Odd ε := by
  simp only [isCharacteristicVector_iff, Int.ModEq, Int.odd_iff]
  constructor
  · intro h
    have hnone := h none
    rw [blowUpCovectorEquiv_apply_none, blowUpVertex_weight_none] at hnone
    refine ⟨fun w => ?_, by omega⟩
    have hw := h (some w)
    rcases eq_or_ne w v with rfl | hwv
    · rw [blowUpCovectorEquiv_apply_some_self, blowUpVertex_weight_some_self] at hw
      omega
    · rw [blowUpCovectorEquiv_apply_some_of_ne (h := hwv),
        blowUpVertex_weight_some_of_ne (h := hwv)] at hw
      omega
  · rintro ⟨hk, hε⟩ a
    cases a with
    | none => rw [blowUpCovectorEquiv_apply_none, blowUpVertex_weight_none]; omega
    | some w =>
        have hw := hk w
        rcases eq_or_ne w v with rfl | hwv
        · rw [blowUpCovectorEquiv_apply_some_self, blowUpVertex_weight_some_self]
          omega
        · rw [blowUpCovectorEquiv_apply_some_of_ne (h := hwv),
            blowUpVertex_weight_some_of_ne (h := hwv)]
          omega

/-- Every characteristic covector of a blow-up is the lift of a characteristic covector of `P`
carrying an odd value on the exceptional class. Together with
`isCharacteristicVector_blowUpCovectorEquiv_iff` this parametrizes the characteristic covectors of
a blow-up completely. -/
theorem exists_blowUpCovectorEquiv_eq (k : (P.blowUpVertex v).characteristicVectors) :
    ∃ (l : P.characteristicVectors) (ε : ℤ), Odd ε ∧
      blowUpCovectorEquiv v (l.val, ε) = k.val := by
  obtain ⟨p, hp⟩ := (blowUpCovectorEquiv v).surjective k.val
  obtain ⟨hl, hε⟩ :=
    (P.isCharacteristicVector_blowUpCovectorEquiv_iff v p.1 p.2).mp (hp ▸ k.property)
  exact ⟨⟨p.1, hl⟩, p.2, hε, hp⟩

/-- The characteristic covector of the blow-up of `P` at `v` determined by a characteristic
covector `k` of `P` and an odd value `ε` on the exceptional class.

Every odd exceptional value gives a characteristic covector; the canonical characteristic covector
of a blow-up is the case `ε = -1` of `k` canonical, by
`blowUpCharacteristic_canonicalCharacteristic`. Only the unit values `ε = ±1` make the extra term
by which the blow-up changes the weight function nonnegative at every exceptional multiplicity;
see `characteristicWeight_le_blowUpCharacteristic` in `Weight/BlowUp.lean`. -/
def blowUpCharacteristic (k : P.characteristicVectors) (ε : ℤ) (hε : Odd ε) :
    (P.blowUpVertex v).characteristicVectors :=
  ⟨blowUpCovectorEquiv v (k.val, ε),
    (P.isCharacteristicVector_blowUpCovectorEquiv_iff v k.val ε).mpr ⟨k.property, hε⟩⟩

/-- The underlying covector of `blowUpCharacteristic` is the lift of the underlying covector. -/
@[simp]
theorem blowUpCharacteristic_val (k : P.characteristicVectors) (ε : ℤ) (hε : Odd ε) :
    (P.blowUpCharacteristic v k ε hε).val = blowUpCovectorEquiv v (k.val, ε) :=
  (rfl)

/-- The canonical characteristic covector of a blow-up is the canonical characteristic covector of
`P` with the unit `-1` on the exceptional class. -/
theorem blowUpCharacteristic_canonicalCharacteristic :
    P.blowUpCharacteristic v
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ (-1)
          (by norm_num) =
      ⟨(P.blowUpVertex v).canonicalCharacteristic,
        (P.blowUpVertex v).isCharacteristicVector_canonicalCharacteristic⟩ := by
  refine Subtype.ext ?_
  rw [blowUpCharacteristic_val]
  simpa using P.blowUpCovectorEquiv_canonicalCharacteristic v

section Lattice

variable [Fintype V]

/-- The `none`-coordinate of the image of a lifted lattice point under the blown-up intersection
matrix: the exceptional class is orthogonal to the total transforms, so only the exceptional
multiplicity survives. -/
private theorem blowUpVertex_mulVec_apply_none (y : V → ℤ) (t : ℤ) :
    ((P.blowUpVertex v).intersectionMatrix *ᵥ blowUpVertexEquiv v (y, t)) none = -t := by
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_option]
  simp only [blowUpVertex_intersectionMatrix_none_none, blowUpVertex_intersectionMatrix_none_some,
    blowUpVertexEquiv_apply_none, blowUpVertexEquiv_apply_some, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
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
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.mulVec_apply_eq_sum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> ring

/-- **The blow-up splits the intersection form.** Under the total-transform identification
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
  simp only [Finset.mem_univ, ite_true]
  ring

/-- The two total-transform identifications are dual to one another: the pairing of the lifted
covector `(k, ε)` against the lifted lattice point `(x, s)` is `⟨k, x⟩ + ε * s`. -/
theorem sum_blowUpCovectorEquiv_mul_blowUpVertexEquiv (k x : V → ℤ) (ε s : ℤ) :
    ∑ a, blowUpCovectorEquiv v (k, ε) a * blowUpVertexEquiv v (x, s) a =
      (∑ w, k w * x w) + ε * s := by
  rw [Fintype.sum_option]
  simp only [blowUpCovectorEquiv_apply_none, blowUpCovectorEquiv_apply_some,
    blowUpVertexEquiv_apply_none, blowUpVertexEquiv_apply_some, sub_mul, ite_mul, zero_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ v fun w => ε * x w]
  simp only [Finset.mem_univ, ite_true]
  ring

/-- The exceptional class has self-intersection `-1`. -/
theorem intersectionForm_single_none_self :
    (P.blowUpVertex v).intersectionForm (Pi.single (none : Option V) (1 : ℤ))
        (Pi.single (none : Option V) (1 : ℤ)) = -1 := by
  rw [(P.blowUpVertex v).intersectionForm_single, blowUpVertex_intersectionMatrix_none_none]

/-- The exceptional class is orthogonal to every total transform, so the splitting of
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
blow-up move stays inside the class of plumbings the theory applies to.

Exposed to `grind` as a rewrite, like the other `IsNegativeDefinite` characterizations, so that
`grind` reduces negative-definiteness of a blow-up to negative-definiteness of `P`. -/
@[grind =]
theorem isNegativeDefinite_blowUpVertex_iff [Finite V] :
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
