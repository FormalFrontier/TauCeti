/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Relations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Scalar-labelled skew-zigzag relation quotients

A skew-zigzag relation quotient changes the ordinary relation identifying all backtracks at a
vertex by allowing a unit-valued, hence invertible, scalar ratio between each ordered pair of
incident edges.  A parameter
therefore assigns a unit `ratio h h'` to two adjacencies with a common source, subject to the
reflexive, inverse, and cocycle identities for these ratios.  The quotient imposes

```text
backtrack(h) = ratio(h,h') • backtrack(h').
```

As for the ordinary relation quotient, non-returning length-two paths and paths of length at least
three vanish.  At the constant parameter, all of whose ratios are one, the relation ideal is the
ordinary zigzag relation ideal, so the two presentations agree there.

## Main definitions

* `TauCeti.SkewZigzagParameter`: a unit-valued backtrack-ratio labelling.
* the `One` instance on `TauCeti.SkewZigzagParameter`: the constant parameter, all of whose ratios
  are one.
* `TauCeti.IsSkewZigzagRelator` and `TauCeti.skewZigzagIdeal`: the uniform skew relation family
  and the two-sided ideal it generates.
* `TauCeti.skewZigzagQuotient` and `TauCeti.skewZigzagMk`: the relation quotient and quotient map.
* `TauCeti.skewZigzagQuotientOneEquiv`: the identification of the constant-parameter quotient with
  the ordinary zigzag relation quotient.

## Main results

* `TauCeti.skewZigzagMk_backtrackElem_eq_smul`: the defining scalar backtrack relation in the
  quotient.
* `TauCeti.skewZigzagLift` and `TauCeti.skewZigzagLift_unique`: the quotient universal property.
* `TauCeti.skewZigzagIdeal_one_eq_zigzagIdeal`: the constant parameter spans the ordinary zigzag
  relation ideal.

## References

This is the scalar-labelled/skew-zigzag definition clause of Layer 1 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.  See C. Couture, *Skew-Zigzag Algebras*,
Definition 3.1 and Definition 3.2, https://arxiv.org/abs/1509.08405.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

/-- A skew-zigzag parameter assigns a unit-valued, hence invertible, scalar ratio to every ordered
pair of adjacencies with a common source.  The units make invertibility part of the type, and the
fields below record the coefficient identities.  Gauge equivalence of parameters is intentionally
not imposed by this presentation. -/
@[ext]
structure SkewZigzagParameter (k : Type w) [Monoid k] {V : Type u} (G : SimpleGraph V) where
  /-- The ratio from the backtrack indexed by `h` to the one indexed by `h'`. -/
  ratio : ∀ ⦃i j j' : V⦄, G.Adj i j → G.Adj i j' → kˣ
  /-- A backtrack has ratio one with itself. -/
  ratio_self : ∀ ⦃i j : V⦄ (h : G.Adj i j), ratio h h = 1
  /-- Reversing an ordered pair of backtracks inverts its ratio. -/
  ratio_inv : ∀ ⦃i j j' : V⦄ (h : G.Adj i j) (h' : G.Adj i j'),
    ratio h h' * ratio h' h = 1
  /-- Ratios between three backtracks satisfy the multiplicative cocycle identity. -/
  ratio_cocycle : ∀ ⦃i j j' j'' : V⦄ (h : G.Adj i j) (h' : G.Adj i j')
    (h'' : G.Adj i j''), ratio h h' * ratio h' h'' * ratio h'' h = 1

attribute [simp] SkewZigzagParameter.ratio_self

namespace SkewZigzagParameter

section One

variable {k : Type w} [Monoid k] {V : Type u} {G : SimpleGraph V}

/-- The constant skew-zigzag parameter, all of whose ratios are one: it imposes that all backtracks
at a vertex are equal, which is the ordinary zigzag relation. -/
instance : One (SkewZigzagParameter k G) where
  one :=
    { ratio _ _ _ _ _ := 1
      ratio_self := by intro i j h; rfl
      ratio_inv := by intro i j j' h h'; exact one_mul 1
      ratio_cocycle := by intro i j j' j'' h h' h''; rw [one_mul, one_mul] }

@[simp]
theorem one_ratio {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j') :
    (1 : SkewZigzagParameter k G).ratio h h' = 1 := (rfl)

end One

variable {k : Type w} [MonoidWithZero k] [Nontrivial k] {V : Type u} {G : SimpleGraph V}

/-- The scalar ratio attached to two incident edges is nonzero. -/
theorem ratio_ne_zero (c : SkewZigzagParameter k G) {i j j' : V} (h : G.Adj i j)
    (h' : G.Adj i j') : (c.ratio h h' : k) ≠ 0 :=
  Units.ne_zero (c.ratio h h')

end SkewZigzagParameter

/-- The uniform skew-zigzag relators: non-returning quadratic paths, scalar ratios between
backtracks based at one vertex, and all paths of length at least three. -/
inductive IsSkewZigzagRelator (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)
    (c : SkewZigzagParameter k G) : pathAlgebra k (DoubledQuiver G) → Prop
  | nonreturn {i j : DoubledQuiver G} (p : _root_.Quiver.Path i j) (length_eq : p.length = 2)
      (different_endpoints : i ≠ j) : IsSkewZigzagRelator k G c (ofPath ⟨i, j, p⟩)
  | backtrack_ratio {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j') :
      IsSkewZigzagRelator k G c
        (backtrackElem G k h - (c.ratio h h' : k) • backtrackElem G k h')
  | long_path (x : Quiver.TotalPath (DoubledQuiver G)) (three_le : 3 ≤ x.2.2.length) :
      IsSkewZigzagRelator k G c (ofPath x)

section Relations

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (c : SkewZigzagParameter k G)

/-- The two-sided ideal generated by the uniform skew-zigzag relation family. -/
noncomputable def skewZigzagIdeal : TwoSidedIdeal (pathAlgebra k (DoubledQuiver G)) :=
  TwoSidedIdeal.span {x | IsSkewZigzagRelator k G c x}

/-- Every skew-zigzag relator belongs to the relation ideal it generates. -/
theorem mem_skewZigzagIdeal_of_isSkewZigzagRelator {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsSkewZigzagRelator k G c x) : x ∈ skewZigzagIdeal k G c :=
  TwoSidedIdeal.subset_span hx

/-! ### The relation quotient -/

/-- The scalar-labelled skew-zigzag relation quotient of a doubled simple graph.  As with
`nonisolatedZigzagQuotient`, this is a relation quotient rather than the eventual componentwise
public zigzag algebra. -/
noncomputable abbrev skewZigzagQuotient : Type _ :=
  pathAlgebra k (DoubledQuiver G) ⧸ (skewZigzagIdeal k G c).asIdeal

/-- The quotient map onto the skew-zigzag relation quotient. -/
noncomputable def skewZigzagMk :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] skewZigzagQuotient k G c :=
  Ideal.Quotient.mkₐ k _

/-- The quotient map is the ring-theoretic quotient map of the skew relation ideal. -/
theorem skewZigzagMk_apply (x : pathAlgebra k (DoubledQuiver G)) :
    skewZigzagMk k G c x = Ideal.Quotient.mk (skewZigzagIdeal k G c).asIdeal x :=
  by rw [skewZigzagMk, Ideal.Quotient.mkₐ_eq_mk]

/-- The kernel of the skew-zigzag quotient map is its relation ideal. -/
@[simp]
theorem skewZigzagMk_eq_zero_iff {x : pathAlgebra k (DoubledQuiver G)} :
    skewZigzagMk k G c x = 0 ↔ x ∈ skewZigzagIdeal k G c := by
  rw [skewZigzagMk_apply, Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal]

/-- Every skew-zigzag relator dies in the quotient. -/
theorem skewZigzagMk_eq_zero_of_isSkewZigzagRelator {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsSkewZigzagRelator k G c x) : skewZigzagMk k G c x = 0 :=
  (skewZigzagMk_eq_zero_iff k G c).mpr (mem_skewZigzagIdeal_of_isSkewZigzagRelator k G c hx)

/-- A length-two path whose endpoints differ dies in the skew-zigzag quotient. -/
@[simp]
theorem skewZigzagMk_ofPath_eq_zero_of_ne {i j : DoubledQuiver G} (p : _root_.Quiver.Path i j)
    (hp : p.length = 2) (hij : i ≠ j) : skewZigzagMk k G c (ofPath ⟨i, j, p⟩) = 0 :=
  skewZigzagMk_eq_zero_of_isSkewZigzagRelator k G c
    (IsSkewZigzagRelator.nonreturn p hp hij)

/-- A path of length at least three dies in the skew-zigzag quotient. -/
@[simp]
theorem skewZigzagMk_ofPath_eq_zero_of_three_le (x : Quiver.TotalPath (DoubledQuiver G))
    (hx : 3 ≤ x.2.2.length) : skewZigzagMk k G c (ofPath x) = 0 :=
  skewZigzagMk_eq_zero_of_isSkewZigzagRelator k G c (IsSkewZigzagRelator.long_path x hx)

/-- **The defining skew relation:** backtracks at one vertex differ by the prescribed unit-valued,
hence invertible, scalar ratio. -/
theorem skewZigzagMk_backtrackElem_eq_smul {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j') :
    skewZigzagMk k G c (backtrackElem G k h) =
      (c.ratio h h' : k) • skewZigzagMk k G c (backtrackElem G k h') := by
  have hzero := skewZigzagMk_eq_zero_of_isSkewZigzagRelator k G c
    (IsSkewZigzagRelator.backtrack_ratio h h')
  rw [map_sub, map_smul] at hzero
  exact sub_eq_zero.mp hzero

/-! ### The universal property -/

section Lift

variable {B : Type*} [Ring B] [Algebra k B]

/-- An algebra map which kills the skew relators kills the two-sided ideal they generate. -/
theorem skewZigzagIdeal_le_ker (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsSkewZigzagRelator k G c x → f x = 0) :
    skewZigzagIdeal k G c ≤ TwoSidedIdeal.ker f := by
  rw [skewZigzagIdeal, TwoSidedIdeal.span_le]
  intro x hx
  exact (TwoSidedIdeal.mem_ker f).mpr (hf x hx)

/-- An algebra map which kills every skew-zigzag relator factors through the skew relation
quotient. -/
noncomputable def skewZigzagLift (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsSkewZigzagRelator k G c x → f x = 0) :
    skewZigzagQuotient k G c →ₐ[k] B :=
  Ideal.Quotient.liftₐ _ f fun _ ha =>
    (TwoSidedIdeal.mem_ker f).mp <|
      (skewZigzagIdeal_le_ker k G c f hf
        (TwoSidedIdeal.mem_asIdeal.mp ha))

/-- The skew-zigzag lift agrees with its defining map on quotient representatives. -/
@[simp]
theorem skewZigzagLift_skewZigzagMk (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsSkewZigzagRelator k G c x → f x = 0) (x : pathAlgebra k (DoubledQuiver G)) :
    skewZigzagLift k G c f hf (skewZigzagMk k G c x) = f x := by
  rw [skewZigzagMk_apply, skewZigzagLift, Ideal.Quotient.liftₐ_apply]
  exact Ideal.Quotient.lift_mk _ _ _

/-- The skew-zigzag lift is the unique algebra map whose composite with the quotient map is its
defining map. -/
theorem skewZigzagLift_unique (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsSkewZigzagRelator k G c x → f x = 0)
    (g : skewZigzagQuotient k G c →ₐ[k] B)
    (hg : ∀ x, g (skewZigzagMk k G c x) = f x) : g = skewZigzagLift k G c f hf :=
  Ideal.Quotient.algHom_ext k <| PathAlgebra.algHom_ext k fun x ↦
    (hg (ofPath x)).trans (skewZigzagLift_skewZigzagMk k G c f hf (ofPath x)).symm

end Lift

end Relations

/-! ### The constant parameter and the ordinary zigzag relations -/

section One

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- **The constant parameter imposes exactly the ordinary zigzag relations.** Its backtrack relators
say that two backtracks at a vertex are equal, which is the ordinary quadratic relator, and the
non-returning and long-path families of the two presentations agree. -/
theorem skewZigzagIdeal_one_eq_zigzagIdeal : skewZigzagIdeal k G 1 = zigzagIdeal k G := by
  refine le_antisymm ?_ ?_
  · rw [skewZigzagIdeal, TwoSidedIdeal.span_le]
    intro x hx
    cases hx with
    | nonreturn p hlen hne =>
      exact mem_zigzagIdeal_of_isZigzagRelator k G
        (IsZigzagRelator.quadratic (IsQuadraticZigzagRelator.nonreturn p hlen hne))
    | backtrack_ratio h h' =>
      rw [SkewZigzagParameter.one_ratio, Units.val_one, one_smul]
      exact quadraticZigzagIdeal_le_zigzagIdeal k G
        (backtrackElem_sub_backtrackElem_mem_quadraticZigzagIdeal k G h h')
    | long_path y h3 =>
      exact mem_zigzagIdeal_of_isZigzagRelator k G (IsZigzagRelator.long_path y h3)
  · rw [zigzagIdeal_eq_span, TwoSidedIdeal.span_le]
    intro x hx
    cases hx with
    | quadratic hq =>
      cases hq with
      | nonreturn p hlen hne =>
        exact mem_skewZigzagIdeal_of_isSkewZigzagRelator k G 1
          (IsSkewZigzagRelator.nonreturn p hlen hne)
      | equal_backtracks p q hp hq =>
        rename_i i
        obtain ⟨v, rfl⟩ : ∃ v, i = vertex G v :=
          ⟨(vertexEquiv G).symm i, (vertexEquiv_symm_apply G i).symm⟩
        obtain ⟨j, hj, rfl⟩ := exists_eq_backtrackPath G p hp
        obtain ⟨j', hj', rfl⟩ := exists_eq_backtrackPath G q hq
        have hmem := mem_skewZigzagIdeal_of_isSkewZigzagRelator k G 1
          (IsSkewZigzagRelator.backtrack_ratio hj hj')
        rw [SkewZigzagParameter.one_ratio, Units.val_one, one_smul] at hmem
        rwa [← backtrackElem_eq_ofPath, ← backtrackElem_eq_ofPath]
    | long_path y h3 =>
      exact mem_skewZigzagIdeal_of_isSkewZigzagRelator k G 1
        (IsSkewZigzagRelator.long_path y h3)

/-- **The constant parameter presents the ordinary zigzag algebra**: its skew relation is that all
backtracks at a vertex are equal, which is the ordinary zigzag relation. -/
noncomputable def skewZigzagQuotientOneEquiv :
    skewZigzagQuotient k G 1 ≃ₐ[k] nonisolatedZigzagQuotient k G :=
  Ideal.quotientEquivAlgOfEq k
    (congrArg TwoSidedIdeal.asIdeal (skewZigzagIdeal_one_eq_zigzagIdeal k G))

/-- The comparison with the ordinary zigzag quotient sends the class of an element to its ordinary
class. -/
@[simp]
theorem skewZigzagQuotientOneEquiv_skewZigzagMk (x : pathAlgebra k (DoubledQuiver G)) :
    skewZigzagQuotientOneEquiv k G (skewZigzagMk k G 1 x) = zigzagMk k G x := by
  rw [skewZigzagMk_apply, skewZigzagQuotientOneEquiv, Ideal.quotientEquivAlgOfEq_mk, zigzagMk_apply]

end One

end TauCeti
