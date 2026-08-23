/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The infimal `c`-transform, `c`-concavity, and contact sets

The Kantorovich dual constraint on a pair of potentials `φ : X → EReal` and `ψ : Y → EReal`
against a cost `c : X × Y → ℝ` is the pointwise inequality `φ x + ψ y ≤ c (x, y)`. With `φ`
fixed, the largest `ψ` satisfying it is the *infimal `c`-transform*
`cTransform c φ y = ⨅ x, (c (x, y) - φ x)`, and symmetrically with `ψ` fixed. This file builds
that transform, the two closure operations it generates, the `c`-concave potentials they fix,
and the contact set on which the dual constraint is an equality.

Even for a finite real cost and a finite real potential the infimum defining the transform can
be `-∞`, so the transform must have an extended-real codomain; and once the codomain is
extended, iterating the transform forces extended-real potentials. The cost is therefore taken
finite here, and that is exactly what makes the subtraction safe: `(c (x, y) : EReal) - φ x`
subtracts an arbitrary extended real from a real one, so it is never of the form `∞ - ∞`, and no
statement below hides such a term. Concretely, Mathlib's `EReal.le_sub_iff_add_le` applies with
no side condition, which gives the adjunction `ψ ≤ cTransform c φ ↔ φ ≤ cTransformSymm c ψ`
recorded as `TauCeti.cTransform_galoisConnection`. For an extended-valued cost the same formula
is *not* the right one: with `c ≡ ⊤` and `φ ≡ 0`, `EReal` subtraction gives `⊤ - ⊤ = ⊥`, so the
double transform of `φ` is `⊥` on nonempty factors and the inequality `φ ≤ φᶜᶜ` fails. The
extended-cost interface needs its own conventions and is not built here.

Nothing in this file is measure-theoretic: the two factors are bare types and the results are
order-theoretic identities about the transform. They are the algebraic half of the Kantorovich
dual problem, to be combined with the integrability conditions that make the two marginal
integrals of a dual pair meaningful.

## Main definitions

* `TauCeti.cTransform c φ` — the infimal `c`-transform `y ↦ ⨅ x, (c (x, y) - φ x)` of a
  potential on the source, and `TauCeti.cTransformSymm c ψ`, the symmetric transform
  `x ↦ ⨅ y, (c (x, y) - ψ y)` of a potential on the target;
* `TauCeti.IsCConcave c φ` and `TauCeti.IsCConcaveSymm c ψ` — the potentials that arise as a
  transform, equivalently those fixed by the corresponding double transform;
* `TauCeti.contactSet c φ ψ` — the set where the dual constraint holds with equality, and
  `TauCeti.cSuperdifferential c φ`, its instance at the canonical partner `cTransform c φ`.

## Main statements

* `TauCeti.add_cTransform_le` — the transform is dual feasible against its own source potential,
  and `TauCeti.le_cTransform_iff` — it is the largest such partner; together these give
  `TauCeti.cTransform_galoisConnection`, the antitone Galois connection between the potentials
  on the two factors, and with it the order reversal `TauCeti.cTransform_antitone`;
* `TauCeti.le_cTransformSymm_cTransform` — a potential is dominated by its double transform, so
  transforming a dual feasible pair improves it, and
  `TauCeti.cTransform_cTransformSymm_cTransform` — a transform is unchanged by a further double
  transform;
* `TauCeti.isCConcave_iff` — `c`-concavity is exactly being fixed by the double transform;
* `TauCeti.upperSemicontinuous_cTransform` — a cost with continuous sections has an upper
  semicontinuous transform;
* `TauCeti.cTransform_add_const` — the transform turns an additive real constant into its
  negative, which is the normalisation freedom of the dual problem;
* `TauCeti.contactSet_subset_contactSet_cTransform` — the improvement step only enlarges the
  contact set, and `TauCeti.cTransformSymm_cTransform_eq_of_mem_cSuperdifferential` — a
  potential agrees with its double transform at every point of its `c`-superdifferential.

This is Layer 2, item 2 of the optimal-transport roadmap.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.4, where the `c`-transform, `c`-concavity and the `c`-superdifferential are introduced for
  a real cost;
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Chapter 5, in particular
  the discussion of `c`-convexity preceding Theorem 5.10;
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Progress in Nonlinear
  Differential Equations and their Applications 87, 2015, §1.6.
-/

public section

noncomputable section

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v}

/-- The infimal `c`-transform of a potential `φ` on the source: the largest potential on the
target that is dual feasible against `φ` for the cost `c`, namely
`cTransform c φ y = ⨅ x, (c (x, y) - φ x)`. The cost is real and the potential is extended real,
so the subtraction is always defined; the infimum can be `-∞`, and it is `⊤` when `X` is
empty. -/
@[expose]
def cTransform (c : X × Y → ℝ) (φ : X → EReal) (y : Y) : EReal :=
  ⨅ x, ((c (x, y) : EReal) - φ x)

/-- The infimal `c`-transform of a potential `ψ` on the target: the largest potential on the
source that is dual feasible against `ψ` for the cost `c`, namely
`cTransformSymm c ψ x = ⨅ y, (c (x, y) - ψ y)`. It is `TauCeti.cTransform` for the transposed
cost, and is provided so that no user has to transpose a product by hand. -/
@[expose]
def cTransformSymm (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) : EReal :=
  ⨅ y, ((c (x, y) : EReal) - ψ y)

variable {c c' : X × Y → ℝ} {φ φ' : X → EReal} {ψ ψ' : Y → EReal} {a : EReal} {x : X} {y : Y}

/-- The defining formula for the `c`-transform. -/
theorem cTransform_apply (c : X × Y → ℝ) (φ : X → EReal) (y : Y) :
    cTransform c φ y = ⨅ x, ((c (x, y) : EReal) - φ x) := rfl

/-- The defining formula for the symmetric `c`-transform. -/
theorem cTransformSymm_apply (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) :
    cTransformSymm c ψ x = ⨅ y, ((c (x, y) : EReal) - ψ y) := rfl

/-- The symmetric transform is the transform of the transposed cost. -/
theorem cTransformSymm_eq_cTransform (c : X × Y → ℝ) (ψ : Y → EReal) :
    cTransformSymm c ψ = cTransform (fun p : Y × X => c (p.2, p.1)) ψ := rfl

/-- Each source point bounds the `c`-transform at each target point. -/
theorem cTransform_le (c : X × Y → ℝ) (φ : X → EReal) (x : X) (y : Y) :
    cTransform c φ y ≤ (c (x, y) : EReal) - φ x :=
  iInf_le _ x

/-- Each target point bounds the symmetric `c`-transform at each source point. -/
theorem cTransformSymm_le (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) (y : Y) :
    cTransformSymm c ψ x ≤ (c (x, y) : EReal) - ψ y :=
  iInf_le _ y

/-- A lower bound valid at every source point is a lower bound for the `c`-transform. -/
theorem le_cTransform (h : ∀ x, a ≤ (c (x, y) : EReal) - φ x) : a ≤ cTransform c φ y :=
  le_iInf h

/-- A lower bound valid at every target point is a lower bound for the symmetric
`c`-transform. -/
theorem le_cTransformSymm (h : ∀ y, a ≤ (c (x, y) : EReal) - ψ y) : a ≤ cTransformSymm c ψ x :=
  le_iInf h

/-- The `c`-transform of `φ` is dual feasible against `φ`. -/
theorem add_cTransform_le (c : X × Y → ℝ) (φ : X → EReal) (x : X) (y : Y) :
    φ x + cTransform c φ y ≤ (c (x, y) : EReal) := by
  rw [add_comm]
  exact EReal.add_le_of_le_sub (cTransform_le c φ x y)

/-- The symmetric `c`-transform of `ψ` is dual feasible against `ψ`. -/
theorem cTransformSymm_add_le (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) (y : Y) :
    cTransformSymm c ψ x + ψ y ≤ (c (x, y) : EReal) :=
  EReal.add_le_of_le_sub (cTransformSymm_le c ψ x y)

/-- The `c`-transform of `φ` is the *largest* potential on the target that is dual feasible
against `φ`. -/
theorem le_cTransform_iff : ψ ≤ cTransform c φ ↔ ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal) := by
  refine ⟨fun h x y => (add_le_add le_rfl (h y)).trans (add_cTransform_le c φ x y), fun h y => ?_⟩
  refine le_cTransform fun x => ?_
  rw [EReal.le_sub_iff_add_le (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)), add_comm]
  exact h x y

/-- The symmetric `c`-transform of `ψ` is the *largest* potential on the source that is dual
feasible against `ψ`. -/
theorem le_cTransformSymm_iff :
    φ ≤ cTransformSymm c ψ ↔ ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal) := by
  refine ⟨fun h x y => (add_le_add (h x) le_rfl).trans (cTransformSymm_add_le c ψ x y),
    fun h x => ?_⟩
  refine le_cTransformSymm fun y => ?_
  rw [EReal.le_sub_iff_add_le (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))]
  exact h x y

/-- The two `c`-transforms form an antitone Galois connection between the potentials on the two
factors: `ψ ≤ cTransform c φ` and `φ ≤ cTransformSymm c ψ` each say that the pair `(φ, ψ)` is
dual feasible. Order reversal, the double-transform inequalities and the triple-transform
identities below are its standard consequences. -/
theorem cTransform_galoisConnection (c : X × Y → ℝ) :
    GaloisConnection (fun φ : X → EReal => OrderDual.toDual (cTransform c φ))
      (fun ψ : (Y → EReal)ᵒᵈ => cTransformSymm c (OrderDual.ofDual ψ)) := fun _ _ =>
  le_cTransform_iff.trans le_cTransformSymm_iff.symm

/-- The `c`-transform reverses the order of potentials. -/
theorem cTransform_antitone (c : X × Y → ℝ) : Antitone (cTransform c) := fun _ _ h y =>
  le_cTransform fun x => (cTransform_le c _ x y).trans (EReal.sub_le_sub le_rfl (h x))

/-- The symmetric `c`-transform reverses the order of potentials. -/
theorem cTransformSymm_antitone (c : X × Y → ℝ) : Antitone (cTransformSymm c) := fun _ _ h x =>
  le_cTransformSymm fun y => (cTransformSymm_le c _ x y).trans (EReal.sub_le_sub le_rfl (h y))

/-- A potential is dominated by its double `c`-transform. Transforming a dual feasible pair
twice therefore improves it. -/
theorem le_cTransformSymm_cTransform (c : X × Y → ℝ) (φ : X → EReal) :
    φ ≤ cTransformSymm c (cTransform c φ) :=
  le_cTransformSymm_iff.2 fun x y => add_cTransform_le c φ x y

/-- A potential on the target is dominated by its double `c`-transform. -/
theorem le_cTransform_cTransformSymm (c : X × Y → ℝ) (ψ : Y → EReal) :
    ψ ≤ cTransform c (cTransformSymm c ψ) :=
  le_cTransform_iff.2 fun x y => cTransformSymm_add_le c ψ x y

/-- A `c`-transform is unchanged by a further double transform: three transforms are one. -/
theorem cTransform_cTransformSymm_cTransform (c : X × Y → ℝ) (φ : X → EReal) :
    cTransform c (cTransformSymm c (cTransform c φ)) = cTransform c φ :=
  le_antisymm (cTransform_antitone c (le_cTransformSymm_cTransform c φ))
    (le_cTransform_cTransformSymm c (cTransform c φ))

/-- A symmetric `c`-transform is unchanged by a further double transform. -/
theorem cTransformSymm_cTransform_cTransformSymm (c : X × Y → ℝ) (ψ : Y → EReal) :
    cTransformSymm c (cTransform c (cTransformSymm c ψ)) = cTransformSymm c ψ :=
  le_antisymm (cTransformSymm_antitone c (le_cTransform_cTransformSymm c ψ))
    (le_cTransformSymm_cTransform c (cTransformSymm c ψ))

/-- The `c`-transform is monotone in the cost. -/
theorem cTransform_mono_cost (h : c ≤ c') (φ : X → EReal) :
    cTransform c φ ≤ cTransform c' φ := fun y =>
  le_cTransform fun x =>
    (cTransform_le c φ x y).trans (EReal.sub_le_sub (EReal.coe_le_coe_iff.2 (h (x, y))) le_rfl)

/-- The symmetric `c`-transform is monotone in the cost. -/
theorem cTransformSymm_mono_cost (h : c ≤ c') (ψ : Y → EReal) :
    cTransformSymm c ψ ≤ cTransformSymm c' ψ := fun x =>
  le_cTransformSymm fun y =>
    (cTransformSymm_le c ψ x y).trans (EReal.sub_le_sub (EReal.coe_le_coe_iff.2 (h (x, y))) le_rfl)

/-- If the potential avoids `-∞` at one source point, its `c`-transform avoids `⊤`. In
particular a real potential on a nonempty source has a transform valued in `[-∞, ∞)`. -/
theorem cTransform_lt_top (c : X × Y → ℝ) (hx : φ x ≠ ⊥) (y : Y) : cTransform c φ y < ⊤ := by
  refine lt_of_le_of_lt (cTransform_le c φ x y) ?_
  rcases eq_or_ne (φ x) ⊤ with h | h
  · simp [h]
  · rw [← EReal.coe_toReal h hx, ← EReal.coe_sub]
    exact EReal.coe_lt_top _

/-- The `c`-transform of a potential on an empty source is `⊤`. -/
@[simp]
theorem cTransform_of_isEmpty [IsEmpty X] (c : X × Y → ℝ) (φ : X → EReal) (y : Y) :
    cTransform c φ y = ⊤ := by
  simp [cTransform_apply]

/-- If every section `y ↦ c (x, y)` of the cost is continuous, the `c`-transform is upper
semicontinuous, being a pointwise infimum of functions each of which is continuous or constant.
No finiteness of the potential is needed. -/
theorem upperSemicontinuous_cTransform [TopologicalSpace Y]
    (hc : ∀ x, Continuous fun y => c (x, y)) (φ : X → EReal) :
    UpperSemicontinuous (cTransform c φ) := by
  have hφ : cTransform c φ = fun y => ⨅ x, ((c (x, y) : EReal) - φ x) := rfl
  rw [hφ]
  refine upperSemicontinuous_iInf fun x => ?_
  rcases eq_or_ne (φ x) ⊥ with h | h
  · simp only [h, EReal.coe_sub_bot]
    exact upperSemicontinuous_const
  rcases eq_or_ne (φ x) ⊤ with h' | h'
  · simp only [h', EReal.sub_top]
    exact upperSemicontinuous_const
  obtain ⟨b, hb⟩ : ∃ b : ℝ, φ x = (b : EReal) := ⟨_, (EReal.coe_toReal h' h).symm⟩
  simp only [hb, ← EReal.coe_sub]
  exact (EReal.continuous_coe_iff.2 ((hc x).sub continuous_const)).upperSemicontinuous

/-- Subtracting a real constant commutes with an infimum in `EReal`; both sides are `⊤` when the
index type is empty. This is the shift that normalises a `c`-transform. -/
private theorem iInf_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨅ i, (f i - (a : EReal))) = (⨅ i, f i) - (a : EReal) := by
  refine le_antisymm ?_ (le_iInf fun i => EReal.sub_le_sub (iInf_le f i) le_rfl)
  rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))]
  exact le_iInf fun i => EReal.add_le_of_le_sub (iInf_le _ i)

/-- Shifting a potential by a real constant shifts its `c`-transform by the opposite constant.
This is the normalisation freedom of the Kantorovich dual problem: the pair `(φ + a, φᶜ - a)`
satisfies the same dual constraint as `(φ, φᶜ)`. -/
theorem cTransform_add_const (c : X × Y → ℝ) (φ : X → EReal) (a : ℝ) :
    cTransform c (fun x => φ x + (a : EReal)) = fun y => cTransform c φ y - (a : EReal) := by
  funext y
  simp only [cTransform_apply]
  rw [← iInf_sub_coe]
  refine iInf_congr fun x => ?_
  rcases eq_or_ne (φ x) ⊥ with h | h
  · simp [h]
  rcases eq_or_ne (φ x) ⊤ with h' | h'
  · simp [h']
  rw [← EReal.coe_toReal h' h, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_sub, EReal.coe_eq_coe_iff]
  ring

/-- Shifting a potential on the target by a real constant shifts its symmetric `c`-transform by
the opposite constant. -/
theorem cTransformSymm_add_const (c : X × Y → ℝ) (ψ : Y → EReal) (a : ℝ) :
    cTransformSymm c (fun y => ψ y + (a : EReal)) = fun x => cTransformSymm c ψ x - (a : EReal) :=
  cTransform_add_const (fun p : Y × X => c (p.2, p.1)) ψ a

/-! ### `c`-concave potentials -/

/-- A potential on the source is `c`-concave when it is the symmetric `c`-transform of some
potential on the target. By `TauCeti.isCConcave_iff` this happens exactly when it is fixed by
the double transform. -/
def IsCConcave (c : X × Y → ℝ) (φ : X → EReal) : Prop :=
  ∃ ψ : Y → EReal, φ = cTransformSymm c ψ

/-- A potential on the target is `c`-concave when it is the `c`-transform of some potential on
the source. By `TauCeti.isCConcaveSymm_iff` this happens exactly when it is fixed by the double
transform. -/
def IsCConcaveSymm (c : X × Y → ℝ) (ψ : Y → EReal) : Prop :=
  ∃ φ : X → EReal, ψ = cTransform c φ

/-- Every symmetric `c`-transform is `c`-concave. -/
theorem isCConcave_cTransformSymm (c : X × Y → ℝ) (ψ : Y → EReal) :
    IsCConcave c (cTransformSymm c ψ) := ⟨ψ, rfl⟩

/-- Every `c`-transform is `c`-concave. -/
theorem isCConcaveSymm_cTransform (c : X × Y → ℝ) (φ : X → EReal) :
    IsCConcaveSymm c (cTransform c φ) := ⟨φ, rfl⟩

/-- A potential on the source is `c`-concave exactly when it is fixed by the double
`c`-transform. -/
theorem isCConcave_iff : IsCConcave c φ ↔ cTransformSymm c (cTransform c φ) = φ := by
  refine ⟨?_, fun h => ⟨cTransform c φ, h.symm⟩⟩
  rintro ⟨ψ, rfl⟩
  exact cTransformSymm_cTransform_cTransformSymm c ψ

/-- A potential on the target is `c`-concave exactly when it is fixed by the double
`c`-transform. -/
theorem isCConcaveSymm_iff : IsCConcaveSymm c ψ ↔ cTransform c (cTransformSymm c ψ) = ψ := by
  refine ⟨?_, fun h => ⟨cTransformSymm c ψ, h.symm⟩⟩
  rintro ⟨φ, rfl⟩
  exact cTransform_cTransformSymm_cTransform c φ

/-- A `c`-concave potential is fixed by the double `c`-transform. -/
alias ⟨IsCConcave.cTransformSymm_cTransform, _⟩ := isCConcave_iff

/-- A `c`-concave potential on the target is fixed by the double `c`-transform. -/
alias ⟨IsCConcaveSymm.cTransform_cTransformSymm, _⟩ := isCConcaveSymm_iff

/-! ### Contact sets and `c`-superdifferentials -/

/-- The contact set of a pair of potentials: the set where the dual constraint
`φ x + ψ y ≤ c (x, y)` holds with equality. For a dual feasible pair this is the set that a
complementary slackness condition refers to. -/
@[expose]
def contactSet (c : X × Y → ℝ) (φ : X → EReal) (ψ : Y → EReal) : Set (X × Y) :=
  {z | φ z.1 + ψ z.2 = (c z : EReal)}

/-- The `c`-superdifferential of a potential: its contact set against its own `c`-transform. -/
@[expose]
def cSuperdifferential (c : X × Y → ℝ) (φ : X → EReal) : Set (X × Y) :=
  contactSet c φ (cTransform c φ)

/-- Membership in the contact set, for a point of the product. -/
theorem mem_contactSet_iff {z : X × Y} :
    z ∈ contactSet c φ ψ ↔ φ z.1 + ψ z.2 = (c z : EReal) := Iff.rfl

/-- Membership in the contact set, for an explicit pair. -/
@[simp]
theorem mk_mem_contactSet_iff :
    (x, y) ∈ contactSet c φ ψ ↔ φ x + ψ y = (c (x, y) : EReal) := Iff.rfl

/-- The `c`-superdifferential is the contact set against the `c`-transform. -/
theorem cSuperdifferential_eq (c : X × Y → ℝ) (φ : X → EReal) :
    cSuperdifferential c φ = contactSet c φ (cTransform c φ) := rfl

/-- Membership in the `c`-superdifferential, for an explicit pair. -/
@[simp]
theorem mk_mem_cSuperdifferential_iff :
    (x, y) ∈ cSuperdifferential c φ ↔ φ x + cTransform c φ y = (c (x, y) : EReal) := Iff.rfl

/-- The contact set is invariant under transposing the cost and swapping the potentials. -/
theorem mk_mem_contactSet_transpose_iff :
    (y, x) ∈ contactSet (fun p : Y × X => c (p.2, p.1)) ψ φ ↔ (x, y) ∈ contactSet c φ ψ := by
  rw [mk_mem_contactSet_iff, mk_mem_contactSet_iff, add_comm]

/-- Both potentials are finite at a contact point: the dual constraint cannot hold with equality
at an infinite value, because the cost is real. -/
theorem exists_coe_of_mem_contactSet (hz : (x, y) ∈ contactSet c φ ψ) :
    ∃ b b' : ℝ, φ x = (b : EReal) ∧ ψ y = (b' : EReal) ∧ b + b' = c (x, y) := by
  rw [mk_mem_contactSet_iff] at hz
  have hbot : φ x + ψ y ≠ ⊥ := hz ▸ EReal.coe_ne_bot _
  have hbot₁ : φ x ≠ ⊥ := fun h => hbot (by simp [h])
  have hbot₂ : ψ y ≠ ⊥ := fun h => hbot (by simp [h])
  have htop : φ x + ψ y ≠ ⊤ := hz ▸ EReal.coe_ne_top _
  obtain ⟨htop₁, htop₂⟩ := (EReal.add_ne_top_iff_ne_top₂ hbot₁ hbot₂).1 htop
  refine ⟨(φ x).toReal, (ψ y).toReal, (EReal.coe_toReal htop₁ hbot₁).symm,
    (EReal.coe_toReal htop₂ hbot₂).symm, ?_⟩
  rw [← EReal.coe_eq_coe_iff, EReal.coe_add, EReal.coe_toReal htop₁ hbot₁,
    EReal.coe_toReal htop₂ hbot₂]
  exact hz

/-- The source potential avoids `-∞` at a contact point. -/
theorem ne_bot_left_of_mem_contactSet (hz : (x, y) ∈ contactSet c φ ψ) : φ x ≠ ⊥ := by
  obtain ⟨b, -, hb, -, -⟩ := exists_coe_of_mem_contactSet hz
  simp [hb]

/-- The source potential avoids `⊤` at a contact point. -/
theorem ne_top_left_of_mem_contactSet (hz : (x, y) ∈ contactSet c φ ψ) : φ x ≠ ⊤ := by
  obtain ⟨b, -, hb, -, -⟩ := exists_coe_of_mem_contactSet hz
  simp [hb]

/-- The target potential avoids `-∞` at a contact point. -/
theorem ne_bot_right_of_mem_contactSet (hz : (x, y) ∈ contactSet c φ ψ) : ψ y ≠ ⊥ := by
  obtain ⟨-, b', -, hb', -⟩ := exists_coe_of_mem_contactSet hz
  simp [hb']

/-- The target potential avoids `⊤` at a contact point. -/
theorem ne_top_right_of_mem_contactSet (hz : (x, y) ∈ contactSet c φ ψ) : ψ y ≠ ⊤ := by
  obtain ⟨-, b', -, hb', -⟩ := exists_coe_of_mem_contactSet hz
  simp [hb']

/-- At a contact point of a dual feasible pair, the second potential already agrees with the
`c`-transform of the first: the infimum defining that transform is attained there. -/
theorem cTransform_eq_of_mem_contactSet (hfeas : ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal))
    (hz : (x, y) ∈ contactSet c φ ψ) : cTransform c φ y = ψ y := by
  obtain ⟨b, b', hb, hb', -⟩ := exists_coe_of_mem_contactSet hz
  refine le_antisymm ?_ (le_cTransform_iff.2 hfeas y)
  have h := cTransform_le c φ x y
  rw [mk_mem_contactSet_iff, hb] at hz
  rwa [hb, ← hz, EReal.add_sub_cancel_left] at h

/-- At a contact point of a dual feasible pair, the first potential already agrees with the
symmetric `c`-transform of the second. -/
theorem cTransformSymm_eq_of_mem_contactSet (hfeas : ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal))
    (hz : (x, y) ∈ contactSet c φ ψ) : cTransformSymm c ψ x = φ x := by
  rw [cTransformSymm_eq_cTransform]
  exact cTransform_eq_of_mem_contactSet (c := fun p : Y × X => c (p.2, p.1))
    (fun y x => by rw [add_comm]; exact hfeas x y) (mk_mem_contactSet_transpose_iff.2 hz)

/-- Transforming a dual feasible pair only enlarges its contact set. This is the sense in which
the `c`-transform *improves* a dual feasible pair: the new pair dominates the old one pointwise,
is still dual feasible, and still touches the cost wherever the old one did. -/
theorem contactSet_subset_contactSet_cTransform
    (hfeas : ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal)) :
    contactSet c φ ψ ⊆ contactSet c (cTransformSymm c ψ) (cTransform c φ) := by
  rintro ⟨x, y⟩ hz
  rw [mk_mem_contactSet_iff, cTransformSymm_eq_of_mem_contactSet hfeas hz,
    cTransform_eq_of_mem_contactSet hfeas hz]
  exact hz

/-- The contact set of a potential against its own `c`-transform is the largest one available:
every dual feasible pair with the same source potential has a smaller contact set. -/
theorem contactSet_subset_cSuperdifferential (hfeas : ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal)) :
    contactSet c φ ψ ⊆ cSuperdifferential c φ := by
  rintro ⟨x, y⟩ hz
  rw [mk_mem_cSuperdifferential_iff, cTransform_eq_of_mem_contactSet hfeas hz]
  exact hz

/-- On its `c`-superdifferential, the infimum defining the `c`-transform is attained. -/
theorem cTransform_eq_of_mem_cSuperdifferential (hz : (x, y) ∈ cSuperdifferential c φ) :
    cTransform c φ y = (c (x, y) : EReal) - φ x := by
  rw [cSuperdifferential_eq] at hz
  obtain ⟨b, -, hb, -, -⟩ := exists_coe_of_mem_contactSet hz
  rw [mk_mem_contactSet_iff, hb] at hz
  rw [hb, ← hz, EReal.add_sub_cancel_left]

/-- A potential agrees with its double `c`-transform at every point of its
`c`-superdifferential, whether or not it is `c`-concave elsewhere. -/
theorem cTransformSymm_cTransform_eq_of_mem_cSuperdifferential
    (hz : (x, y) ∈ cSuperdifferential c φ) : cTransformSymm c (cTransform c φ) x = φ x := by
  rw [cSuperdifferential_eq] at hz
  exact cTransformSymm_eq_of_mem_contactSet (fun x y => add_cTransform_le c φ x y) hz

end TauCeti

end

end
