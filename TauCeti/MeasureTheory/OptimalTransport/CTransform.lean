/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import TauCeti.Data.EReal.Operations

/-!
# The infimal `c`-transform, `c`-concavity, and contact sets

The Kantorovich dual constraint on a pair of potentials `φ : X → EReal` and `ψ : Y → EReal`
against a cost `c : X × Y → ℝ` is the pointwise inequality `φ x + ψ y ≤ c (x, y)`. With `φ`
fixed, the largest `ψ` satisfying it is the *infimal `c`-transform*
`cTransform c φ y = ⨅ x, (c (x, y) - φ x)`, and symmetrically with `ψ` fixed. This file builds
that transform, the two closure operations it generates, the `c`-concave potentials they fix,
and the contact set on which the dual constraint is an equality. It is the finite-real slice of
the roadmap's broader transform interface; the extended-cost, analytic-sublevel, and compact
attainment/lower-semicontinuity interfaces are separate follow-up slices. The elementary
upper-semicontinuity result for infimal transforms is included here.

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

Nothing in this file is measure-theoretic: apart from the upper-semicontinuity results, the two
factors are bare types and the results are order-theoretic identities about the transform. They
are the algebraic half of the Kantorovich dual problem, to be combined with the integrability
conditions that make the two marginal integrals of a dual pair meaningful.

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
* `TauCeti.upperSemicontinuous_cTransform` — an infimal transform of upper-semicontinuous
  sections is upper semicontinuous;
* `TauCeti.cTransform_add_const` — the transform turns an additive real constant into its
  negative, which is the normalisation freedom of the dual problem;
* `TauCeti.cTransform_coe` — over a nonempty finite source the transform of a coerced real
  potential is the coercion of a real infimum;
* `TauCeti.contactSet_subset_contactSet_cTransformSymm_cTransform` — sequentially transforming a
  feasible pair gives a dominating feasible pair with a larger contact set, and
  `TauCeti.cTransformSymm_cTransform_eq_of_mem_cSuperdifferential` — a potential agrees with its
  double transform at every point of its `c`-superdifferential.

This is the finite-real algebraic slice of Layer 2, item 2 of the optimal-transport roadmap.

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
def cTransform (c : X × Y → ℝ) (φ : X → EReal) (y : Y) : EReal :=
  ⨅ x, ((c (x, y) : EReal) - φ x)

/-- The infimal `c`-transform of a potential `ψ` on the target: the largest potential on the
source that is dual feasible against `ψ` for the cost `c`, namely
`cTransformSymm c ψ x = ⨅ y, (c (x, y) - ψ y)`. It is `TauCeti.cTransform` for the transposed
cost, and is provided so that no user has to transpose a product by hand. -/
def cTransformSymm (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) : EReal :=
  ⨅ y, ((c (x, y) : EReal) - ψ y)

variable {c c' : X × Y → ℝ} {φ φ' : X → EReal} {ψ ψ' : Y → EReal} {a : EReal} {x : X} {y : Y}

/-- The defining formula for the `c`-transform. -/
theorem cTransform_apply (c : X × Y → ℝ) (φ : X → EReal) (y : Y) :
    cTransform c φ y = ⨅ x, ((c (x, y) : EReal) - φ x) := (rfl)

/-- The defining formula for the symmetric `c`-transform. -/
theorem cTransformSymm_apply (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) :
    cTransformSymm c ψ x = ⨅ y, ((c (x, y) : EReal) - ψ y) := (rfl)

/-- The symmetric transform is the transform of the transposed cost. -/
theorem cTransformSymm_eq_cTransform (c : X × Y → ℝ) (ψ : Y → EReal) :
    cTransformSymm c ψ = cTransform (fun p : Y × X => c (p.2, p.1)) ψ := (rfl)

/-- Each source point bounds the `c`-transform at each target point. -/
theorem cTransform_le (c : X × Y → ℝ) (φ : X → EReal) (x : X) (y : Y) :
    cTransform c φ y ≤ (c (x, y) : EReal) - φ x :=
  iInf_le _ x

/-- Each target point bounds the symmetric `c`-transform at each source point. -/
theorem cTransformSymm_le (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) (y : Y) :
    cTransformSymm c ψ x ≤ (c (x, y) : EReal) - ψ y := by
  simpa only [cTransformSymm_eq_cTransform] using
    cTransform_le (fun p : Y × X => c (p.2, p.1)) ψ y x

/-- A lower bound valid at every source point is a lower bound for the `c`-transform. -/
theorem le_cTransform (h : ∀ x, a ≤ (c (x, y) : EReal) - φ x) : a ≤ cTransform c φ y :=
  le_iInf h

/-- A lower bound valid at every target point is a lower bound for the symmetric
`c`-transform. -/
theorem le_cTransformSymm (h : ∀ y, a ≤ (c (x, y) : EReal) - ψ y) : a ≤ cTransformSymm c ψ x :=
  by simpa only [cTransformSymm_eq_cTransform] using
    le_cTransform (c := fun p : Y × X => c (p.2, p.1)) h

/-- The `c`-transform of `φ` is dual feasible against `φ`. -/
theorem add_cTransform_le (c : X × Y → ℝ) (φ : X → EReal) (x : X) (y : Y) :
    φ x + cTransform c φ y ≤ (c (x, y) : EReal) := by
  rw [add_comm]
  exact EReal.add_le_of_le_sub (cTransform_le c φ x y)

/-- The symmetric `c`-transform of `ψ` is dual feasible against `ψ`. -/
theorem cTransformSymm_add_le (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) (y : Y) :
    cTransformSymm c ψ x + ψ y ≤ (c (x, y) : EReal) := by
  simpa only [cTransformSymm_eq_cTransform, add_comm] using
    add_cTransform_le (fun p : Y × X => c (p.2, p.1)) ψ y x

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
  rw [cTransformSymm_eq_cTransform]
  constructor
  · intro h x y
    simpa only [add_comm] using (le_cTransform_iff.1 h y x)
  · intro h
    exact le_cTransform_iff.2 fun y x => by simpa only [add_comm] using h x y

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
  (cTransform_galoisConnection c).monotone_l h y

/-- The symmetric `c`-transform reverses the order of potentials. -/
theorem cTransformSymm_antitone (c : X × Y → ℝ) : Antitone (cTransformSymm c) := fun _ _ h x =>
  (cTransform_galoisConnection c).monotone_u h x

/-- A potential is dominated by its double `c`-transform. Transforming a dual feasible pair
twice therefore improves it. -/
theorem le_cTransformSymm_cTransform (c : X × Y → ℝ) (φ : X → EReal) :
    φ ≤ cTransformSymm c (cTransform c φ) :=
  (cTransform_galoisConnection c).le_u_l φ

/-- A potential on the target is dominated by its double `c`-transform. -/
theorem le_cTransform_cTransformSymm (c : X × Y → ℝ) (ψ : Y → EReal) :
    ψ ≤ cTransform c (cTransformSymm c ψ) :=
  (cTransform_galoisConnection c).l_u_le ψ

/-- A `c`-transform is unchanged by a further double transform: three transforms are one. -/
@[simp]
theorem cTransform_cTransformSymm_cTransform (c : X × Y → ℝ) (φ : X → EReal) :
    cTransform c (cTransformSymm c (cTransform c φ)) = cTransform c φ :=
  (cTransform_galoisConnection c).l_u_l_eq_l φ

/-- A symmetric `c`-transform is unchanged by a further double transform. -/
@[simp]
theorem cTransformSymm_cTransform_cTransformSymm (c : X × Y → ℝ) (ψ : Y → EReal) :
    cTransformSymm c (cTransform c (cTransformSymm c ψ)) = cTransformSymm c ψ :=
  (cTransform_galoisConnection c).u_l_u_eq_u ψ

/-- The `c`-transform is monotone in the cost. -/
theorem cTransform_mono_cost (h : c ≤ c') (φ : X → EReal) :
    cTransform c φ ≤ cTransform c' φ := fun y =>
  le_cTransform fun x =>
    (cTransform_le c φ x y).trans (EReal.sub_le_sub (EReal.coe_le_coe_iff.2 (h (x, y))) le_rfl)

/-- The symmetric `c`-transform is monotone in the cost. -/
theorem cTransformSymm_mono_cost (h : c ≤ c') (ψ : Y → EReal) :
    cTransformSymm c ψ ≤ cTransformSymm c' ψ := by
  simpa only [cTransformSymm_eq_cTransform] using
    cTransform_mono_cost (c := fun p : Y × X => c (p.2, p.1))
      (c' := fun p : Y × X => c' (p.2, p.1)) (fun p => h (p.2, p.1)) ψ

/-- If the potential avoids `-∞` at one source point, its `c`-transform avoids `⊤`. In
particular a real potential on a nonempty source has a transform valued in `[-∞, ∞)`. -/
theorem cTransform_lt_top_of_ne_bot (c : X × Y → ℝ) (hx : φ x ≠ ⊥) (y : Y) :
    cTransform c φ y < ⊤ := by
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

/-- If the potential avoids `-∞` at one target point, its symmetric `c`-transform avoids `⊤`. -/
theorem cTransformSymm_lt_top_of_ne_bot (c : X × Y → ℝ) (hy : ψ y ≠ ⊥) (x : X) :
    cTransformSymm c ψ x < ⊤ := by
  simpa only [cTransformSymm_eq_cTransform] using
    cTransform_lt_top_of_ne_bot (fun p : Y × X => c (p.2, p.1)) hy x

/-- The symmetric `c`-transform of a potential on an empty target is `⊤`. -/
@[simp]
theorem cTransformSymm_of_isEmpty [IsEmpty Y] (c : X × Y → ℝ) (ψ : Y → EReal) (x : X) :
    cTransformSymm c ψ x = ⊤ := by
  simpa only [cTransformSymm_eq_cTransform] using
    cTransform_of_isEmpty (fun p : Y × X => c (p.2, p.1)) ψ x

/-- On a nonempty finite source space the infimal `c`-transform of a real potential is itself
real-valued: the `c`-transform of the coerced potential is the coercion of the real infimum. -/
theorem cTransform_coe [Finite X] [Nonempty X] (c : X × Y → ℝ) (φ : X → ℝ) (y : Y) :
    cTransform c (fun x ↦ (φ x : EReal)) y = ((⨅ x, (c (x, y) - φ x) : ℝ) : EReal) := by
  obtain ⟨x₀, hx₀⟩ := exists_eq_ciInf_of_finite (f := fun x ↦ c (x, y) - φ x)
  rw [cTransform_apply, ← hx₀]
  refine le_antisymm ((iInf_le _ x₀).trans (le_of_eq (EReal.coe_sub _ _).symm))
    (le_iInf fun x ↦ ?_)
  rw [← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.2
    (hx₀.symm ▸ ciInf_le (Finite.bddBelow_range fun x ↦ c (x, y) - φ x) x)

/-- A `c`-transform is upper semicontinuous when each function in its defining infimum is upper
semicontinuous. -/
theorem upperSemicontinuous_cTransform [TopologicalSpace Y]
    (h : ∀ x, UpperSemicontinuous fun y => (c (x, y) : EReal) - φ x) :
    UpperSemicontinuous (cTransform c φ) := by
  unfold cTransform
  exact upperSemicontinuous_iInf h

/-- A symmetric `c`-transform is upper semicontinuous when each function in its defining infimum
is upper semicontinuous. -/
theorem upperSemicontinuous_cTransformSymm [TopologicalSpace X]
    (h : ∀ y, UpperSemicontinuous fun x => (c (x, y) : EReal) - ψ y) :
    UpperSemicontinuous (cTransformSymm c ψ) := by
  rw [cTransformSymm_eq_cTransform]
  exact upperSemicontinuous_cTransform h

/-- If every section `y ↦ c (x, y)` of the cost is upper semicontinuous, the `c`-transform is
upper semicontinuous. No finiteness of the potential is needed. -/
theorem upperSemicontinuous_cTransform_of_upperSemicontinuous [TopologicalSpace Y]
    (hc : ∀ x, UpperSemicontinuous fun y => c (x, y)) (φ : X → EReal) :
    UpperSemicontinuous (cTransform c φ) := by
  refine upperSemicontinuous_cTransform fun x => ?_
  rcases eq_or_ne (φ x) ⊥ with h | h
  · simp only [h, EReal.coe_sub_bot]
    exact upperSemicontinuous_const
  rcases eq_or_ne (φ x) ⊤ with h' | h'
  · simp only [h', EReal.sub_top]
    exact upperSemicontinuous_const
  obtain ⟨b, hb⟩ : ∃ b : ℝ, φ x = (b : EReal) := ⟨_, (EReal.coe_toReal h' h).symm⟩
  simp only [hb, ← EReal.coe_sub]
  exact continuous_coe_real_ereal.comp_upperSemicontinuous
    (by simpa only [sub_eq_add_neg] using (hc x).add upperSemicontinuous_const)
    EReal.coe_strictMono.monotone

/-- If every section `y ↦ c (x, y)` of the cost is continuous, the `c`-transform is upper
semicontinuous. -/
theorem upperSemicontinuous_cTransform_of_continuous [TopologicalSpace Y]
    (hc : ∀ x, Continuous fun y => c (x, y)) (φ : X → EReal) :
    UpperSemicontinuous (cTransform c φ) :=
  upperSemicontinuous_cTransform_of_upperSemicontinuous (fun x => (hc x).upperSemicontinuous) φ

/-- If every section `x ↦ c (x, y)` of the cost is upper semicontinuous, the symmetric
`c`-transform is upper semicontinuous. -/
theorem upperSemicontinuous_cTransformSymm_of_upperSemicontinuous [TopologicalSpace X]
    (hc : ∀ y, UpperSemicontinuous fun x => c (x, y)) (ψ : Y → EReal) :
    UpperSemicontinuous (cTransformSymm c ψ) := by
  rw [cTransformSymm_eq_cTransform]
  exact upperSemicontinuous_cTransform_of_upperSemicontinuous hc ψ

/-- If every section `x ↦ c (x, y)` of the cost is continuous, the symmetric `c`-transform is
upper semicontinuous. -/
theorem upperSemicontinuous_cTransformSymm_of_continuous [TopologicalSpace X]
    (hc : ∀ y, Continuous fun x => c (x, y)) (ψ : Y → EReal) :
    UpperSemicontinuous (cTransformSymm c ψ) :=
  upperSemicontinuous_cTransformSymm_of_upperSemicontinuous
    (fun y => (hc y).upperSemicontinuous) ψ

/-- Subtracting a sum whose final term is real can be reassociated when the minuend is real. -/
private theorem coe_sub_add_coe (b : EReal) (d a : ℝ) :
    (d : EReal) - (b + (a : EReal)) = (d : EReal) - b - (a : EReal) := by
  induction b with
  | bot => simp
  | coe b => norm_cast; ring
  | top => simp

/-- Shifting a potential by a real constant shifts its `c`-transform by the opposite constant.
This is the normalisation freedom of the Kantorovich dual problem: the pair `(φ + a, φᶜ - a)`
satisfies the same dual constraint as `(φ, φᶜ)`. -/
theorem cTransform_add_const (c : X × Y → ℝ) (φ : X → EReal) (a : ℝ) (y : Y) :
    cTransform c (fun x => φ x + (a : EReal)) y = cTransform c φ y - (a : EReal) := by
  simp only [cTransform_apply]
  rw [← EReal.iInf_sub_coe]
  exact iInf_congr fun x => coe_sub_add_coe (φ x) (c (x, y)) a

/-- Shifting a potential on the target by a real constant shifts its symmetric `c`-transform by
the opposite constant. -/
theorem cTransformSymm_add_const (c : X × Y → ℝ) (ψ : Y → EReal) (a : ℝ) (x : X) :
    cTransformSymm c (fun y => ψ y + (a : EReal)) x =
      cTransformSymm c ψ x - (a : EReal) := by
  simpa only [cTransformSymm_eq_cTransform] using
    cTransform_add_const (fun p : Y × X => c (p.2, p.1)) ψ a x

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
  simpa only [IsCConcaveSymm, IsCConcave, cTransformSymm_eq_cTransform] using
    (isCConcave_iff (c := fun p : Y × X => c (p.2, p.1)) (φ := ψ))

/-- A `c`-concave potential is fixed by the double `c`-transform. -/
alias ⟨IsCConcave.cTransformSymm_cTransform, _⟩ := isCConcave_iff

/-- A `c`-concave potential on the target is fixed by the double `c`-transform. -/
alias ⟨IsCConcaveSymm.cTransform_cTransformSymm, _⟩ := isCConcaveSymm_iff

/-! ### Contact sets and `c`-superdifferentials -/

/-- The contact set of a pair of potentials: the set where the dual constraint
`φ x + ψ y ≤ c (x, y)` holds with equality. For a dual feasible pair this is the set that a
complementary slackness condition refers to. -/
def contactSet (c : X × Y → ℝ) (φ : X → EReal) (ψ : Y → EReal) : Set (X × Y) :=
  {z | φ z.1 + ψ z.2 = (c z : EReal)}

/-- The `c`-superdifferential of a potential: its contact set against its own `c`-transform. -/
def cSuperdifferential (c : X × Y → ℝ) (φ : X → EReal) : Set (X × Y) :=
  contactSet c φ (cTransform c φ)

/-- Membership in the contact set, for a point of the product. -/
@[simp]
theorem mem_contactSet_iff {z : X × Y} :
    z ∈ contactSet c φ ψ ↔ φ z.1 + ψ z.2 = (c z : EReal) := Iff.rfl

/-- Membership in the contact set, for an explicit pair. -/
theorem mk_mem_contactSet_iff :
    (x, y) ∈ contactSet c φ ψ ↔ φ x + ψ y = (c (x, y) : EReal) :=
  mem_contactSet_iff

/-- The `c`-superdifferential is the contact set against the `c`-transform. -/
theorem cSuperdifferential_def (c : X × Y → ℝ) (φ : X → EReal) :
    cSuperdifferential c φ = contactSet c φ (cTransform c φ) := (rfl)

/-- Membership in the `c`-superdifferential, for a point of the product. -/
@[simp]
theorem mem_cSuperdifferential_iff {z : X × Y} :
    z ∈ cSuperdifferential c φ ↔
      φ z.1 + cTransform c φ z.2 = (c z : EReal) := Iff.rfl

/-- Membership in the `c`-superdifferential, for an explicit pair. -/
theorem mk_mem_cSuperdifferential_iff :
    (x, y) ∈ cSuperdifferential c φ ↔ φ x + cTransform c φ y = (c (x, y) : EReal) :=
  mem_cSuperdifferential_iff

/-- The contact set is invariant under swapping the cost factors and the potentials. -/
theorem mk_mem_contactSet_swap_iff :
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

/-- At a contact point, if dual feasibility holds along the corresponding target section, the
second potential already agrees with the `c`-transform of the first: the infimum defining that
transform is attained there. -/
theorem cTransform_eq_of_mem_contactSet
    (hfeas : ∀ x', φ x' + ψ y ≤ (c (x', y) : EReal))
    (hz : (x, y) ∈ contactSet c φ ψ) : cTransform c φ y = ψ y := by
  obtain ⟨b, b', hb, hb', -⟩ := exists_coe_of_mem_contactSet hz
  refine le_antisymm ?_ ?_
  · have h := cTransform_le c φ x y
    rw [mk_mem_contactSet_iff, hb] at hz
    rwa [hb, ← hz, EReal.add_sub_cancel_left] at h
  · refine le_cTransform fun x' => ?_
    rw [EReal.le_sub_iff_add_le (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)),
      add_comm]
    exact hfeas x'

/-- At a contact point, if dual feasibility holds along the corresponding source section, the
first potential already agrees with the symmetric `c`-transform of the second. -/
theorem cTransformSymm_eq_of_mem_contactSet
    (hfeas : ∀ y', φ x + ψ y' ≤ (c (x, y') : EReal))
    (hz : (x, y) ∈ contactSet c φ ψ) : cTransformSymm c ψ x = φ x := by
  rw [cTransformSymm_eq_cTransform]
  exact cTransform_eq_of_mem_contactSet (c := fun p : Y × X => c (p.2, p.1))
    (fun y' => by rw [add_comm]; exact hfeas y') (mk_mem_contactSet_swap_iff.2 hz)

/-- Replacing first the target potential by the transform of the source and then the source by
the symmetric transform of that new target only enlarges the contact set. -/
theorem contactSet_subset_contactSet_cTransformSymm_cTransform
    (hfeas : ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal)) :
    contactSet c φ ψ ⊆
      contactSet c (cTransformSymm c (cTransform c φ)) (cTransform c φ) := by
  rintro ⟨x, y⟩ hz
  have htarget := cTransform_eq_of_mem_contactSet (fun x' => hfeas x' y) hz
  have hz' : (x, y) ∈ contactSet c φ (cTransform c φ) := by
    rw [mk_mem_contactSet_iff, htarget]
    exact hz
  rw [mk_mem_contactSet_iff,
    cTransformSymm_eq_of_mem_contactSet (fun y' => add_cTransform_le c φ x y') hz', htarget]
  exact hz

/-- The contact set of a potential against its own `c`-transform is the largest one available:
every dual feasible pair with the same source potential has a smaller contact set. -/
theorem contactSet_subset_cSuperdifferential (hfeas : ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal)) :
    contactSet c φ ψ ⊆ cSuperdifferential c φ := by
  rintro ⟨x, y⟩ hz
  rw [mk_mem_cSuperdifferential_iff,
    cTransform_eq_of_mem_contactSet (fun x' => hfeas x' y) hz]
  exact hz

/-- On its `c`-superdifferential, the infimum defining the `c`-transform is attained. -/
theorem cTransform_eq_of_mem_cSuperdifferential (hz : (x, y) ∈ cSuperdifferential c φ) :
    cTransform c φ y = (c (x, y) : EReal) - φ x := by
  rw [cSuperdifferential_def] at hz
  obtain ⟨b, -, hb, -, -⟩ := exists_coe_of_mem_contactSet hz
  rw [mk_mem_contactSet_iff, hb] at hz
  rw [hb, ← hz, EReal.add_sub_cancel_left]

/-- A point where the infimum defining the `c`-transform is attained belongs to the
`c`-superdifferential, provided the source potential is real at that point. -/
theorem mem_cSuperdifferential_of_cTransform_eq {b : ℝ} (hb : φ x = (b : EReal))
    (h : cTransform c φ y = (c (x, y) : EReal) - φ x) :
    (x, y) ∈ cSuperdifferential c φ := by
  rw [mk_mem_cSuperdifferential_iff, h, hb, add_comm, EReal.sub_add_cancel]

/-- A potential agrees with its double `c`-transform at every point of its
`c`-superdifferential, whether or not it is `c`-concave elsewhere. -/
theorem cTransformSymm_cTransform_eq_of_mem_cSuperdifferential
    (hz : (x, y) ∈ cSuperdifferential c φ) : cTransformSymm c (cTransform c φ) x = φ x := by
  rw [cSuperdifferential_def] at hz
  exact cTransformSymm_eq_of_mem_contactSet (fun y' => add_cTransform_le c φ x y') hz

end TauCeti

end

end
