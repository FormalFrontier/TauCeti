/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Rescale
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew

/-!
# Gauge equivalence of skew-zigzag parameters

A skew-zigzag parameter labels each ordered pair of incident edges of a simple graph `G` by the
unit-valued ratio between the two backtracks they carry, and the associated relation quotient
imposes `backtrack(h) = ratio(h,h') • backtrack(h')`. Rescaling every arrow of the doubled quiver
by a unit is an automorphism of the doubled path algebra which fixes the vertex idempotents, so it
carries one skew presentation to another. This file identifies the induced change of parameters and
proves that it does not change the presented algebra.

Rescaling by a labelling `u` multiplies the backtrack along an edge by the *backtrack scale*
`u(h) * u(h*)`, the product of the labels of the two orientations of that edge; the scale is
therefore a function of the underlying unoriented edge. The parameter is changed by

```text
(c ⬝ u)(h,h') = c(h,h') * scale(h') / scale(h),
```

which is again reflexive, inverse-symmetric, and a multiplicative cocycle. Two parameters related
this way present isomorphic algebras, the isomorphism being the arrow rescaling itself, so gauge
equivalence is a genuine equivalence relation on parameters through which the presented algebra
factors. Specializing to the constant parameter `1`, which presents the ordinary zigzag relation
quotient, a gauge-trivial parameter presents the ordinary zigzag algebra.

## Main definitions

* `TauCeti.DoubledQuiver.backtrackScale`: the factor by which an arrow rescaling multiplies the
  backtrack along an edge.
* `TauCeti.SkewZigzagParameter.gauge`: the gauge transform of a skew-zigzag parameter.
* `TauCeti.SkewZigzagParameter.IsGaugeEquivalent`: the gauge equivalence relation on parameters.

## Main results

* `TauCeti.DoubledQuiver.backtrackScale_symm`: the backtrack scale depends only on the unoriented
  edge.
* `TauCeti.SkewZigzagParameter.IsGaugeEquivalent.equivalence`: gauge equivalence is an equivalence
  relation.
* `TauCeti.skewZigzagQuotientGaugeEquiv`: **gauge independence**, a gauge transform of a parameter
  presents an isomorphic algebra.
* `TauCeti.nonempty_algEquiv_nonisolatedZigzagQuotient_of_isGaugeEquivalent_one`: a gauge-trivial
  parameter presents the ordinary zigzag relation quotient.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, https://arxiv.org/abs/1509.08405, which sets up the
gauge relation on skew parameters and its cohomological classification.

The proof pattern for the gauge isomorphism of relation quotients — rescaling the arrows, checking
that it carries the relators of one presentation into the relation ideal of the other, and matching
the two lifts — follows `TauCeti.RepresentationTheory.Quiver.Preprojective.Gauge`.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

namespace DoubledQuiver

variable {V : Type u} (G : SimpleGraph V)

/-! ### The backtrack scale of an arrow labelling -/

section Scale

variable {M : Type*} [Monoid M]

/-- The **backtrack scale** of a labelling `u` of the arrows of a doubled quiver along an edge: the
product of the labels of the two orientations of that edge. Rescaling by `u` multiplies the
backtrack along the edge by this factor. -/
def backtrackScale (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → M) {i j : V} (h : G.Adj i j) : M :=
  u (arrow G h) * u (arrow G h.symm)

/-- The backtrack scale of a unit-valued labelling is the backtrack scale of its underlying scalar
labelling. -/
theorem val_backtrackScale {k : Type w} [Monoid k]
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) {i j : V} (h : G.Adj i j) :
    ((backtrackScale G u h : kˣ) : k) = backtrackScale G (fun _ _ e => ((u e : kˣ) : k)) h :=
  Units.val_mul _ _

end Scale

section ScaleComm

variable {M : Type*} [CommMonoid M]

/-- **The backtrack scale is a function of the unoriented edge**: it is unchanged by reversing the
adjacency indexing it. -/
theorem backtrackScale_symm (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → M) {i j : V}
    (h : G.Adj i j) : backtrackScale G u h.symm = backtrackScale G u h :=
  mul_comm _ _

end ScaleComm

/-! ### Rescaling a backtrack element -/

section Rescale

variable (k : Type w) [CommSemiring k] [Finite V]

/-- **Rescaling multiplies a backtrack element by its backtrack scale**: the backtrack element is
the product of an arrow with its reverse, and rescaling multiplies each of the two by its own
label. -/
theorem rescale_backtrackElem (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → k) {i j : V}
    (h : G.Adj i j) :
    rescale u (backtrackElem G k h) = backtrackScale G u h • backtrackElem G k h := by
  rw [← ofArrow_symm_mul_ofArrow, map_mul, rescale_ofArrow, rescale_ofArrow, smul_mul_smul_comm,
    ofArrow_symm_mul_ofArrow, backtrackScale, mul_comm]

end Rescale

end DoubledQuiver

/-! ### The gauge transform of a parameter -/

namespace SkewZigzagParameter

variable {k : Type w} [CommMonoid k] {V : Type u} {G : SimpleGraph V}

/-- The **gauge transform** of a skew-zigzag parameter by a unit-valued labelling `u` of the arrows
of the doubled quiver: each ratio is multiplied by the ratio of the two backtrack scales it
compares. This is exactly the change of parameters produced by rescaling the arrows by `u`. -/
def gauge (c : SkewZigzagParameter k G) (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) :
    SkewZigzagParameter k G where
  ratio _ _ _ h h' := c.ratio h h' * (backtrackScale G u h' / backtrackScale G u h)
  ratio_self := by
    intro i j h
    rw [c.ratio_self, one_mul, div_self']
  ratio_inv := by
    intro i j j' h h'
    rw [mul_mul_mul_comm, c.ratio_inv h h', one_mul, div_mul_div_comm, div_eq_one]
    exact mul_comm _ _
  ratio_cocycle := by
    intro i j j' j'' h h' h''
    rw [mul_mul_mul_comm (c.ratio h h') _ (c.ratio h' h''),
      mul_mul_mul_comm (c.ratio h h' * c.ratio h' h''),
      c.ratio_cocycle h h' h'', one_mul, div_mul_div_comm, div_mul_div_comm, div_eq_one]
    simp only [mul_comm, mul_assoc]

@[simp]
theorem gauge_ratio (c : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) {i j j' : V} (h : G.Adj i j)
    (h' : G.Adj i j') :
    (c.gauge u).ratio h h' =
      c.ratio h h' * (backtrackScale G u h' / backtrackScale G u h) := (rfl)

/-- Gauging by pointwise equal labellings gives the same parameter. -/
theorem gauge_congr (c : SkewZigzagParameter k G)
    {u u' : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ}
    (hu : ∀ ⦃x y : DoubledQuiver G⦄ (e : x ⟶ y), u e = u' e) : c.gauge u = c.gauge u' := by
  ext i j j' a b
  rw [gauge_ratio, gauge_ratio, backtrackScale, backtrackScale, backtrackScale, backtrackScale,
    hu, hu, hu, hu]

/-- **Gauging by the constant labelling one changes nothing.** -/
@[simp]
theorem gauge_one (c : SkewZigzagParameter k G) : c.gauge (fun _ _ _ => 1) = c := by
  ext i j j' a b
  rw [gauge_ratio, backtrackScale, backtrackScale, one_mul, div_self', mul_one]

/-- **Gauge transforms compose by multiplying labellings.** -/
theorem gauge_gauge (c : SkewZigzagParameter k G)
    (u u' : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) :
    (c.gauge u).gauge u' = c.gauge (fun _ _ e => u e * u' e) := by
  ext i j j' a b
  rw [gauge_ratio, gauge_ratio, gauge_ratio, mul_assoc, div_mul_div_comm]
  simp only [backtrackScale]
  rw [mul_mul_mul_comm (u (arrow G b)), mul_mul_mul_comm (u (arrow G a))]

/-- **The defining identity of the gauge transform**: multiplying a gauged ratio by the backtrack
scale of its first edge gives the original ratio times the backtrack scale of its second edge. This
is the scalar identity behind gauge independence of the presented algebra: it equates the two ways
of rescaling the backtrack relator of a pair of incident edges. -/
theorem backtrackScale_mul_gauge_ratio (c : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) {i j j' : V} (h : G.Adj i j)
    (h' : G.Adj i j') :
    backtrackScale G u h * (c.gauge u).ratio h h' =
      c.ratio h h' * backtrackScale G u h' := by
  rw [gauge_ratio, mul_left_comm, mul_div_cancel]

/-- **Gauging by the pointwise inverse labelling undoes a gauge transform.** -/
@[simp]
theorem gauge_gauge_inv (c : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) :
    (c.gauge u).gauge (fun _ _ e => (u e)⁻¹) = c := by
  rw [gauge_gauge, gauge_congr c (u' := fun _ _ _ => 1) fun _ _ e => mul_inv_cancel (u e),
    gauge_one]

/-! ### Gauge equivalence -/

/-- Two skew-zigzag parameters are **gauge equivalent** when one is a gauge transform of the other,
that is, when rescaling the arrows of the doubled quiver by units carries the first presentation to
the second. -/
def IsGaugeEquivalent (c c' : SkewZigzagParameter k G) : Prop :=
  ∃ u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ, c' = c.gauge u

/-- Every parameter is gauge equivalent to itself, by the constant labelling one. -/
@[refl]
theorem IsGaugeEquivalent.refl (c : SkewZigzagParameter k G) : IsGaugeEquivalent c c :=
  ⟨fun _ _ _ => 1, (gauge_one c).symm⟩

/-- Gauge equivalence is symmetric: the pointwise inverse labelling gauges back. -/
theorem IsGaugeEquivalent.symm {c c' : SkewZigzagParameter k G} (h : IsGaugeEquivalent c c') :
    IsGaugeEquivalent c' c := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨fun _ _ e => (u e)⁻¹, (gauge_gauge_inv c u).symm⟩

/-- Gauge equivalence is transitive: the pointwise product labelling gauges across. -/
theorem IsGaugeEquivalent.trans {c c' c'' : SkewZigzagParameter k G}
    (h : IsGaugeEquivalent c c') (h' : IsGaugeEquivalent c' c'') : IsGaugeEquivalent c c'' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨u', rfl⟩ := h'
  exact ⟨fun _ _ e => u e * u' e, gauge_gauge c u u'⟩

/-- **Gauge equivalence of skew-zigzag parameters is an equivalence relation.** -/
theorem IsGaugeEquivalent.equivalence :
    Equivalence (IsGaugeEquivalent (k := k) (G := G)) :=
  ⟨IsGaugeEquivalent.refl, IsGaugeEquivalent.symm, IsGaugeEquivalent.trans⟩

end SkewZigzagParameter

/-! ### Gauge independence of the presented algebra -/

section Independence

open SkewZigzagParameter

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- **Rescaling by a unit labelling carries the skew relators of a parameter into the relation ideal
of its gauge transform**: a path relator is multiplied by its path weight, and the backtrack
relator of a pair of incident edges is multiplied by the backtrack scale at the first of them. -/
theorem skewZigzagMk_rescale_eq_zero (c c' : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) (hc : c' = c.gauge u)
    {x : pathAlgebra k (DoubledQuiver G)} (hx : IsSkewZigzagRelator k G c x) :
    skewZigzagMk k G c' (rescale (fun _ _ e => ((u e : kˣ) : k)) x) = 0 := by
  subst hc
  cases hx with
  | nonreturn p hlen hne =>
    rw [rescale_ofPath, map_smul, skewZigzagMk_ofPath_eq_zero_of_ne k G (c.gauge u) p hlen hne,
      smul_zero]
  | backtrack_ratio h h' =>
    have key : backtrackScale G (fun _ _ e => ((u e : kˣ) : k)) h * ((c.gauge u).ratio h h' : k)
        = ((c.ratio h h' : k)) * backtrackScale G (fun _ _ e => ((u e : kˣ) : k)) h' := by
      rw [← val_backtrackScale, ← val_backtrackScale, ← Units.val_mul, ← Units.val_mul,
        backtrackScale_mul_gauge_ratio]
    rw [map_sub, map_smul, rescale_backtrackElem, rescale_backtrackElem, map_sub, map_smul,
      map_smul, map_smul, skewZigzagMk_backtrackElem_eq_smul k G (c.gauge u) h h', smul_smul,
      smul_smul, key, sub_self]
  | long_path y h3 =>
    rw [rescale_ofPath, map_smul,
      skewZigzagMk_ofPath_eq_zero_of_three_le k G (c.gauge u) y h3, smul_zero]

/-- The map of skew relation quotients induced by an arrow rescaling. This is only one direction of
`TauCeti.skewZigzagQuotientGaugeEquiv`, which is the public API; it is private so as not to
duplicate it. -/
private noncomputable def skewZigzagQuotientRescaleHom (c c' : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) (hc : c' = c.gauge u) :
    skewZigzagQuotient k G c →ₐ[k] skewZigzagQuotient k G c' :=
  skewZigzagLift k G c
    ((skewZigzagMk k G c').comp (rescale fun _ _ e => ((u e : kˣ) : k))) fun x hx => by
      rw [AlgHom.comp_apply]
      exact skewZigzagMk_rescale_eq_zero k G c c' u hc hx

/-- The induced map of quotients sends the class of an element to the class of its rescaling. -/
private theorem skewZigzagQuotientRescaleHom_skewZigzagMk (c c' : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) (hc : c' = c.gauge u)
    (x : pathAlgebra k (DoubledQuiver G)) :
    skewZigzagQuotientRescaleHom k G c c' u hc (skewZigzagMk k G c x)
      = skewZigzagMk k G c' (rescale (fun _ _ e => ((u e : kˣ) : k)) x) :=
  skewZigzagLift_skewZigzagMk k G c _ _ x

/-- **Gauge independence of the skew-zigzag relation quotient.** A parameter and its gauge transform
present isomorphic algebras: the isomorphism is the arrow rescaling by the gauging units, which
fixes every vertex idempotent and multiplies each oriented edge by its unit. -/
noncomputable def skewZigzagQuotientGaugeEquiv (c c' : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) (hc : c' = c.gauge u) :
    skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c' :=
  AlgEquiv.ofAlgHom (skewZigzagQuotientRescaleHom k G c c' u hc)
    (skewZigzagQuotientRescaleHom k G c' c (fun _ _ e => (u e)⁻¹) (by rw [hc, gauge_gauge_inv]))
    (Ideal.Quotient.algHom_ext k (AlgHom.ext fun x => by
      have hid : rescale (fun _ _ e => ((u e : kˣ) : k) * (((u e)⁻¹ : kˣ) : k))
          = AlgHom.id k (pathAlgebra k (DoubledQuiver G)) := by
        rw [← rescale_one]
        exact rescale_congr _ _ fun _ _ e => by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hux : rescale (fun _ _ e => ((u e : kˣ) : k))
          (rescale (fun _ _ e => (((u e)⁻¹ : kˣ) : k)) x) = x := by
        rw [← AlgHom.comp_apply, rescale_comp_rescale, hid, AlgHom.id_apply]
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← skewZigzagMk_apply,
        skewZigzagQuotientRescaleHom_skewZigzagMk, AlgHom.id_apply, hux]))
    (Ideal.Quotient.algHom_ext k (AlgHom.ext fun x => by
      have hid : rescale (fun _ _ e => (((u e)⁻¹ : kˣ) : k) * ((u e : kˣ) : k))
          = AlgHom.id k (pathAlgebra k (DoubledQuiver G)) := by
        rw [← rescale_one]
        exact rescale_congr _ _ fun _ _ e => by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hux : rescale (fun _ _ e => (((u e)⁻¹ : kˣ) : k))
          (rescale (fun _ _ e => ((u e : kˣ) : k)) x) = x := by
        rw [← AlgHom.comp_apply, rescale_comp_rescale, hid, AlgHom.id_apply]
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← skewZigzagMk_apply,
        skewZigzagQuotientRescaleHom_skewZigzagMk, AlgHom.id_apply, hux]))

/-- **The gauge isomorphism is the arrow rescaling**: on an arbitrary quotient representative it
rescales and then takes the class in the gauged quotient. -/
@[simp]
theorem skewZigzagQuotientGaugeEquiv_skewZigzagMk (c c' : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) (hc : c' = c.gauge u)
    (x : pathAlgebra k (DoubledQuiver G)) :
    skewZigzagQuotientGaugeEquiv k G c c' u hc (skewZigzagMk k G c x)
      = skewZigzagMk k G c' (rescale (fun _ _ e => ((u e : kˣ) : k)) x) := by
  rw [skewZigzagQuotientGaugeEquiv, ← AlgEquiv.coe_toAlgHom, AlgEquiv.toAlgHom_ofAlgHom,
    skewZigzagQuotientRescaleHom_skewZigzagMk]

/-- **Gauge equivalent parameters present isomorphic algebras.** -/
theorem nonempty_algEquiv_skewZigzagQuotient_of_isGaugeEquivalent
    {c c' : SkewZigzagParameter k G} (h : c.IsGaugeEquivalent c') :
    Nonempty (skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c') := by
  obtain ⟨u, hu⟩ := h
  exact ⟨skewZigzagQuotientGaugeEquiv k G c c' u hu⟩

end Independence

/-! ### Gauge-trivial parameters -/

section One

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- **A gauge-trivial skew-zigzag parameter presents the ordinary zigzag algebra.** Gauge
equivalence is symmetric, so this is the comparison for every parameter in the gauge class of the
constant one. -/
theorem nonempty_algEquiv_nonisolatedZigzagQuotient_of_isGaugeEquivalent_one
    {c : SkewZigzagParameter k G}
    (h : SkewZigzagParameter.IsGaugeEquivalent (1 : SkewZigzagParameter k G) c) :
    Nonempty (skewZigzagQuotient k G c ≃ₐ[k] nonisolatedZigzagQuotient k G) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨(skewZigzagQuotientGaugeEquiv k G 1 _ u rfl).symm.trans (skewZigzagQuotientOneEquiv k G)⟩

end One

end TauCeti
