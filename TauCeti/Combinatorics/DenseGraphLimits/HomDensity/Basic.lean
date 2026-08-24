/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Homomorphism densities of a graphon

The homomorphism density `t(F, W)` of a finite graph `F` in a graphon `W`: integrate, over all maps
`x : V(F) → Ω`, the product of `W` along the edges of `F`.

```text
t(F, W) = ∫ ∏_{e ∈ E(F)} W (x eᵢ) (x eⱼ) dμ^{V(F)}
```

**Edges are `Sym2`, and no orientation is chosen.** An edge of a `SimpleGraph` is a `Sym2` element,
with no distinguished endpoint. Rather than pick a representative, `edgeFactor` is built with
`Sym2.lift` from the symmetric function `fun a b => W (x a) (x b)` — symmetric exactly because a
graphon is. Choosing an orientation would work numerically but would leave every later proof
carrying a well-definedness obligation that the `Sym2.lift` formulation discharges once.

**The empty cases are not special-cased.** The empty product is `1`, and the probability-measure
instance for `Measure.pi` makes its integral `1`, including when the vertex type is empty. Nothing
here needs a nonempty-carrier hypothesis.

## Main definitions

* `TauCeti.DenseGraphLimits.edgeFactor` — the value of `W` on one edge, orientation-free;
* `TauCeti.DenseGraphLimits.homDensity` — the density `t(F, W)`.

## Main results

* `edgeFactor_congr` — an edge factor depends only on the assignment along that edge;
* `measurable_prod_edgeFactor`, `prod_edgeFactor_nonneg`, `prod_edgeFactor_le_one` and
  `integrable_prod_edgeFactor` — the basic analytic facts about a finite product of edge factors,
  each edge read in its own graphon.  The integrand of `homDensity` is the special case of one
  graphon on the edges of `F`, and the telescoping proof of the counting lemma needs the general
  form;
* `homDensity_nonneg`, `homDensity_le_one` — `t(F, W) ∈ [0, 1]`, with no hypotheses;
* `homDensity_const` — the Erdős–Rényi value `t(F, W_p) = p ^ e(F)`, the first real consumer of both
  the graphon carrier and this definition.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — `homDensity` and the
  constant-graphon value. The counting lemmas, `cutNorm`, finite-graph compatibility with
  `homDensityFin`, disjoint-union multiplicativity, and the catalogue of small-graph integrals are
  separate targets and are not built here.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.2.
-/

public section

noncomputable section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {V : Type*} [Fintype V]

/-- The value of a graphon on a single edge, as a function of the vertex assignment.

Built with `Sym2.lift` from `fun a b => W (x a) (x b)`, which is symmetric because `W` is, so no
orientation of the edge is chosen. -/
def edgeFactor (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun a b => W (x a) (x b), fun a b => W.symm (x a) (x b)⟩ e

omit [Fintype V] in
@[simp]
theorem edgeFactor_mk (W : Graphon Ω μ) (x : V → Ω) (a b : V) :
    edgeFactor W x s(a, b) = W (x a) (x b) := (rfl)

omit [Fintype V] in
/-- Each edge factor is nonnegative, since a graphon is. -/
theorem edgeFactor_nonneg (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) : 0 ≤ edgeFactor W x e := by
  induction e using Sym2.ind with | _ a b => exact W.nonneg _ _

omit [Fintype V] in
/-- Each edge factor is at most `1`, since a graphon is. -/
theorem edgeFactor_le_one (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) : edgeFactor W x e ≤ 1 := by
  induction e using Sym2.ind with | _ a b => exact W.le_one _ _

omit [Fintype V] in
/-- Each edge factor depends measurably on the vertex assignment. -/
theorem measurable_edgeFactor (W : Graphon Ω μ) (e : Sym2 V) :
    Measurable fun x : V → Ω => edgeFactor W x e := by
  induction e using Sym2.ind with
  | _ a b =>
    have h : Measurable fun x : V → Ω => (x a, x b) :=
      (measurable_pi_apply a).prodMk (measurable_pi_apply b)
    exact W.measurable.comp h

omit [Fintype V] in
/-- The value of a graphon on an edge depends only on the vertex assignment along that edge.  This
is what lets an edge factor be read off after the assignment has been altered away from the edge. -/
theorem edgeFactor_congr (W : Graphon Ω μ) {x y : V → Ω} {e : Sym2 V}
    (h : ∀ v ∈ e, x v = y v) : edgeFactor W x e = edgeFactor W y e := by
  induction e using Sym2.ind with
  | _ a b => rw [edgeFactor_mk, edgeFactor_mk, h a (by simp), h b (by simp)]

omit [Fintype V] in
/-- A finite product of edge factors, each edge read in its own graphon, depends measurably on the
vertex assignment. -/
theorem measurable_prod_edgeFactor (E : Finset (Sym2 V)) (G : Sym2 V → Graphon Ω μ) :
    Measurable fun x : V → Ω => ∏ e ∈ E, edgeFactor (G e) x e :=
  Finset.measurable_prod _ fun e _ => measurable_edgeFactor (G e) e

omit [Fintype V] in
/-- A finite product of edge factors is nonnegative. -/
theorem prod_edgeFactor_nonneg (E : Finset (Sym2 V)) (G : Sym2 V → Graphon Ω μ) (x : V → Ω) :
    0 ≤ ∏ e ∈ E, edgeFactor (G e) x e :=
  Finset.prod_nonneg fun e _ => edgeFactor_nonneg (G e) x e

omit [Fintype V] in
/-- A finite product of edge factors is at most `1`: every factor lies in `[0, 1]`. -/
theorem prod_edgeFactor_le_one (E : Finset (Sym2 V)) (G : Sym2 V → Graphon Ω μ) (x : V → Ω) :
    ∏ e ∈ E, edgeFactor (G e) x e ≤ 1 :=
  Finset.prod_le_one (fun e _ => edgeFactor_nonneg (G e) x e)
    fun e _ => edgeFactor_le_one (G e) x e

/-- A finite product of edge factors is integrable against the product measure: it is measurable
and `[0, 1]`-valued on a probability space. -/
theorem integrable_prod_edgeFactor (E : Finset (Sym2 V)) (G : Sym2 V → Graphon Ω μ) :
    Integrable (fun x : V → Ω => ∏ e ∈ E, edgeFactor (G e) x e)
      (Measure.pi fun _ : V => μ) := by
  refine Integrable.mono' (integrable_const 1)
    (measurable_prod_edgeFactor E G).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (prod_edgeFactor_nonneg E G x)]
  exact prod_edgeFactor_le_one E G x

/-- The **homomorphism density** `t(F, W)`: the integral, over vertex assignments, of the product of
`W` along the edges of `F`.

Outside this module, use `homDensity_def` to unfold `homDensity`; its definition is intentionally
not exposed across module boundaries. -/
def homDensity (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) : ℝ :=
  ∫ x, ∏ e ∈ F.edgeFinset, edgeFactor W x e ∂(Measure.pi fun _ : V => μ)

variable (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ)

/-- The defining integral of `homDensity`.

Outside this module, use this to unfold `homDensity`; its definition is intentionally not exposed
across module boundaries, so `rfl` will not do it. -/
theorem homDensity_def :
    homDensity F W =
      ∫ x, ∏ e ∈ F.edgeFinset, edgeFactor W x e ∂(Measure.pi fun _ : V => μ) := (rfl)

/-- The integrand of `homDensity` is nonnegative. -/
theorem homDensity_integrand_nonneg (x : V → Ω) :
    0 ≤ ∏ e ∈ F.edgeFinset, edgeFactor W x e :=
  prod_edgeFactor_nonneg F.edgeFinset (fun _ => W) x

/-- The integrand of `homDensity` is at most `1`: it is a product of factors in `[0, 1]`. -/
theorem homDensity_integrand_le_one (x : V → Ω) :
    ∏ e ∈ F.edgeFinset, edgeFactor W x e ≤ 1 :=
  prod_edgeFactor_le_one F.edgeFinset (fun _ => W) x

/-- The integrand of `homDensity` is integrable: it is measurable and bounded on a probability
space. -/
theorem integrable_homDensity_integrand :
    Integrable (fun x : V → Ω => ∏ e ∈ F.edgeFinset, edgeFactor W x e)
      (Measure.pi fun _ : V => μ) :=
  integrable_prod_edgeFactor F.edgeFinset fun _ => W

/-- A homomorphism density is nonnegative. -/
theorem homDensity_nonneg : 0 ≤ homDensity F W :=
  integral_nonneg fun x => homDensity_integrand_nonneg F W x

/-- A homomorphism density is at most `1`. -/
theorem homDensity_le_one : homDensity F W ≤ 1 := by
  have h : homDensity F W ≤ ∫ _ : V → Ω, (1 : ℝ) ∂(Measure.pi fun _ : V => μ) :=
    integral_mono (integrable_homDensity_integrand F W) (integrable_const 1)
      fun x => homDensity_integrand_le_one F W x
  simpa using h

/-- **The Erdős–Rényi value.** The constant graphon with parameter `p` has
`t(F, W_p) = p ^ e(F)`. -/
@[simp]
theorem homDensity_const (p : I) :
    homDensity F (Graphon.const μ p) = (p : ℝ) ^ F.edgeFinset.card := by
  have hfac : ∀ (x : V → Ω) (e : Sym2 V), edgeFactor (Graphon.const μ p) x e = (p : ℝ) := by
    intro x e
    induction e using Sym2.ind with | _ a b => exact Graphon.const_apply μ p (x a) (x b)
  have : (fun x : V → Ω => ∏ e ∈ F.edgeFinset, edgeFactor (Graphon.const μ p) x e)
      = fun _ => (p : ℝ) ^ F.edgeFinset.card := by
    funext x
    rw [Finset.prod_congr rfl fun e _ => hfac x e, Finset.prod_const]
  rw [homDensity, this]
  simp

end DenseGraphLimits

end TauCeti
