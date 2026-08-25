/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Pullback
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic

/-!
# Homomorphism densities are invariant under measure-preserving pullback

If `f : Ω' → Ω` pushes a probability measure `ν` forward to `μ`, then a graphon `W` on `(Ω, μ)` and
its pullback `W.comap f` on `(Ω', ν)` have the *same* homomorphism densities:
`t(F, W.comap f) = t(F, W)` for every finite graph `F`.

Unlike the corresponding statement for the cut norm
(`TauCeti.DenseGraphLimits.cutNorm_comap`), no cut-norm estimate or inequality is needed.
The proof is instead a measure-theoretic change-of-variables argument. A homomorphism density is
an integral over vertex assignments `V → Ω`, and postcomposition with
`f` sends assignments upstairs to assignments downstairs; `MeasureTheory.measurePreserving_pi`
says that this coordinatewise map is itself measure preserving for the product measures, and the
integrand transforms along it on the nose, because each edge factor only ever evaluates `W` at
images of the assignment.

This is what makes homomorphism densities a *cross-carrier* observable. Two graphons on different
carriers are compared through a coupling `π`, which reads both as graphons on `(Ω₁ × Ω₂, π)` by
pulling back along the coordinate projections; those projections are measure preserving precisely
because `π` is a coupling, so the pulled-back densities are the original ones. That identification
is the step turning the same-carrier counting lemma into its coupling form,
`TauCeti.DenseGraphLimits.counting_lemma_coupling`.

## Main results

* `TauCeti.DenseGraphLimits.edgeFactor_comap` — an edge factor of a pulled-back graphon is the edge
  factor of the graphon at the postcomposed assignment;
* `TauCeti.DenseGraphLimits.homDensity_comap` — `t(F, W.comap f) = t(F, W)` for a measure-preserving
  `f`.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the basic theory of `homDensity`;
  the invariance recorded here is the transport the cross-carrier Layer-2 counting lemma runs on.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §7 — homomorphism densities of a graphon read through a measure-preserving map.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {V : Type*} [Fintype V]

omit [Fintype V] in
/-- An edge factor of a pulled-back graphon is the edge factor of the original graphon, read at the
postcomposed vertex assignment. -/
@[simp]
theorem edgeFactor_comap (W : Graphon Ω μ) {f : Ω' → Ω} (hf : Measurable f) (x : V → Ω')
    (e : Sym2 V) : edgeFactor (W.comap f hf ν) x e = edgeFactor W (fun i => f (x i)) e := by
  induction e using Sym2.ind with | _ a b => simp

/-- **Homomorphism densities are invariant under measure-preserving pullback.** If `f` pushes `ν`
forward to `μ`, then `t(F, W.comap f) = t(F, W)`.

Postcomposition with `f` is a measure-preserving map `(V → Ω', Πν) → (V → Ω, Πμ)` by
`MeasureTheory.measurePreserving_pi`, and by `edgeFactor_comap` the integrand of the left-hand side
is the integrand of the right-hand side composed with it. -/
@[simp]
theorem homDensity_comap (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {f : Ω' → Ω}
    (hf : MeasurePreserving f ν μ) :
    homDensity F (W.comap f hf.measurable ν) = homDensity F W := by
  have hpi : MeasurePreserving (fun (x : V → Ω') (i : V) => f (x i))
      (Measure.pi fun _ : V => ν) (Measure.pi fun _ : V => μ) :=
    measurePreserving_pi _ _ fun _ => hf
  rw [homDensity_def, homDensity_def, ← hpi.map_eq,
    integral_map hpi.measurable.aemeasurable
      (measurable_prod_edgeFactor F.edgeFinset fun _ => W).aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    Finset.prod_congr rfl fun e _ => edgeFactor_comap W hf.measurable x e)

end DenseGraphLimits

end TauCeti
