/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.CutNorm
public import TauCeti.MeasureTheory.Integral.Pi

/-!
# The counting lemma

The **counting lemma** bounds the gap between the homomorphism densities of a finite graph `F` in
two graphons on one carrier by the cut norm of their difference:

`|t(F, U) - t(F, W)| ≤ e(F) · ‖U - W‖□`.

It is what makes the cut norm the right notion of distance for dense graph limits: the graph
observables `t(F, ·)` are Lipschitz in it, uniformly in everything but the number of edges of `F`.

**The proof is a telescope over the edges.** Swap the edges of `F` from `W` to `U` one at a time.
Each swap changes the integrand at a single edge `e₀ = s(a, b)`, weighted by the product of edge
factors over the *other* edges of `F`; the gap it contributes is bounded by `‖U - W‖□`, and there
are `e(F)` swaps. The hybrid stage is indexed by a subset `D` of the edges — the edges already
swapped — so the induction runs over `D` with the ambient edge set `E` fixed. That is the shape the
argument needs: an induction on `E` alone would have to carry the already-fixed edge factor of the
edge being peeled off, which is exactly the weight the single-edge bound consumes.

**One swap is a rectangle test.** `F` is a *simple* graph, so no edge other than `e₀` joins `a` to
`b`: every other edge misses `a`, or misses `b`, or both. Refreshing the two coordinates `a` and `b`
(`TauCeti.integral_pi_eq_integral_integral_update`) therefore leaves an inner double
integral whose weights *factor* — one `[0, 1]`-valued function of the new `a`-coordinate, one of the
new `b`-coordinate — and `abs_testIntegral_le_cutNorm` bounds such a pairing by the cut norm, with
no loss of constant. The outer integral is over a probability measure, so the bound survives it.

## Main results

* `TauCeti.DenseGraphLimits.counting_lemma` — the forward counting lemma
  `|t(F, U) - t(F, W)| ≤ e(F) · ‖U - W‖□`.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 2 — the forward counting lemma; the
  signature follows `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`. The cross-carrier coupling
  form `counting_lemma_coupling`, the descent `homDensityOnSpace` to `GraphonSpace`, weak
  regularity and total boundedness are separate targets and are not built here.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Lemma 10.23.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 7.2.
-/

public section

noncomputable section

open Function MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {V : Type*} [Fintype V] [DecidableEq V]

/-- **The analytic core of one swap.** If refreshing the two distinct coordinates `a` and `b`
factors the integrand as `p z u * q z t * K u t` with `[0, 1]`-valued weights, then the integral is
bounded by the cut norm of `K`: the inner double integral is a `[0, 1]`-test pairing, and the outer
integral averages over a probability measure. -/
private theorem abs_integral_le_cutNorm_of_factors (K : SymmKernel Ω μ) {a b : V} (hab : a ≠ b)
    (f : (V → Ω) → ℝ) (hf : Integrable f (Measure.pi fun _ : V => μ))
    (p q : (V → Ω) → Ω → ℝ) (hpm : ∀ z, Measurable (p z)) (hqm : ∀ z, Measurable (q z))
    (hp1 : ∀ z u, p z u ∈ Icc (0 : ℝ) 1) (hq1 : ∀ z t, q z t ∈ Icc (0 : ℝ) 1)
    (hfac : ∀ z u t, f (update (update z a u) b t) = p z u * q z t * K u t) :
    |∫ x, f x ∂(Measure.pi fun _ : V => μ)| ≤ cutNorm μ K := by
  rw [TauCeti.integral_pi_eq_integral_integral_update (fun _ : V => μ) hab hf]
  have hbound : ∀ z : V → Ω,
      ‖∫ w : Ω × Ω, f (update (update z a w.1) b w.2) ∂μ.prod μ‖ ≤ cutNorm μ K := by
    intro z
    have hinner : (∫ w : Ω × Ω, f (update (update z a w.1) b w.2) ∂μ.prod μ)
        = K.testIntegral μ (p z) (q z) := by
      rw [SymmKernel.testIntegral_def]
      exact integral_congr_ae (ae_of_all _ fun w => hfac z w.1 w.2)
    rw [Real.norm_eq_abs, hinner]
    exact abs_testIntegral_le_cutNorm μ K (hpm z) (hqm z) (hp1 z) (hq1 z)
  have h := norm_integral_le_of_norm_le_const
    (μ := Measure.pi fun _ : V => μ) (ae_of_all _ hbound)
  simpa [Real.norm_eq_abs] using h

/-- **The single-edge bound, with the edge spelled out.** The difference of two graphons at the edge
`s(a, b)`, weighted by edge factors over any finite family of *other* edges, integrates to at most
the cut norm of the difference.

Every other edge misses `a` or misses `b` — it cannot contain both, since it would then *be*
`s(a, b)` — so, once the coordinates `a` and `b` are refreshed, the weight splits into a function of
the new `a`-coordinate times a function of the new `b`-coordinate. -/
private theorem abs_integral_prod_mul_sub_le_aux (E : Finset (Sym2 V)) (G : Sym2 V → Graphon Ω μ)
    (U W : Graphon Ω μ) {a b : V} (hab : a ≠ b) :
    |∫ x, (∏ e ∈ E.erase s(a, b), edgeFactor (G e) x e)
        * (U (x a) (x b) - W (x a) (x b)) ∂(Measure.pi fun _ : V => μ)|
      ≤ cutNorm μ (U.toSymmKernel - W.toSymmKernel) := by
  -- the edges other than `s(a, b)`, split by whether they contain `b`
  have hmem_b : ∀ e ∈ (E.erase s(a, b)).filter (fun e => b ∉ e), b ∉ e := by
    intro e he
    exact (Finset.mem_filter.1 he).2
  have hmem_a : ∀ e ∈ (E.erase s(a, b)).filter (fun e => ¬ b ∉ e), a ∉ e := by
    intro e he
    obtain ⟨heE, hb⟩ := Finset.mem_filter.1 he
    rw [not_not] at hb
    intro ha
    exact Finset.ne_of_mem_erase heE ((Sym2.mem_and_mem_iff hab).1 ⟨ha, hb⟩)
  refine abs_integral_le_cutNorm_of_factors (U.toSymmKernel - W.toSymmKernel) hab _ ?_
    (fun z u => ∏ e ∈ (E.erase s(a, b)).filter (fun e => b ∉ e),
      edgeFactor (G e) (update z a u) e)
    (fun z t => ∏ e ∈ (E.erase s(a, b)).filter (fun e => ¬ b ∉ e),
      edgeFactor (G e) (update z b t) e)
    (fun z => (measurable_prod_edgeFactor _ G).comp (measurable_update z))
    (fun z => (measurable_prod_edgeFactor _ G).comp (measurable_update z))
    (fun z u => ⟨prod_edgeFactor_nonneg _ G _, prod_edgeFactor_le_one _ G _⟩)
    (fun z t => ⟨prod_edgeFactor_nonneg _ G _, prod_edgeFactor_le_one _ G _⟩) ?_
  · -- integrability: reuse the integrable edge-factor product and bound the difference by `1`
    have hm : Measurable fun x : V → Ω => U (x a) (x b) - W (x a) (x b) := by
      convert (measurable_edgeFactor U s(a, b)).sub (measurable_edgeFactor W s(a, b)) using 1
      funext x
      rw [Pi.sub_apply, edgeFactor_mk, edgeFactor_mk]
    refine (integrable_prod_edgeFactor (E.erase s(a, b)) G).mul_bdd (c := 1)
      hm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have h2 : |U (x a) (x b) - W (x a) (x b)| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [U.nonneg (x a) (x b), W.le_one (x a) (x b)],
        by linarith [U.le_one (x a) (x b), W.nonneg (x a) (x b)]⟩
    simpa only [edgeFactor_mk, Real.norm_eq_abs] using h2
  · -- the factorisation after refreshing the two coordinates
    intro z u t
    have hva : update (update z a u) b t a = u := by
      rw [update_of_ne hab t (update z a u), update_self a u z]
    have hvb : update (update z a u) b t b = t := update_self b t (update z a u)
    have hsplit : (∏ e ∈ E.erase s(a, b), edgeFactor (G e) (update (update z a u) b t) e)
        = (∏ e ∈ (E.erase s(a, b)).filter (fun e => b ∉ e),
            edgeFactor (G e) (update z a u) e)
          * ∏ e ∈ (E.erase s(a, b)).filter (fun e => ¬ b ∉ e),
              edgeFactor (G e) (update z b t) e := by
      rw [← Finset.prod_filter_mul_prod_filter_not (E.erase s(a, b)) (fun e => b ∉ e)]
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun e he => ?_)
        (Finset.prod_congr rfl fun e he => ?_)
      · refine edgeFactor_congr (G e) fun v hv => ?_
        have hvb' : v ≠ b := by rintro rfl; exact hmem_b e he hv
        exact update_of_ne hvb' t (update z a u)
      · refine edgeFactor_congr (G e) fun v hv => ?_
        have hva' : v ≠ a := by rintro rfl; exact hmem_a e he hv
        by_cases hvb' : v = b
        · subst hvb'
          rw [update_self, update_self]
        · rw [update_of_ne hvb' t (update z a u), update_of_ne hva' u z,
            update_of_ne hvb' t z]
    -- `(U - W) u t` is the pointwise difference, by construction of the kernel module structure
    have hK : (U.toSymmKernel - W.toSymmKernel) u t = U u t - W u t := by
      simp [SymmKernel.coe_sub]
    rw [hsplit, hva, hvb, hK]

/-- **The single-edge bound.** The same statement with the swapped edge given as a non-diagonal
`Sym2` element, which is how the telescope below meets it. -/
private theorem abs_integral_prod_mul_sub_le (E : Finset (Sym2 V)) (G : Sym2 V → Graphon Ω μ)
    (U W : Graphon Ω μ) (e₀ : Sym2 V) (he₀ : ¬ e₀.IsDiag) :
    |∫ x, (∏ e ∈ E.erase e₀, edgeFactor (G e) x e)
        * (edgeFactor U x e₀ - edgeFactor W x e₀) ∂(Measure.pi fun _ : V => μ)|
      ≤ cutNorm μ (U.toSymmKernel - W.toSymmKernel) := by
  revert he₀
  induction e₀ using Sym2.ind with
  | _ a b =>
    intro he₀
    have hab : a ≠ b := fun h => he₀ (Sym2.mk_isDiag_iff.2 h)
    simpa only [edgeFactor_mk] using abs_integral_prod_mul_sub_le_aux E G U W hab

/-- **The telescope.** Swapping the edges in a subset `D` of `E` from `W` to `U`, one edge at a
time, costs at most `‖U - W‖□` per swap. -/
private theorem abs_integral_hybrid_sub_le (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (U W : Graphon Ω μ) (D : Finset (Sym2 V)) : D ⊆ E →
    |(∫ x, ∏ e ∈ E, edgeFactor (if e ∈ D then U else W) x e ∂(Measure.pi fun _ : V => μ))
        - ∫ x, ∏ e ∈ E, edgeFactor W x e ∂(Measure.pi fun _ : V => μ)|
      ≤ D.card * cutNorm μ (U.toSymmKernel - W.toSymmKernel) := by
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | @insert e₀ D' he₀D' ih =>
    intro hsub
    have he₀E : e₀ ∈ E := hsub (Finset.mem_insert_self e₀ D')
    have hD'E : D' ⊆ E := (Finset.subset_insert _ _).trans hsub
    have key : ∀ x : V → Ω,
        (∏ e ∈ E, edgeFactor (if e ∈ insert e₀ D' then U else W) x e)
          - (∏ e ∈ E, edgeFactor (if e ∈ D' then U else W) x e)
        = (∏ e ∈ E.erase e₀, edgeFactor (if e ∈ D' then U else W) x e)
            * (edgeFactor U x e₀ - edgeFactor W x e₀) := by
      intro x
      rw [← Finset.prod_erase_mul E
          (fun e => edgeFactor (if e ∈ insert e₀ D' then U else W) x e) he₀E,
        ← Finset.prod_erase_mul E (fun e => edgeFactor (if e ∈ D' then U else W) x e) he₀E]
      have hcongr : ∀ e ∈ E.erase e₀,
          edgeFactor (if e ∈ insert e₀ D' then U else W) x e
            = edgeFactor (if e ∈ D' then U else W) x e := by
        intro e he
        have hmem : (e ∈ insert e₀ D') ↔ e ∈ D' := by
          simp [Finset.mem_insert, Finset.ne_of_mem_erase he]
        simp only [hmem]
      rw [Finset.prod_congr rfl hcongr]
      have h1 : (if e₀ ∈ insert e₀ D' then U else W) = U := by simp
      have h2 : (if e₀ ∈ D' then U else W) = W := by simp [he₀D']
      rw [h1, h2]
      ring
    have hstep :
        |(∫ x, ∏ e ∈ E, edgeFactor (if e ∈ insert e₀ D' then U else W) x e
              ∂(Measure.pi fun _ : V => μ))
            - ∫ x, ∏ e ∈ E, edgeFactor (if e ∈ D' then U else W) x e
              ∂(Measure.pi fun _ : V => μ)|
          ≤ cutNorm μ (U.toSymmKernel - W.toSymmKernel) := by
      rw [← integral_sub (integrable_prod_edgeFactor E _) (integrable_prod_edgeFactor E _)]
      have hfun : (fun x : V → Ω =>
            (∏ e ∈ E, edgeFactor (if e ∈ insert e₀ D' then U else W) x e)
              - ∏ e ∈ E, edgeFactor (if e ∈ D' then U else W) x e)
          = fun x : V → Ω => (∏ e ∈ E.erase e₀, edgeFactor (if e ∈ D' then U else W) x e)
              * (edgeFactor U x e₀ - edgeFactor W x e₀) := funext key
      rw [hfun]
      exact abs_integral_prod_mul_sub_le E _ U W e₀ (hE e₀ he₀E)
    have htri := abs_sub_le
      (∫ x, ∏ e ∈ E, edgeFactor (if e ∈ insert e₀ D' then U else W) x e
        ∂(Measure.pi fun _ : V => μ))
      (∫ x, ∏ e ∈ E, edgeFactor (if e ∈ D' then U else W) x e
        ∂(Measure.pi fun _ : V => μ))
      (∫ x, ∏ e ∈ E, edgeFactor W x e ∂(Measure.pi fun _ : V => μ))
    have hcard : ((insert e₀ D').card : ℝ) = D'.card + 1 := by
      rw [Finset.card_insert_of_notMem he₀D']
      push_cast
      ring
    rw [hcard]
    linarith [htri, hstep, ih hD'E]

omit [DecidableEq V] in
/-- **The counting lemma.** The homomorphism densities of a finite graph `F` in two graphons on one
carrier differ by at most `e(F)` times the cut norm of their difference. The argument to `cutNorm`
is the *kernel* `U - W`: a difference of graphons is not a graphon, which is exactly why the cut
norm is defined on symmetric kernels. -/
theorem counting_lemma (F : SimpleGraph V) [DecidableRel F.Adj] (U W : Graphon Ω μ) :
    |homDensity F U - homDensity F W|
      ≤ (F.edgeFinset.card : ℝ) * cutNorm μ (U.toSymmKernel - W.toSymmKernel) := by
  classical
  have hE : ∀ e ∈ F.edgeFinset, ¬ e.IsDiag := fun _ he =>
    SimpleGraph.not_isDiag_of_mem_edgeFinset he
  have h := abs_integral_hybrid_sub_le F.edgeFinset hE U W F.edgeFinset Finset.Subset.rfl
  have hrw : (∫ x, ∏ e ∈ F.edgeFinset, edgeFactor (if e ∈ F.edgeFinset then U else W) x e
        ∂(Measure.pi fun _ : V => μ))
      = ∫ x, ∏ e ∈ F.edgeFinset, edgeFactor U x e ∂(Measure.pi fun _ : V => μ) :=
    integral_congr_ae (ae_of_all _ fun x => Finset.prod_congr rfl fun e he => by simp [he])
  rw [hrw] at h
  rw [homDensity_def, homDensity_def]
  exact h

end DenseGraphLimits

end TauCeti
