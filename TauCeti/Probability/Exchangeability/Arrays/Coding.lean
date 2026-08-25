/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the array symmetry and the inherited invariance of the row mixing law are the
-- hypothesis and the conclusion of the representation.
public import TauCeti.Probability.Exchangeability.Arrays.MixingLaw
-- Public: the coding map and the barycenter identity it satisfies appear in every statement.
public import TauCeti.Probability.DeFinetti.Coding
-- Non-public: the mixture form of a row path law is used only inside proofs.
import TauCeti.Probability.Exchangeability.MixedIID.Mixture

/-!
# The coding representation of a separately exchangeable array

De Finetti's theorem turns an exchangeable sequence into a fixed measurable function of its
directing measure and independent uniform noise (`deFinetti_coding`). This file does the same for
the rows of a **separately exchangeable array**: an array `X : ℕ × ℕ → Ω → α` over a nonempty
standard Borel state space satisfies

```text
X (i, j)  =ᵈ  f P (ϑ i) j,
```

for the canonical coding map `f = unitIntervalCoding (ℕ → α)`, a single random parameter
`P : ProbabilityMeasure (ℕ → α)` drawn from a mixing law `π`, and an independent i.i.d. uniform
sequence `ϑ` carrying one variable per row. All the randomness of the array beyond the global
parameter sits in the per-row noise, which is the shape the Aldous–Hoover representation takes;
the finer resolution of a row path into a per-column and a per-cell source is not carried out
here, and the column symmetry enters only through the invariance of `π`.

That invariance is what makes the representation exact rather than one-directional. The mixing
law of the rows is invariant under pushing a path law forward by a permutation of the time
coordinate (`SeparatelyExchangeable.mixingLaw_map_permReindex_arrayRow_eq`), and, conversely,
coding *any* mixing law with that invariance produces a separately exchangeable array. So over a
nonempty standard Borel state space, separate exchangeability of an array is exactly codability by
a permutation-invariant mixing law (`separatelyExchangeable_iff_exists_coding`).

## Main results

* `TauCeti.Probability.SeparatelyExchangeable.exists_arrayLaw_eq_map_unitIntervalCoding` — **the
  representation**: the law of a separately exchangeable array is the law of the array coded by a
  permutation-invariant mixing law.
* `TauCeti.Probability.separatelyExchangeable_unitIntervalCoding` — the converse: the
  array coded by a permutation-invariant mixing law is separately exchangeable.
* `TauCeti.Probability.separatelyExchangeable_iff_exists_coding` — the resulting
  characterization.

## Implementation

The row process of the coded array is the coded sequence in path space, so its law is the
de Finetti barycenter of the mixing law (`map_prod_unitIntervalCoding_eq_deFinettiBarycenter` at
value space `ℕ → α`). Both array symmetries are therefore read off that barycenter: permuting the
rows is exchangeability of the barycenter (`exchangeableLaw_deFinettiBarycenter`), and permuting
the columns is a coordinatewise pushforward, which by naturality (`map_pi_deFinettiBarycenter`) is
the barycenter of the pushed-forward mixing law. Only the second uses the hypothesis on `π`. The
transport from the row process back to the array is `map_uncurry_pathLaw_arrayRow`, along which
every statement here is read.

The unit interval is written out rather than through the `unitInterval` scoped notation `I`, whose
namespace also carries a `σ` notation that would collide with the permutation names used by the
neighbouring array files.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22, for the coding map.

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable sequences
rather than arrays.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

section Coding

variable [StandardBorelSpace α] [Nonempty α]

/-- The law of the array coded by a parameter and one uniform variable per row, computed through
its row process: it is the uncurried de Finetti barycenter of the parameter law. -/
private theorem map_prod_unitIntervalCoding_array
    (π : Measure (ProbabilityMeasure (ℕ → α))) :
    ((π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
        fun q p => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2)
      = (deFinettiBarycenter π).map Function.uncurry := by
  rw [← map_prod_unitIntervalCoding_eq_deFinettiBarycenter (α := ℕ → α) π,
    Measure.map_map measurable_uncurry (measurable_unitIntervalCodingPath (α := ℕ → α))]
  refine congrArg (Measure.map · _) ?_
  funext q ⟨i, j⟩
  simp

/-- The same computation after reindexing the two axes: permuting the rows reindexes the sequence
of coded paths, and permuting the columns pushes every coded path forward by the time
permutation. -/
private theorem map_prod_unitIntervalCoding_array_pairReindex
    (π : Measure (ProbabilityMeasure (ℕ → α))) (σ τ : Equiv.Perm ℕ) :
    ((π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
        fun q p => unitIntervalCoding (ℕ → α) q.1 (q.2 (σ p.1)) (τ p.2))
      = (((deFinettiBarycenter π).map (permReindex (α := ℕ → α) σ)).map
          fun x i => permReindex (α := α) τ (x i)).map Function.uncurry := by
  have hR := measurable_unitIntervalCodingPath (α := ℕ → α)
  have hS : Measurable (permReindex (α := ℕ → α) σ) := measurable_reindex σ
  have hT : Measurable fun x : ℕ → ℕ → α => fun i => permReindex (α := α) τ (x i) :=
    measurable_pi_lambda _ fun i => (measurable_reindex τ).comp (measurable_pi_apply i)
  rw [← map_prod_unitIntervalCoding_eq_deFinettiBarycenter (α := ℕ → α) π,
    Measure.map_map hS hR, Measure.map_map hT (hS.comp hR),
    Measure.map_map measurable_uncurry (hT.comp (hS.comp hR))]
  refine congrArg (Measure.map · _) ?_
  funext q ⟨i, j⟩
  simp

/-- **Coding a permutation-invariant mixing law gives a separately exchangeable array.** Draw a
path law `P` from `π` and one uniform variable `ϑ i` per row, and let the `(i, j)`-entry be
`unitIntervalCoding (ℕ → α) P (ϑ i) j`. Permuting the rows permutes the i.i.d. noise, so it always
leaves the law alone; permuting the columns pushes `P` forward by that time permutation, so it
leaves the law alone exactly because `π` is invariant under that pushforward. -/
theorem separatelyExchangeable_unitIntervalCoding
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsProbabilityMeasure π]
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (measurable_reindex (α := α) τ).aemeasurable) = π) :
    SeparatelyExchangeable
        (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))
      fun p q => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 := by
  refine separatelyExchangeable_iff.mpr fun σ τ => ?_
  have hrow : (deFinettiBarycenter π).map (permReindex (α := ℕ → α) σ) = deFinettiBarycenter π :=
    (exchangeableLaw_deFinettiBarycenter (π := π)).map_permReindex σ
  have hcol : ((deFinettiBarycenter π).map fun x : ℕ → ℕ → α =>
      fun i => permReindex (α := α) τ (x i)) = deFinettiBarycenter π := by
    have hnat := map_pi_deFinettiBarycenter π (measurable_reindex (α := α) τ)
    rw [hπ τ] at hnat
    exact hnat
  calc ((π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
          fun q p => unitIntervalCoding (ℕ → α) q.1 (q.2 (σ p.1)) (τ p.2))
      = (((deFinettiBarycenter π).map (permReindex (α := ℕ → α) σ)).map
          fun x i => permReindex (α := α) τ (x i)).map Function.uncurry :=
        map_prod_unitIntervalCoding_array_pairReindex π σ τ
    _ = (deFinettiBarycenter π).map Function.uncurry := by rw [hrow, hcol]
    _ = (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
          fun q p => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 :=
        (map_prod_unitIntervalCoding_array π).symm

/-- Every entry of a coded array is measurable in the parameter and the noise. -/
theorem measurable_unitIntervalCoding_entry (p : ℕ × ℕ) :
    Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) =>
      unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 :=
  (measurable_pi_apply p.2).comp ((measurable_uncurry_unitIntervalCoding (ℕ → α)).comp
    (measurable_fst.prodMk ((measurable_pi_apply p.1).comp measurable_snd)))

/-- **The coding representation of a separately exchangeable array.** Over a nonempty standard
Borel state space, the law of a separately exchangeable array is the law of the array coded by a
single random path law `P` and one independent uniform variable per row: the `(i, j)`-entry is
`unitIntervalCoding (ℕ → α) P (ϑ i) j`.

The mixing law `π` of `P` is the law of a directing measure for the row process, and it inherits
the column symmetry as invariance under pushing a path law forward by a time permutation. -/
theorem SeparatelyExchangeable.exists_arrayLaw_eq_map_unitIntervalCoding
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃ π : ProbabilityMeasure (ProbabilityMeasure (ℕ → α)),
      (∀ τ : Equiv.Perm ℕ,
          (π : Measure (ProbabilityMeasure (ℕ → α))).map
            (fun P => P.map (measurable_reindex (α := α) τ).aemeasurable) = π) ∧
        (μ.map fun ω p => X p ω) =
          ((π : Measure (ProbabilityMeasure (ℕ → α))).prod
              (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
            fun q p => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 := by
  obtain ⟨ν, hν, hinv⟩ := h.exists_directing_arrayRow_mixingLaw_invariant hX
  have hν_meas : Measurable ν :=
    (mixedIIDWith_of_conditionallyIIDWith hν).measurable_mixingRepresentative
  have hprob : IsProbabilityMeasure (μ.map ν) :=
    Measure.isProbabilityMeasure_map hν_meas.aemeasurable
  refine ⟨⟨μ.map ν, hprob⟩, fun τ => ?_, ?_⟩
  · have hmap : Measurable fun P : ProbabilityMeasure (ℕ → α) =>
        P.map (measurable_reindex (α := α) τ).aemeasurable :=
      ((Measure.measurable_map _ (measurable_reindex τ)).comp measurable_subtype_coe).subtype_mk
    simp only [ProbabilityMeasure.coe_mk]
    rw [AEMeasurable.map_map_of_aemeasurable hmap.aemeasurable hν_meas.aemeasurable]
    exact hinv τ
  · have hpath : pathLaw μ (arrayRow X) = deFinettiBarycenter (μ.map ν) := by
      rw [deFinettiBarycenter_def]
      exact pathLaw_eq_bind_infinitePi_of_mixedIIDWith
        (mixedIIDWith_of_conditionallyIIDWith hν)
    simp only [ProbabilityMeasure.coe_mk]
    rw [map_prod_unitIntervalCoding_array (μ.map ν), ← hpath, map_uncurry_pathLaw_arrayRow hX]

/-- **Separate exchangeability is exactly codability by a permutation-invariant mixing law.** Over
a nonempty standard Borel state space, an array has the law of a coded array — one random path law
and one independent uniform variable per row — exactly when it is separately exchangeable, the
mixing law being invariant under pushing a path law forward by a time permutation. -/
theorem separatelyExchangeable_iff_exists_coding {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ × ℕ → Ω → α} (hX : ∀ p, AEMeasurable (X p) μ) :
    SeparatelyExchangeable μ X ↔
      ∃ π : ProbabilityMeasure (ProbabilityMeasure (ℕ → α)),
        (∀ τ : Equiv.Perm ℕ,
            (π : Measure (ProbabilityMeasure (ℕ → α))).map
              (fun P => P.map (measurable_reindex (α := α) τ).aemeasurable) = π) ∧
          (μ.map fun ω p => X p ω) =
            ((π : Measure (ProbabilityMeasure (ℕ → α))).prod
                (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
              fun q p => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 := by
  refine ⟨fun h => h.exists_arrayLaw_eq_map_unitIntervalCoding hX, ?_⟩
  rintro ⟨π, hπ, hlaw⟩
  have : IsProbabilityMeasure (π : Measure (ProbabilityMeasure (ℕ → α))) := π.2
  have hcoded := separatelyExchangeable_unitIntervalCoding
    (π : Measure (ProbabilityMeasure (ℕ → α))) hπ
  rw [separatelyExchangeable_iff_map_pairReindex
    fun p => (measurable_unitIntervalCoding_entry p).aemeasurable] at hcoded
  rw [separatelyExchangeable_iff_map_pairReindex hX]
  simp only [hlaw]
  exact hcoded

end Coding

end Probability

end TauCeti
