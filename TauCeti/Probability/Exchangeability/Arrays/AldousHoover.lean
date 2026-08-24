/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
public import Mathlib.Data.Sym.Sym2
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.Independence.InfinitePi

/-!
# Aldous--Hoover array codings are exchangeable

The functional forms in the Aldous--Hoover representation use four independent kinds of uniform
randomness.  A separately exchangeable array is coded from a global variable, one variable for
each row, one for each column, and one for each cell:

```text
X i j = f(U, U_row i, U_col j, U_cell i j).
```

For a jointly exchangeable array, the row and column variables are replaced by one family of
vertex variables:

```text
X i j = f(U, U_vert i, U_vert j, U_cell {i, j}).
```

This file defines canonical product probability spaces carrying those sources and proves the easy
direction of the Aldous--Hoover representation theorem: every measurable coding of the first form
is separately exchangeable, and every measurable coding of the second form is jointly
exchangeable.  The proof reindexes the independent source family.  Row and column permutations
act on their respective vertex variables and together on the cell variables, while leaving the
global variable fixed.

These results advance the exchangeable-arrays milestone in
`TauCetiRoadmap/Exchangeability/README.md`, Layer 8.  The converse representation direction still
has to construct the coding function from an exchangeable array.

## Main definitions

* `TauCeti.Probability.AldousHoover.Axis` labels the row and column noise families;
* `TauCeti.Probability.AldousHoover.NoiseIndex` indexes global, vertex, and cell noise;
* `TauCeti.Probability.AldousHoover.noiseMeasure` is the corresponding i.i.d. uniform law;
* `TauCeti.Probability.AldousHoover.separateArray` and
  `TauCeti.Probability.AldousHoover.jointArray` are the two coding forms.

## Main results

* `TauCeti.Probability.AldousHoover.separatelyExchangeable_separateArray`;
* `TauCeti.Probability.AldousHoover.jointlyExchangeable_jointArray`.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory unitInterval

namespace TauCeti

namespace Probability

namespace AldousHoover

/-- Indices for the independent noise in an Aldous--Hoover coding.  The parameter `κ` indexes
families of vertex variables, while `ι` indexes the cell variables. -/
inductive NoiseIndex (κ ι : Type*) where
  | global
  | vertex (axis : κ) (i : ℕ)
  | cell (p : ι)

/-- The two vertex-noise families in the separately exchangeable coding. -/
inductive Axis where
  | row
  | column

/-- Reindex Aldous--Hoover noise by a permutation of each vertex family and of the cell indices. -/
def indexEquiv {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ) (cellPerm : ι ≃ ι) :
    NoiseIndex κ ι ≃ NoiseIndex κ ι where
  toFun
    | .global => .global
    | .vertex a i => .vertex a (vertexPerm a i)
    | .cell p => .cell (cellPerm p)
  invFun
    | .global => .global
    | .vertex a i => .vertex a ((vertexPerm a).symm i)
    | .cell p => .cell (cellPerm.symm p)
  left_inv x := by
    cases x <;> simp
  right_inv x := by
    cases x <;> simp

@[simp]
theorem indexEquiv_global {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ)
    (cellPerm : ι ≃ ι) :
    indexEquiv vertexPerm cellPerm (.global : NoiseIndex κ ι) = .global :=
  (rfl)

@[simp]
theorem indexEquiv_vertex {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ) (cellPerm : ι ≃ ι)
    (a : κ) (i : ℕ) :
    indexEquiv vertexPerm cellPerm (.vertex a i) = .vertex a (vertexPerm a i) :=
  (rfl)

@[simp]
theorem indexEquiv_cell {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ)
    (cellPerm : ι ≃ ι) (p : ι) :
    indexEquiv vertexPerm cellPerm (.cell p) = .cell (cellPerm p) :=
  (rfl)

/-- The canonical law of the independent uniform variables used by an Aldous--Hoover coding. -/
def noiseMeasure (κ ι : Type*) : Measure (NoiseIndex κ ι → I) :=
  Measure.infinitePi fun _ => (volume : Measure I)

/-- The canonical Aldous--Hoover noise law is a probability measure. -/
instance instIsProbabilityMeasureNoiseMeasure (κ ι : Type*) :
    IsProbabilityMeasure (noiseMeasure κ ι) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi fun _ : NoiseIndex κ ι => (volume : Measure I)))

/-- Reindex a realization of the Aldous--Hoover noise. -/
def noiseReindex {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ) (cellPerm : ι ≃ ι)
    (u : NoiseIndex κ ι → I) : NoiseIndex κ ι → I :=
  fun q => u (indexEquiv vertexPerm cellPerm q)

@[simp]
theorem noiseReindex_apply {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ) (cellPerm : ι ≃ ι)
    (u : NoiseIndex κ ι → I) (q : NoiseIndex κ ι) :
    noiseReindex vertexPerm cellPerm u q = u (indexEquiv vertexPerm cellPerm q) :=
  (rfl)

/-- Reindexing the noise is measurable. -/
@[fun_prop]
theorem measurable_noiseReindex {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ)
    (cellPerm : ι ≃ ι) :
    Measurable (noiseReindex vertexPerm cellPerm) :=
  measurable_pi_lambda _ fun q =>
    measurable_pi_apply (indexEquiv vertexPerm cellPerm q)

/-- The independent uniform noise law is invariant under reindexing its vertex and cell
coordinates. -/
@[simp]
theorem map_noiseReindex_noiseMeasure {κ : Type*} (vertexPerm : κ → Equiv.Perm ℕ)
    {ι : Type*} (cellPerm : ι ≃ ι) :
    (noiseMeasure κ ι).map (noiseReindex vertexPerm cellPerm) = noiseMeasure κ ι := by
  -- Expose the two wrappers so the generic infinite-product reindexing theorem sees its expected
  -- coordinate projection literally.
  change (Measure.infinitePi fun _ : NoiseIndex κ ι => (volume : Measure I)).map
      (fun u q => u (indexEquiv vertexPerm cellPerm q)) =
    Measure.infinitePi fun _ : NoiseIndex κ ι => (volume : Measure I)
  rw [Measure.map_infinitePi_infinitePi_of_inj
    (indexEquiv vertexPerm cellPerm).injective]

section Codings

variable {α : Type*} [MeasurableSpace α]

/-- The separately exchangeable Aldous--Hoover coding. -/
def separateArray (f : I × I × I × I → α)
    (p : ℕ × ℕ) (u : NoiseIndex Axis (ℕ × ℕ) → I) : α :=
  f (u .global, u (.vertex .row p.1), u (.vertex .column p.2), u (.cell p))

omit [MeasurableSpace α] in
@[simp]
theorem separateArray_apply (f : I × I × I × I → α)
    (p : ℕ × ℕ) (u : NoiseIndex Axis (ℕ × ℕ) → I) :
    separateArray f p u =
      f (u .global, u (.vertex .row p.1), u (.vertex .column p.2), u (.cell p)) :=
  (rfl)

/-- A measurable separate Aldous--Hoover coding is measurable as an array-valued random
variable. -/
theorem measurable_separateArray (f : I × I × I × I → α) (hf : Measurable f) :
    Measurable fun u : NoiseIndex Axis (ℕ × ℕ) → I => fun p => separateArray f p u :=
  measurable_pi_lambda _ fun p => hf.comp
    ((measurable_pi_apply (NoiseIndex.global : NoiseIndex Axis (ℕ × ℕ))).prodMk
      ((measurable_pi_apply (NoiseIndex.vertex Axis.row p.1)).prodMk
        ((measurable_pi_apply (NoiseIndex.vertex Axis.column p.2)).prodMk
          (measurable_pi_apply (NoiseIndex.cell p)))))

/-- **Every measurable separate Aldous--Hoover coding is separately exchangeable.** -/
theorem separatelyExchangeable_separateArray
    (f : I × I × I × I → α) (hf : Measurable f) :
    SeparatelyExchangeable (noiseMeasure Axis (ℕ × ℕ)) (separateArray f) := by
  rw [separatelyExchangeable_iff]
  intro rowPerm colPerm
  let vertexPerm : Axis → Equiv.Perm ℕ
    | .row => rowPerm
    | .column => colPerm
  let cellPerm : ℕ × ℕ ≃ ℕ × ℕ := rowPerm.prodCongr colPerm
  have hcode : Measurable fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
      fun p => separateArray f p u := measurable_separateArray f hf
  have hfun : (fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
      fun p => separateArray f (rowPerm p.1, colPerm p.2) u) =
        (fun u => fun p => separateArray f p u) ∘
          noiseReindex vertexPerm cellPerm := by
    funext u ⟨i, j⟩
    simp [separateArray_apply, Function.comp_apply, vertexPerm, cellPerm]
  rw [hfun, ← Measure.map_map hcode
      (measurable_noiseReindex vertexPerm cellPerm),
    map_noiseReindex_noiseMeasure]

/-- The jointly exchangeable Aldous--Hoover coding, using one common family of vertex variables
for the two axes. -/
def jointArray (f : I × I × I × I → α)
    (p : ℕ × ℕ) (u : NoiseIndex Unit (Sym2 ℕ) → I) : α :=
  f (u .global, u (.vertex () p.1), u (.vertex () p.2), u (.cell s(p.1, p.2)))

omit [MeasurableSpace α] in
@[simp]
theorem jointArray_apply (f : I × I × I × I → α)
    (p : ℕ × ℕ) (u : NoiseIndex Unit (Sym2 ℕ) → I) :
    jointArray f p u =
      f (u .global, u (.vertex () p.1), u (.vertex () p.2), u (.cell s(p.1, p.2))) :=
  (rfl)

/-- A measurable joint Aldous--Hoover coding is measurable as an array-valued random variable. -/
theorem measurable_jointArray (f : I × I × I × I → α) (hf : Measurable f) :
    Measurable fun u : NoiseIndex Unit (Sym2 ℕ) → I => fun p => jointArray f p u :=
  measurable_pi_lambda _ fun p => hf.comp
    ((measurable_pi_apply (NoiseIndex.global : NoiseIndex Unit (Sym2 ℕ))).prodMk
      ((measurable_pi_apply (NoiseIndex.vertex () p.1)).prodMk
        ((measurable_pi_apply (NoiseIndex.vertex () p.2)).prodMk
          (measurable_pi_apply (NoiseIndex.cell s(p.1, p.2))))))

/-- **Every measurable joint Aldous--Hoover coding is jointly exchangeable.** -/
theorem jointlyExchangeable_jointArray
    (f : I × I × I × I → α) (hf : Measurable f) :
    JointlyExchangeable (noiseMeasure Unit (Sym2 ℕ)) (jointArray f) := by
  rw [jointlyExchangeable_iff]
  intro perm
  let vertexPerm : Unit → Equiv.Perm ℕ := fun _ => perm
  let cellPerm : Sym2 ℕ ≃ Sym2 ℕ := {
    toFun := Sym2.map perm
    invFun := Sym2.map perm.symm
    left_inv p := by simp [Sym2.map_map]
    right_inv p := by simp [Sym2.map_map]
  }
  have hcode : Measurable fun u : NoiseIndex Unit (Sym2 ℕ) → I =>
      fun p => jointArray f p u := measurable_jointArray f hf
  have hfun : (fun u : NoiseIndex Unit (Sym2 ℕ) → I =>
      fun p => jointArray f (perm p.1, perm p.2) u) =
        (fun u => fun p => jointArray f p u) ∘ noiseReindex vertexPerm cellPerm := by
    funext u p
    simp [jointArray_apply, Function.comp_apply, vertexPerm, cellPerm]
  rw [hfun, ← Measure.map_map hcode (measurable_noiseReindex vertexPerm cellPerm),
    map_noiseReindex_noiseMeasure]

end Codings

end AldousHoover

end Probability

end TauCeti

end
