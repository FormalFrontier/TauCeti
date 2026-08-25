/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Dissociated
public import Mathlib.Data.Sym.Sym2
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Independence.InfinitePi

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

Dropping the global variable — that is, coding through a function `f` that ignores its first
argument — gives the **ergodic form** of the representation, and the arrays it produces are
*dissociated* as well as exchangeable: two blocks over disjoint row sets and disjoint column sets
read disjoint sets of noise coordinates once the global one is out of the way, and the noise
coordinates are independent.  This is the easy direction of the ergodic form of the theorem.  The
global variable is exactly what dissociation forbids, by
`JointlyDissociated.measure_preimage_eq_zero_or_one_of_const`.

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
* `TauCeti.Probability.AldousHoover.jointlyExchangeable_jointArray`;
* `TauCeti.Probability.AldousHoover.separatelyDissociated_separateArray_of_snd`;
* `TauCeti.Probability.AldousHoover.jointlyDissociated_jointArray_of_snd`.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

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

/-- Each coordinate of the canonical Aldous--Hoover noise law is uniform on the unit interval. -/
@[simp]
theorem map_eval_noiseMeasure {κ ι : Type*} (q : NoiseIndex κ ι) :
    (noiseMeasure κ ι).map (fun u => u q) = (volume : Measure I) :=
  Measure.infinitePi_map_eval _ q

/-- The coordinates of the canonical Aldous--Hoover noise law are independent. -/
theorem iIndepFun_eval_noiseMeasure (κ ι : Type*) :
    iIndepFun (fun (q : NoiseIndex κ ι) u => u q) (noiseMeasure κ ι) :=
  iIndepFun_infinitePi (X := fun _ u => u) fun _ => measurable_id

/-- Reindexing a realization of the Aldous--Hoover noise by a permutation of each vertex family
and of the cell indices, as a measurable equivalence. -/
abbrev noiseCongr {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ) (cellPerm : ι ≃ ι) :
    (NoiseIndex κ ι → I) ≃ᵐ (NoiseIndex κ ι → I) :=
  MeasurableEquiv.piCongrLeft (fun _ => I) (indexEquiv vertexPerm cellPerm).symm

@[simp]
theorem noiseCongr_apply {κ ι : Type*} (vertexPerm : κ → Equiv.Perm ℕ) (cellPerm : ι ≃ ι)
    (u : NoiseIndex κ ι → I) (q : NoiseIndex κ ι) :
    noiseCongr vertexPerm cellPerm u q = u (indexEquiv vertexPerm cellPerm q) := by
  simp [noiseCongr, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- The independent uniform noise law is invariant under reindexing its vertex and cell
coordinates. -/
@[simp]
theorem map_noiseCongr_noiseMeasure {κ : Type*} (vertexPerm : κ → Equiv.Perm ℕ)
    {ι : Type*} (cellPerm : ι ≃ ι) :
    (noiseMeasure κ ι).map (noiseCongr vertexPerm cellPerm) = noiseMeasure κ ι :=
  Measure.infinitePi_map_piCongrLeft (fun _ => (volume : Measure I))
    (indexEquiv vertexPerm cellPerm).symm

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
          noiseCongr vertexPerm cellPerm := by
    funext u ⟨i, j⟩
    simp [separateArray_apply, Function.comp_apply, vertexPerm, cellPerm]
  rw [hfun, ← Measure.map_map hcode (noiseCongr vertexPerm cellPerm).measurable,
    map_noiseCongr_noiseMeasure]

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
        (fun u => fun p => jointArray f p u) ∘ noiseCongr vertexPerm cellPerm := by
    funext u p
    simp [jointArray_apply, Function.comp_apply, vertexPerm, cellPerm]
  rw [hfun, ← Measure.map_map hcode (noiseCongr vertexPerm cellPerm).measurable,
    map_noiseCongr_noiseMeasure]

end Codings

section Dissociation

variable {α : Type*} [MeasurableSpace α]

/-- A noise coordinate in a block is measurable for the σ-algebra that block generates. This
restates `measurable_blockSigma_of_mem` with the coordinate family spelled out, which is what fixes
it for unification. -/
private theorem measurable_eval_blockSigma {κ ι : Type*} {S : Set (NoiseIndex κ ι)}
    {q : NoiseIndex κ ι} (hq : q ∈ S) :
    Measurable[blockSigma (fun (r : NoiseIndex κ ι) (u : NoiseIndex κ ι → I) => u r) S]
      fun u : NoiseIndex κ ι → I => u q :=
  measurable_blockSigma_of_mem
    (Z := fun (r : NoiseIndex κ ι) (u : NoiseIndex κ ι → I) => u r) hq

/-- The noise coordinates that the rectangular block along `e` and `f` of a separate
Aldous--Hoover coding reads, with the global coordinate left out. -/
private def separateBlockNoise (e f : ℕ → ℕ) : Set (NoiseIndex Axis (ℕ × ℕ)) := fun q =>
  match q with
  | .global => False
  | .vertex .row i => i ∈ Set.range e
  | .vertex .column j => j ∈ Set.range f
  | .cell p => p.1 ∈ Set.range e ∧ p.2 ∈ Set.range f

private theorem mem_separateBlockNoise_global_iff {e f : ℕ → ℕ} :
    (NoiseIndex.global : NoiseIndex Axis (ℕ × ℕ)) ∈ separateBlockNoise e f ↔ False :=
  (Iff.rfl)

private theorem mem_separateBlockNoise_row_iff {e f : ℕ → ℕ} {i : ℕ} :
    (NoiseIndex.vertex Axis.row i : NoiseIndex Axis (ℕ × ℕ)) ∈ separateBlockNoise e f ↔
      i ∈ Set.range e :=
  (Iff.rfl)

private theorem mem_separateBlockNoise_column_iff {e f : ℕ → ℕ} {j : ℕ} :
    (NoiseIndex.vertex Axis.column j : NoiseIndex Axis (ℕ × ℕ)) ∈ separateBlockNoise e f ↔
      j ∈ Set.range f :=
  (Iff.rfl)

private theorem mem_separateBlockNoise_cell_iff {e f : ℕ → ℕ} {p : ℕ × ℕ} :
    (NoiseIndex.cell p : NoiseIndex Axis (ℕ × ℕ)) ∈ separateBlockNoise e f ↔
      p.1 ∈ Set.range e ∧ p.2 ∈ Set.range f :=
  (Iff.rfl)

/-- Blocks over disjoint row sets and disjoint column sets read disjoint noise coordinates. The
global coordinate, which every block would read, is the only obstruction, and it has been removed
from `separateBlockNoise`. -/
private theorem disjoint_separateBlockNoise {e f e' f' : ℕ → ℕ}
    (he : Disjoint (Set.range e) (Set.range e')) (hf : Disjoint (Set.range f) (Set.range f')) :
    Disjoint (separateBlockNoise e f) (separateBlockNoise e' f') := by
  rw [Set.disjoint_left]
  rintro (_ | ⟨_ | _, i⟩ | p) hq hq'
  · exact mem_separateBlockNoise_global_iff.mp hq
  · exact Set.disjoint_left.mp he (mem_separateBlockNoise_row_iff.mp hq)
      (mem_separateBlockNoise_row_iff.mp hq')
  · exact Set.disjoint_left.mp hf (mem_separateBlockNoise_column_iff.mp hq)
      (mem_separateBlockNoise_column_iff.mp hq')
  · exact Set.disjoint_left.mp he (mem_separateBlockNoise_cell_iff.mp hq).1
      (mem_separateBlockNoise_cell_iff.mp hq').1

/-- A rectangular block of a global-free separate coding is measurable for the σ-algebra generated
by the noise coordinates it reads. -/
private theorem measurable_separateBlockNoise (g : I × I × I → α) (hg : Measurable g)
    (e f : ℕ → ℕ) :
    Measurable[blockSigma (fun (q : NoiseIndex Axis (ℕ × ℕ)) u => u q) (separateBlockNoise e f)]
      fun u (p : ℕ × ℕ) => separateArray (fun q => g q.2) (e p.1, f p.2) u := by
  refine measurable_pi_blockSigma _ fun p => ?_
  have hrow : Measurable[blockSigma (fun (q : NoiseIndex Axis (ℕ × ℕ)) u => u q)
      (separateBlockNoise e f)]
      fun u : NoiseIndex Axis (ℕ × ℕ) → I => u (.vertex .row (e p.1)) :=
    measurable_eval_blockSigma (mem_separateBlockNoise_row_iff.mpr ⟨p.1, rfl⟩)
  have hcol : Measurable[blockSigma (fun (q : NoiseIndex Axis (ℕ × ℕ)) u => u q)
      (separateBlockNoise e f)]
      fun u : NoiseIndex Axis (ℕ × ℕ) → I => u (.vertex .column (f p.2)) :=
    measurable_eval_blockSigma (mem_separateBlockNoise_column_iff.mpr ⟨p.2, rfl⟩)
  have hcell : Measurable[blockSigma (fun (q : NoiseIndex Axis (ℕ × ℕ)) u => u q)
      (separateBlockNoise e f)]
      fun u : NoiseIndex Axis (ℕ × ℕ) → I => u (.cell (e p.1, f p.2)) :=
    measurable_eval_blockSigma (mem_separateBlockNoise_cell_iff.mpr ⟨⟨p.1, rfl⟩, ⟨p.2, rfl⟩⟩)
  simpa only [separateArray_apply, Function.comp_def] using
    hg.comp (hrow.prodMk (hcol.prodMk hcell))

/-- **A separate Aldous--Hoover coding that ignores its global variable is dissociated.** This is
the easy direction of the ergodic form of the representation; the coded array is also separately
exchangeable, by `separatelyExchangeable_separateArray` applied to `fun q => g q.2`. -/
theorem separatelyDissociated_separateArray_of_snd (g : I × I × I → α) (hg : Measurable g) :
    SeparatelyDissociated (noiseMeasure Axis (ℕ × ℕ)) (separateArray fun q => g q.2) :=
  separatelyDissociated_iff.mpr fun e f e' f' he hf =>
    indepFun_of_measurable_blockSigma (iIndepFun_eval_noiseMeasure Axis (ℕ × ℕ))
      (fun q => measurable_pi_apply q) (disjoint_separateBlockNoise he hf)
      (measurable_separateBlockNoise g hg e f) (measurable_separateBlockNoise g hg e' f')

/-- Every unordered pair has a member. -/
private theorem exists_mem_sym2 (s : Sym2 ℕ) : ∃ i, i ∈ s :=
  Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left a b⟩) s

/-- The noise coordinates that the square block along `e` of a joint Aldous--Hoover coding reads,
with the global coordinate left out. A cell variable is read only when **both** its endpoints are
selected, which is what makes two such blocks over disjoint index sets disjoint. -/
private def jointBlockNoise (e : ℕ → ℕ) : Set (NoiseIndex Unit (Sym2 ℕ)) := fun q =>
  match q with
  | .global => False
  | .vertex _ i => i ∈ Set.range e
  | .cell s => ∀ i ∈ s, i ∈ Set.range e

private theorem mem_jointBlockNoise_global_iff {e : ℕ → ℕ} :
    (NoiseIndex.global : NoiseIndex Unit (Sym2 ℕ)) ∈ jointBlockNoise e ↔ False :=
  (Iff.rfl)

private theorem mem_jointBlockNoise_vertex_iff {e : ℕ → ℕ} {i : ℕ} :
    (NoiseIndex.vertex () i : NoiseIndex Unit (Sym2 ℕ)) ∈ jointBlockNoise e ↔ i ∈ Set.range e :=
  (Iff.rfl)

private theorem mem_jointBlockNoise_cell_iff {e : ℕ → ℕ} {s : Sym2 ℕ} :
    (NoiseIndex.cell s : NoiseIndex Unit (Sym2 ℕ)) ∈ jointBlockNoise e ↔
      ∀ i ∈ s, i ∈ Set.range e :=
  (Iff.rfl)

/-- Square blocks over disjoint index sets read disjoint noise coordinates. -/
private theorem disjoint_jointBlockNoise {e e' : ℕ → ℕ}
    (he : Disjoint (Set.range e) (Set.range e')) :
    Disjoint (jointBlockNoise e) (jointBlockNoise e') := by
  rw [Set.disjoint_left]
  rintro (_ | ⟨_, i⟩ | s) hq hq'
  · exact mem_jointBlockNoise_global_iff.mp hq
  · exact Set.disjoint_left.mp he (mem_jointBlockNoise_vertex_iff.mp hq)
      (mem_jointBlockNoise_vertex_iff.mp hq')
  · obtain ⟨i, hi⟩ := exists_mem_sym2 s
    exact Set.disjoint_left.mp he (mem_jointBlockNoise_cell_iff.mp hq i hi)
      (mem_jointBlockNoise_cell_iff.mp hq' i hi)

/-- A square block of a global-free joint coding is measurable for the σ-algebra generated by the
noise coordinates it reads. -/
private theorem measurable_jointBlockNoise (g : I × I × I → α) (hg : Measurable g) (e : ℕ → ℕ) :
    Measurable[blockSigma (fun (q : NoiseIndex Unit (Sym2 ℕ)) u => u q) (jointBlockNoise e)]
      fun u (p : ℕ × ℕ) => jointArray (fun q => g q.2) (e p.1, e p.2) u := by
  refine measurable_pi_blockSigma _ fun p => ?_
  have hcell : ∀ i ∈ s(e p.1, e p.2), i ∈ Set.range e := by
    intro i hi
    rcases Sym2.mem_iff.mp hi with rfl | rfl
    exacts [⟨p.1, rfl⟩, ⟨p.2, rfl⟩]
  have hfst : Measurable[blockSigma (fun (q : NoiseIndex Unit (Sym2 ℕ)) u => u q)
      (jointBlockNoise e)]
      fun u : NoiseIndex Unit (Sym2 ℕ) → I => u (.vertex () (e p.1)) :=
    measurable_eval_blockSigma (mem_jointBlockNoise_vertex_iff.mpr ⟨p.1, rfl⟩)
  have hsnd : Measurable[blockSigma (fun (q : NoiseIndex Unit (Sym2 ℕ)) u => u q)
      (jointBlockNoise e)]
      fun u : NoiseIndex Unit (Sym2 ℕ) → I => u (.vertex () (e p.2)) :=
    measurable_eval_blockSigma (mem_jointBlockNoise_vertex_iff.mpr ⟨p.2, rfl⟩)
  have hcellMeas : Measurable[blockSigma (fun (q : NoiseIndex Unit (Sym2 ℕ)) u => u q)
      (jointBlockNoise e)]
      fun u : NoiseIndex Unit (Sym2 ℕ) → I => u (.cell s(e p.1, e p.2)) :=
    measurable_eval_blockSigma (mem_jointBlockNoise_cell_iff.mpr hcell)
  simpa only [jointArray_apply, Function.comp_def] using
    hg.comp (hfst.prodMk (hsnd.prodMk hcellMeas))

/-- **A joint Aldous--Hoover coding that ignores its global variable is jointly dissociated.** It
need not be separately dissociated: the entries `X (i, j)` and `X (j, i)` read the same cell
variable `u (.cell s(i, j))`, and for a coding through a symmetric `g` they are equal, which
`SeparatelyDissociated.measure_preimage_eq_zero_or_one_of_symm` rules out unless they are trivial.
The coded array is also jointly exchangeable, by `jointlyExchangeable_jointArray` applied to
`fun q => g q.2`. -/
theorem jointlyDissociated_jointArray_of_snd (g : I × I × I → α) (hg : Measurable g) :
    JointlyDissociated (noiseMeasure Unit (Sym2 ℕ)) (jointArray fun q => g q.2) :=
  jointlyDissociated_iff.mpr fun e e' he =>
    indepFun_of_measurable_blockSigma (iIndepFun_eval_noiseMeasure Unit (Sym2 ℕ))
      (fun q => measurable_pi_apply q) (disjoint_jointBlockNoise he)
      (measurable_jointBlockNoise g hg e) (measurable_jointBlockNoise g hg e')

end Dissociation

end AldousHoover

end Probability

end TauCeti

end
