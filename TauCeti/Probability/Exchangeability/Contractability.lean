/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Probability.IdentDistrib
import TauCeti.Probability.Exchangeability.PermutationExtension
import TauCeti.Probability.Exchangeability.ExchangeableAtMonotone
import Mathlib.Order.Fin.Tuple
import TauCeti.Probability.Exchangeability.FiniteMarginals

/-!
# Contractability API

This file records basic lemmas for `Contractable` processes. The definitions live in
`TauCeti.Probability.Exchangeability.Basic`; this file is the Layer 0 home for
contractability-specific API.

The main result is `contractable_of_exchangeable` (with dot-notation form
`Exchangeable.contractable`): every exchangeable sequence with a.e. measurable coordinates is
contractable. The file also provides `Exchangeable.blockLaw_eq_prefixLaw_of_injective` (the
injective-selection analogue) and `Contractable.measurePreserving_reindex` /
`Contractable.measurePreserving_shift` (a contractable path law is invariant under strictly monotone
time-reindexing, in particular the shift), plus the converse characterization
`contractable_iff_forall_map_reindex_pathLaw`.

These declarations are adapted from the `cameronfreer/exchangeability` Layer 0 sources pinned
at `e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses; the
combinatorial core now lives in `PermutationExtension.lean`. `Contractable.pairLaw_eq` is adapted
from `DeFinetti/ViaMartingale/FutureRectangles.lean` (`contractable_dist_eq`) in the same repo,
reproved via the reindexing route below rather than the reference's rectangle π-system.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A contractable process has the same finite-dimensional block law as the corresponding
prefix law along any strictly increasing finite index map. -/
theorem Contractable.map {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) :
    blockLaw μ X k = prefixLaw μ X m :=
  h m k hk

/-- The one-coordinate specialization of contractability. -/
theorem Contractable.map_single {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    (k : Fin 1 → ℕ) :
    blockLaw μ X k = prefixLaw μ X 1 :=
  h.map (Subsingleton.strictMono k)

/-- The two-coordinate specialization of contractability. -/
theorem Contractable.map_pair {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {i j : ℕ} (hij : i < j) :
    blockLaw μ X ![i, j] = prefixLaw μ X 2 :=
  h.map (strictMono_vecEmpty.vecCons hij)

/-- **Finite blocks of a contractable process are identically distributed.** For a contractable
process `X`, any two strictly increasing finite coordinate selections have the same joint law. -/
theorem Contractable.identDistrib_block {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) {m : ℕ} {k l : Fin m → ℕ} (hk : StrictMono k) (hl : StrictMono l)
    (hk_meas : ∀ r, AEMeasurable (X (k r)) μ)
    (hl_meas : ∀ r, AEMeasurable (X (l r)) μ) :
    IdentDistrib (fun ω r => X (k r) ω) (fun ω r => X (l r) ω) μ μ where
  aemeasurable_fst := aemeasurable_pi_lambda _ hk_meas
  aemeasurable_snd := aemeasurable_pi_lambda _ hl_meas
  map_eq := by
    simpa [blockLaw_def] using (hX.map hk).trans (hX.map hl).symm

/-- **Coordinates of a contractable process are identically distributed.** For a contractable
process `X`, any two a.e. measurable coordinates `X i` and `X j` have the same law. -/
theorem Contractable.identDistrib_coord {μ : Measure Ω} {X : ℕ → Ω → α} (hX : Contractable μ X)
    {i j : ℕ} (hi_meas : AEMeasurable (X i) μ) (hj_meas : AEMeasurable (X j) μ) :
    IdentDistrib (X i) (X j) μ μ := by
  have hblock := hX.identDistrib_block
    (Subsingleton.strictMono (fun _ : Fin 1 => i))
    (Subsingleton.strictMono (fun _ : Fin 1 => j)) (fun _ => hi_meas) (fun _ => hj_meas)
  have hcomp := hblock.comp (measurable_pi_apply (0 : Fin 1))
  convert hcomp using 1 <;> funext ω <;> simp [Function.comp]

/-- **Increasing pairs of a contractable process are identically distributed.** For a
contractable process `X`, if the four selected coordinates are a.e. measurable and `i < j`,
`k < l`, then `(X i, X j)` has the same joint law as `(X k, X l)`. -/
theorem Contractable.identDistrib_pair {μ : Measure Ω} {X : ℕ → Ω → α} (hX : Contractable μ X)
    {i j k l : ℕ} (hi_meas : AEMeasurable (X i) μ) (hj_meas : AEMeasurable (X j) μ)
    (hk_meas : AEMeasurable (X k) μ) (hl_meas : AEMeasurable (X l) μ)
    (hij : i < j) (hkl : k < l) :
    IdentDistrib (fun ω => (X i ω, X j ω)) (fun ω => (X k ω, X l ω)) μ μ := by
  have hblock := hX.identDistrib_block (strictMono_vecEmpty.vecCons hij)
    (strictMono_vecEmpty.vecCons hkl)
    (fun r => by
      fin_cases r
      · simpa [Matrix.cons_val_zero] using hi_meas
      · simpa [Matrix.cons_val_one] using hj_meas)
    (fun r => by
      fin_cases r
      · simpa [Matrix.cons_val_zero] using hk_meas
      · simpa [Matrix.cons_val_one] using hl_meas)
  have hcomp := hblock.comp
    ((measurable_pi_apply (0 : Fin 2)).prodMk (measurable_pi_apply (1 : Fin 2)))
  convert hcomp using 1 <;> funext ω <;>
    simp [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Contractability is preserved by passing to a strictly increasing subsequence. -/
theorem Contractable.comp {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Contractable μ (fun n ω => X (φ n) ω) := by
  intro m k hk
  calc
    blockLaw μ (fun n ω => X (φ n) ω) k =
        blockLaw μ X (φ ∘ k) := by
      simp only [blockLaw_def, Function.comp_apply]
    _ = prefixLaw μ X m := h.map (hφ.comp hk)
    _ = blockLaw μ (fun n ω => X (φ n) ω) (fun i : Fin m => i.val) := by
      have := (h.map (hφ.comp (Fin.val_strictMono : StrictMono (fun i : Fin m => i.val)))).symm
      simpa only [blockLaw_def, Function.comp_apply] using this
    _ = prefixLaw μ (fun n ω => X (φ n) ω) m := by
      simp only [prefixLaw_def]

/-- **An exchangeable sequence has the prefix law along any injective finite selection:**
`blockLaw μ X k = prefixLaw μ X n` for injective `k : Fin n → ℕ`. -/
theorem Exchangeable.blockLaw_eq_prefixLaw_of_injective {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    {n : ℕ} (k : Fin n → ℕ) (hk : Function.Injective k) :
    blockLaw μ X k = prefixLaw μ X n := by
  set N := max n (Finset.univ.sup k + 1) with hN
  have hnN : n ≤ N := le_max_left _ _
  have hk_bound : ∀ i, k i < N := by
    intro i
    have h1 : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
    have h2 : Finset.univ.sup k + 1 ≤ N := le_max_right _ _
    omega
  simpa using
    (hX.exchangeableAt N).blockLaw_eq_prefixLaw_of_injective
      (fun i : Fin n => (⟨k i, hk_bound i⟩ : Fin N))
      (fun _ _ h => hk (congrArg Fin.val h))
      (fun j : Fin N => hX_meas j.val)

/-- **Every exchangeable sequence with a.e. measurable coordinates is contractable**: along any
strictly increasing finite selection `k`, `blockLaw μ X k = prefixLaw μ X m`. One direction of the
de Finetti–Ryll-Nardzewski equivalence. -/
theorem contractable_of_exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Contractable μ X :=
  fun _ k hk => Exchangeable.blockLaw_eq_prefixLaw_of_injective hX hX_meas k hk.injective

/-- Every exchangeable sequence with a.e. measurable coordinates is contractable (dot-notation
form of `contractable_of_exchangeable`). -/
theorem Exchangeable.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Contractable μ X :=
  contractable_of_exchangeable hX hX_meas

/-- **A contractable process's path law is invariant under strictly monotone time-reindexing:** for
`StrictMono φ`, the reindexing `x ↦ x ∘ φ` preserves `pathLaw μ X`. -/
theorem Contractable.measurePreserving_reindex {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) (pathLaw μ X) (pathLaw μ X) := by
  refine ⟨measurable_pi_lambda _ fun k => measurable_pi_apply (φ k), ?_⟩
  haveI : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  refine measure_eq_of_prefixProj_map_eq ?_
  intro n
  rw [map_reindex_prefixProj_pathLaw μ hX_meas φ n,
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) n]
  exact hX n (fun i : Fin n => φ i.val) (hφ.comp Fin.val_strictMono)

/-- Contractability is equivalent to invariance of the path law under every strictly increasing
time-reindexing `ℕ → ℕ`. This is the path-law form of spreadability/contractability. -/
theorem contractable_iff_forall_map_reindex_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Contractable μ X ↔
      ∀ φ : ℕ → ℕ, StrictMono φ →
        (pathLaw μ X).map (fun x : ℕ → α => fun k => x (φ k)) = pathLaw μ X := by
  constructor
  · intro hX φ hφ
    exact (hX.measurePreserving_reindex hX_meas hφ).map_eq
  · intro hX m k hk
    obtain ⟨φ, hφ, hφ_eq⟩ := exists_strictMono_nat_extending_fin hk
    have hmap := congrArg (fun ν : Measure (ℕ → α) => ν.map (prefixProj α m)) (hX φ hφ)
    rw [map_reindex_prefixProj_pathLaw μ hX_meas φ m,
      map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) m] at hmap
    have hidx : (fun i : Fin m => φ i.val) = k := by
      funext i
      exact hφ_eq i
    simpa [hidx] using hmap

/-- Contractability is equivalent to preservation of the path law by every strictly increasing
time-reindexing `ℕ → ℕ`. -/
theorem contractable_iff_forall_measurePreserving_reindex {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Contractable μ X ↔
      ∀ φ : ℕ → ℕ, StrictMono φ →
        MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) (pathLaw μ X) (pathLaw μ X) := by
  rw [contractable_iff_forall_map_reindex_pathLaw hX_meas]
  constructor
  · intro hX φ hφ
    exact ⟨measurable_reindex φ, hX φ hφ⟩
  · intro hX φ hφ
    exact (hX φ hφ).map_eq

/-- **A contractable process has a shift-invariant path law:** `shift` preserves `pathLaw μ X`. -/
theorem Contractable.measurePreserving_shift {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X) :=
  Contractable.measurePreserving_reindex hX hX_meas (φ := fun k => k + 1)
    (fun _ _ h => Nat.add_lt_add_right h 1)

/-- **Pair-law equality from contractability.** For a contractable process, a strictly increasing
tail selection `g`, and two head indices `j, k` below the tail start `g 0`, the joint law of the
head coordinate `X j` with the tail `(X (g 0), X (g 1), …)` equals the joint law of `X k` with
the **same** tail:
```
μ.map (fun ω => (X j ω, fun n => X (g n) ω)) = μ.map (fun ω => (X k ω, fun n => X (g n) ω)).
```
-/
theorem Contractable.pairLaw_eq {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_ae : ∀ n, AEMeasurable (X n) μ) {g : ℕ → ℕ} (hg : StrictMono g)
    {j k : ℕ} (hj : j < g 0) (hk : k < g 0) :
    μ.map (fun ω => (X j ω, fun n => X (g n) ω))
      = μ.map (fun ω => (X k ω, fun n => X (g n) ω)) := by
  classical
  -- The head/tail split on path space.
  let headTail : (ℕ → α) → α × (ℕ → α) := fun f => (f 0, fun n => f (n + 1))
  have hheadTail_meas : Measurable headTail :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1))
  -- Strictly-monotone time-reindexing preserves the path law of a contractable process.
  have hreindex : ∀ φ : ℕ → ℕ, StrictMono φ →
      μ.map (fun ω (i : ℕ) => X (φ i) ω) = pathLaw μ X := by
    intro φ hφ
    calc μ.map (fun ω (i : ℕ) => X (φ i) ω)
        = (pathLaw μ X).map (fun x : ℕ → α => fun i => x (φ i)) :=
          (map_reindex_pathLaw μ hX_ae φ).symm
      _ = pathLaw μ X := (hX.measurePreserving_reindex hX_ae hφ).map_eq
  -- For a head `h < g 0`, the selection `(h, g 0, g 1, …)` is strictly monotone and collapses the
  -- joint law of `(X h, tail)` onto the common measure `(pathLaw μ X).map headTail`.
  have side : ∀ h : ℕ, h < g 0 →
      μ.map (fun ω => (X h ω, fun n => X (g n) ω)) = (pathLaw μ X).map headTail := by
    intro h hhr
    set φ : ℕ → ℕ := fun i => if i = 0 then h else g (i - 1) with hφdef
    have hφmono : StrictMono φ := by
      intro a b hab
      simp only [hφdef]
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        rw [if_pos rfl, if_neg (by omega : b ≠ 0)]
        exact hhr.trans_le (hg.monotone (Nat.zero_le _))
      · rw [if_neg (by omega : a ≠ 0), if_neg (by omega : b ≠ 0)]
        exact hg (by omega : a - 1 < b - 1)
    have hφ0 : φ 0 = h := by simp [hφdef]
    -- The tail-index identity, stated explicitly rather than left to definitional reduction.
    have hφsucc : ∀ n, φ (n + 1) = g n := by
      intro n; simp only [hφdef]; rw [if_neg (by omega : n + 1 ≠ 0), Nat.add_sub_cancel]
    have hpath_ae : AEMeasurable (fun ω (i : ℕ) => X (φ i) ω) μ :=
      aemeasurable_pi_lambda _ fun i => hX_ae (φ i)
    have hfun : (fun ω => (X h ω, fun n => X (g n) ω))
        = headTail ∘ (fun ω (i : ℕ) => X (φ i) ω) := by
      funext ω
      simp only [headTail, Function.comp_apply, hφ0, hφsucc]
    rw [hfun, ← AEMeasurable.map_map_of_aemeasurable hheadTail_meas.aemeasurable hpath_ae,
      hreindex φ hφmono]
  rw [side j hj, side k hk]

end Probability

end TauCeti
