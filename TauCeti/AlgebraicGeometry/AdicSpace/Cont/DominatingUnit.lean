/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic
public import TauCeti.RingTheory.Huber.Basic
import TauCeti.RingTheory.Huber.ZeroSequenceOfUnits
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Wedhorn Lemma 7.31 and Corollary 7.32: dominating a nonvanishing element by a unit

Let `A` be a Tate ring, `X` a quasi-compact set of continuous points of `Spv A`, and `f : A` an
element that vanishes at no point of `X`. Wedhorn Corollary 7.32 produces a **unit** of `A` whose
valuation is everywhere on `X` strictly below that of `f`; Lemma 7.31 is the neighbourhood-of-zero
form it is drawn from.

## The cover both rest on

Fix a topologically nilpotent `t : A`. A continuous point `v` with `v f ≠ 0` opens the ball
`{a | v a < v f}` around `0`, so the powers of `t` eventually enter it — that is
`Valuation.exists_pow_lt_of_isTopologicallyNilpotent`, and it places `v` in the basic open set
`Spv(A)(tⁿ/f)` for some `n`. These basic opens increase in `n` on `X`, because `v t < 1` there,
so quasi-compactness collapses the cover to a single exponent: `X ⊆ Spv(A)(tᵐ/f)`.

Lemma 7.31 spends that exponent at a pseudouniformiser `ϖ`. The set `ϖᵐ · I` is then a
neighbourhood of zero — multiplication by the unit `ϖᵐ` is an open map, and the image of an ideal
of definition is an open neighbourhood of zero — and every `a = ϖᵐ y` in it satisfies
`v a = v ϖᵐ · v y < v ϖᵐ ≤ v f`, strictly because `y` is topologically nilpotent. Corollary 7.32
then reads off a unit inside that neighbourhood, which is what the Tate hypothesis is for.

## The hypothesis is continuity, not the plus ring

Wedhorn states both results for a quasi-compact subset of an adic spectrum `Spa (A, A⁺)`. Neither
proof uses the sub-unit condition on `A⁺`, only continuity of the points, so both are stated here
over `TauCeti.ValuationSpectrum.cont A`. They apply verbatim in Wedhorn's setting through
`spa_def ▸ Set.inter_subset_left : spa Aplus ⊆ cont A`.

## Main results

* `TauCeti.ValuationSpectrum.exists_subset_basicOpen_pow`: the collapsed cover — some power of a
  topologically nilpotent element is dominated by `f` throughout `X`.
* `TauCeti.ValuationSpectrum.exists_mem_nhds_zero_forall_vlt`: **Lemma 7.31** — a neighbourhood of
  zero all of whose elements are strictly dominated by `f` throughout `X`.
* `TauCeti.ValuationSpectrum.exists_unit_forall_vlt`: **Corollary 7.32** — a unit strictly
  dominated by `f` throughout `X`.

The Tate-ring input, that a neighbourhood of zero contains a unit, is
`TauCeti.HasZeroSequenceOfUnits.exists_unit_smul_mem` at `x = 1`, available for a Tate ring
through the instance `TauCeti.Huber.IsTateRing.hasZeroSequenceOfUnits`.

## Provenance

Adapted from AINTLIB (see References), file `Cor732.lean`: the cover-and-collapse argument, the
construction of the neighbourhood as `ϖᵐ · I`, and the assembly of the corollary are that file's
`exists_pow_dominated_finset`, `exists_zero_nbhd_lt_on_qc` and `exists_dominating_unit_noHArch`.
The vocabulary is adapted to this repository's interfaces throughout: `cont`/`Spv.valuation` in
place of that file's `Spa`/`ValuativeRel.valuation` pairing, `basicOpen` in place of its bespoke
`dominatedBy`, and the per-point step delegated to
`Valuation.exists_pow_lt_of_isTopologicallyNilpotent` rather than restated. That file's
`exists_dominating_unit`, which assumes `MulArchimedean` value groups, is *not* Corollary 7.32 and
is not ported; the route taken here is Wedhorn's own and carries no such hypothesis.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.31 and Corollary 7.32.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, `projects/AdicSpaces/Adic spaces/Cor732.lean`.
-/

namespace TauCeti.ValuationSpectrum

public section

open Topology TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **The basic opens `Spv(A)(tⁿ/f)` increase in the exponent at a continuous point.** A
topologically nilpotent `t` has `v t < 1` there, so `v (tᵐ) ≤ v (tⁿ)` whenever `n ≤ m`. This is
the monotonicity that lets a finite subcover be replaced by its largest exponent. -/
private theorem mem_basicOpen_pow_of_le {v : Spv A} (hv : v ∈ cont A) {f t : A}
    (ht : IsTopologicallyNilpotent t) {n m : ℕ} (hnm : n ≤ m) (hn : v ∈ basicOpen (t ^ n) f) :
    v ∈ basicOpen (t ^ m) f := by
  have hcont : v.valuation.IsContinuous := (isContinuous_def v).mp ((mem_cont_iff v).mp hv)
  have hle : v.valuation (t ^ m) ≤ v.valuation (t ^ n) := by
    rw [map_pow, map_pow]
    exact pow_le_pow_of_le_one zero_le (hcont.lt_one_of_isTopologicallyNilpotent ht).le hnm
  obtain ⟨hvn, hvf⟩ := (mem_basicOpen_iff (t ^ n) f v).mp hn
  exact (mem_basicOpen_iff (t ^ m) f v).mpr ⟨(valuation_le_iff v (t ^ m) f).mp
    (hle.trans ((valuation_le_iff v (t ^ n) f).mpr hvn)), hvf⟩

/-- **The cover behind Wedhorn Lemma 7.31, collapsed to one exponent.** For `X` a quasi-compact
set of continuous points at which `f` does not vanish and `t` topologically nilpotent, some power
`tᵐ` is dominated by `f` at every point of `X`: `X ⊆ Spv(A)(tᵐ/f)`.

Pointwise this is `Valuation.exists_pow_lt_of_isTopologicallyNilpotent` at the threshold `v f`,
whose ball is open because `v` is continuous. The resulting basic opens increase in the exponent
on `X`, so a finite subcover has a largest exponent that works for all. -/
theorem exists_subset_basicOpen_pow {X : Set (Spv A)} (hXcont : X ⊆ cont A) (hX : IsCompact X)
    {f : A} (hf : ∀ v ∈ X, ¬ v.toValuativeRel.vle f 0) {t : A} (ht : IsTopologicallyNilpotent t) :
    ∃ m : ℕ, X ⊆ basicOpen (t ^ m) f := by
  -- the basic opens `Spv(A)(tⁿ/f)` cover `X`, since the powers of `t` enter the ball of
  -- radius `v f` — which is open because `v` is continuous, and nonempty because `v f ≠ 0`
  have hcover : X ⊆ ⋃ n : ℕ, basicOpen (t ^ n) f := fun v hv ↦ by
    have hcont : v.valuation.IsContinuous := (isContinuous_def v).mp ((mem_cont_iff v).mp
      (hXcont hv))
    have hfne : v.valuation f ≠ 0 := fun h ↦ hf v hv ((valuation_le_iff v f 0).mp (by simp [h]))
    have hlt : v.valuation 0 < v.valuation f := by rw [map_zero]; exact zero_lt_iff.mpr hfne
    obtain ⟨n, hn⟩ := Valuation.exists_pow_lt_of_isTopologicallyNilpotent (v := v.valuation)
      (γ := v.valuation f)
      ((Valuation.isContinuous_def.mp hcont f).mem_nhds hlt) ht
    exact Set.mem_iUnion.mpr ⟨n, (mem_basicOpen_iff (t ^ n) f v).mpr
      ⟨(valuation_le_iff v (t ^ n) f).mp (by rw [map_pow]; exact hn.le), hf v hv⟩⟩
  obtain ⟨F, hF⟩ := hX.elim_finite_subcover (fun n : ℕ ↦ basicOpen (t ^ n) f)
    (fun n ↦ isOpen_basicOpen _ _) hcover
  refine ⟨F.sup id, fun v hv ↦ ?_⟩
  obtain ⟨n, hnF, hvn⟩ := Set.mem_iUnion₂.mp (hF hv)
  exact mem_basicOpen_pow_of_le (hXcont hv) ht (Finset.le_sup (f := id) hnF) hvn

variable [IsTopologicalRing A] [IsTateRing A]

/-- **Wedhorn Lemma 7.31.** For `X` a quasi-compact set of continuous points of a Tate ring at
which `f` does not vanish, some neighbourhood of zero is strictly dominated by `f` throughout `X`.

The neighbourhood is `ϖᵐ · I` for a pseudouniformiser `ϖ`, the exponent `m` supplied by
`exists_subset_basicOpen_pow`, and `I` the image of an ideal of definition. Its elements
`a = ϖᵐ y` have `v a = v ϖᵐ · v y < v ϖᵐ ≤ v f`, the strict step because `y` is topologically
nilpotent and `v ϖᵐ ≠ 0`. -/
theorem exists_mem_nhds_zero_forall_vlt {X : Set (Spv A)} (hXcont : X ⊆ cont A) (hX : IsCompact X)
    {f : A} (hf : ∀ v ∈ X, ¬ v.toValuativeRel.vle f 0) :
    ∃ I ∈ 𝓝 (0 : A), ∀ a ∈ I, ∀ v ∈ X, v.toValuativeRel.vlt a f := by
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨m, hm⟩ := exists_subset_basicOpen_pow hXcont hX hf hϖ.isTopologicallyNilpotent
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  refine ⟨(fun y ↦ ϖ ^ m * y) '' (P.idealImage 1 : Set A),
    ((hϖ.isUnit.pow m).isOpenMap_smul _ (P.isOpen_idealImage 1)).mem_nhds
      ⟨0, (P.idealImage 1).zero_mem, mul_zero _⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ v hv
  have hcont : v.valuation.IsContinuous :=
    (isContinuous_def v).mp ((mem_cont_iff v).mp (hXcont hv))
  -- `ϖ ^ m` is a unit, so its valuation is invertible, in particular nonzero
  have hne : v.valuation (ϖ ^ m) ≠ 0 := by
    obtain ⟨z, hz⟩ := (hϖ.isUnit.pow m).exists_right_inv
    intro h
    have h1 : v.valuation (1 : A) = 0 := by rw [← hz, map_mul, h, zero_mul]
    simp at h1
  refine (valuation_lt_iff v _ f).mp ?_
  calc v.valuation (ϖ ^ m * y) = v.valuation (ϖ ^ m) * v.valuation y := map_mul _ _ _
    _ < v.valuation (ϖ ^ m) * 1 :=
        mul_lt_mul_of_pos_left (hcont.lt_one_of_isTopologicallyNilpotent
          (P.isTopologicallyNilpotent_of_mem_idealImage one_ne_zero hy)) (zero_lt_iff.mpr hne)
    _ = v.valuation (ϖ ^ m) := mul_one _
    _ ≤ v.valuation f := (valuation_le_iff v (ϖ ^ m) f).mpr
        ((mem_basicOpen_iff (ϖ ^ m) f v).mp (hm hv)).1

/-- **Wedhorn Corollary 7.32.** For `X` a quasi-compact set of continuous points of a Tate ring at
which `f` does not vanish, there is a unit of `A` strictly dominated by `f` throughout `X`.

Lemma 7.31 supplies a neighbourhood of zero dominated by `f`, and the Tate hypothesis puts a unit
inside it (`TauCeti.HasZeroSequenceOfUnits.exists_unit_smul_mem` at `x = 1`). -/
theorem exists_unit_forall_vlt {X : Set (Spv A)} (hXcont : X ⊆ cont A) (hX : IsCompact X) {f : A}
    (hf : ∀ v ∈ X, ¬ v.toValuativeRel.vle f 0) :
    ∃ ϖ : Aˣ, ∀ v ∈ X, v.toValuativeRel.vlt (ϖ : A) f := by
  obtain ⟨I, hI, hIf⟩ := exists_mem_nhds_zero_forall_vlt hXcont hX hf
  have hc : ContinuousAt (fun a : A ↦ a • (1 : A)) 0 := by fun_prop
  obtain ⟨ϖ, hϖ⟩ := HasZeroSequenceOfUnits.exists_unit_smul_mem (M := A) 1 hc hI
  exact ⟨ϖ, hIf _ (by simpa using hϖ)⟩

end

end TauCeti.ValuationSpectrum
