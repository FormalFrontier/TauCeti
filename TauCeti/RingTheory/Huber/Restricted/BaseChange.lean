/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.Restricted.PowerSeries
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Base change for restricted power series

Wedhorn's Remark 8.29 compares `M ⊗[A] A⟨T₁, …, Tₖ⟩` with `M⟨T₁, …, Tₖ⟩` for a finitely generated
module `M` over a complete strongly noetherian Tate ring. This file builds the comparison map, in
the generality where it exists: writing it down needs no finiteness and no completeness, only
continuity of the scalar action — beyond the hypotheses the two objects themselves carry, namely
that `A` is nonarchimedean (without which `A⟨T₁, …, Tₖ⟩` is not a subring) and `ContinuousAdd M`
(without which `M⟨T₁, …, Tₖ⟩` is not a submodule).

The ambient map is Mathlib's: `TensorProduct.piScalarRightHom A A M (Fin k →₀ ℕ)` already has the
type `M ⊗[A] MvPowerSeries (Fin k) A →ₗ[A] MvPowerSeries (Fin k) M`.

## Main definitions

* `mvPowerSeriesBaseChange` : that map, with its codomain ascribed as `MvPowerSeries (Fin k) M`.
* `restrictedMvPowerSeriesBaseChange` : the comparison map of Remark 8.29 itself,
  `M ⊗[A] A⟨T₁, …, Tₖ⟩ →ₗ[A] M⟨T₁, …, Tₖ⟩`.

## Main results

* `mvPowerSeriesBaseChange_tmul`: the map sends `m ⊗ₜ f` to the coefficientwise scalar action
  `s ↦ coeff s f • m`, and `coeff_mvPowerSeriesBaseChange_tmul` reads off a single coefficient.
* `IsRestricted.mvPowerSeriesBaseChange_tmul`: that series is restricted whenever `f` is. It is
  where `ContinuousSMul A M` is used — continuity of `a ↦ a • m` in the *scalar*, which
  `ContinuousConstSMul` does not give.
* `coe_restrictedMvPowerSeriesBaseChange`, with `coe_restrictedMvPowerSeriesBaseChange_tmul`: read
  in the ambient series, the restricted map is the ambient one, at a general element and at a pure
  tensor.

The isomorphism itself — Remark 8.29 proper, which needs `M` finitely generated over a complete
strongly noetherian Tate ring — is not proved here.

## Implementation notes

`MvPowerSeries σ R` is a plain `def` for `(σ →₀ ℕ) → R`, so Mathlib's lemmas about
`TensorProduct.piScalarRightHom` are stated about a type that `rw` and `simp` will not unfold to
reach a goal phrased in power series. Two declarations answer this, and nothing else here crosses
the gap:

* `mvPowerSeriesBaseChange` ascribes the codomain of `TensorProduct.piScalarRightHom` as
  `MvPowerSeries (Fin k) M`. The `simp` steps of the tensor induction behind
  `restrictedMvPowerSeriesBaseChange` — `map_zero`, `map_add` — match that ascription; against the
  unascribed `(Fin k →₀ ℕ) → M` form they rewrite to a term the goal no longer matches
  syntactically.
* `mvPowerSeriesBaseChange_tmul` restates Mathlib's `piScalarRightHom_tmul` at the series type.

Coefficients are read through the `(· : (Fin k →₀ ℕ) → M)` ascription, as `IsRestricted` itself is
phrased: `MvPowerSeries.coeff` is unavailable here because it is `R`-linear on `R`-valued series
and so asks for `Semiring` on the coefficients, which a module of coefficients does not have.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Remark 8.29.
-/

public section

open Filter

namespace TauCeti.Huber

section Ambient

variable {k : ℕ} {A M : Type*} [CommSemiring A] [TopologicalSpace A] [AddCommMonoid M]
  [TopologicalSpace M] [Module A M]

/-- Mathlib's base-change map at the index type of `k`-variable power series, with its codomain
ascribed as `MvPowerSeries (Fin k) M` rather than `(Fin k →₀ ℕ) → M`. It sends `m ⊗ₜ f` to
`s ↦ coeff s f • m`. -/
abbrev mvPowerSeriesBaseChange :
    TensorProduct A M (MvPowerSeries (Fin k) A) →ₗ[A] MvPowerSeries (Fin k) M :=
  TensorProduct.piScalarRightHom A A M (Fin k →₀ ℕ)

omit [TopologicalSpace A] [TopologicalSpace M] in
/-- `mvPowerSeriesBaseChange` sends a pure tensor `m ⊗ₜ f` to the coefficientwise scalar action
`s ↦ coeff s f • m`. -/
@[simp]
theorem mvPowerSeriesBaseChange_tmul (m : M) (f : MvPowerSeries (Fin k) A) :
    mvPowerSeriesBaseChange (TensorProduct.tmul A m f)
      = show MvPowerSeries (Fin k) M from fun s ↦ MvPowerSeries.coeff s f • m :=
  -- Mathlib's `TensorProduct.piScalarRightHom_tmul` is this statement at the function type
  -- `(Fin k →₀ ℕ) → A`. `MvPowerSeries σ R` is a plain `def` for that type, so neither `rw` nor
  -- `simp` can match the lemma against a goal phrased in series: their matching runs at reducible
  -- transparency, which does not unfold it. A term-mode application does, at full transparency,
  -- so this is the one place the two phrasings are bridged; everything below rewrites with it.
  TensorProduct.piScalarRightHom_tmul A A M (Fin k →₀ ℕ) m f

omit [TopologicalSpace A] [TopologicalSpace M] in
/-- The coefficient of `mvPowerSeriesBaseChange (m ⊗ₜ f)` at `s`, read through the function-type
ascription that `IsRestricted` also uses. -/
@[simp]
theorem coeff_mvPowerSeriesBaseChange_tmul (m : M) (f : MvPowerSeries (Fin k) A)
    (s : Fin k →₀ ℕ) :
    (mvPowerSeriesBaseChange (TensorProduct.tmul A m f) : (Fin k →₀ ℕ) → M) s
      = MvPowerSeries.coeff s f • m := (rfl)

/-- A pure tensor with restricted second factor base-changes to a restricted series.

The hypothesis is `ContinuousSMul A M`, not `ContinuousConstSMul A M`: the continuity needed is of
`a ↦ a • m` in the **scalar** variable, since it is the coefficients that vary and the vector that
is fixed. `ContinuousConstSMul` gives continuity in the vector variable instead. -/
theorem IsRestricted.mvPowerSeriesBaseChange_tmul [ContinuousSMul A M]
    {f : MvPowerSeries (Fin k) A} (hf : IsRestricted f) (m : M) :
    IsRestricted (mvPowerSeriesBaseChange (TensorProduct.tmul A m f)) := by
  rw [_root_.TauCeti.Huber.mvPowerSeriesBaseChange_tmul]
  exact isRestricted_iff.mpr ((isRestricted_iff_coeff.mp hf).zero_smul_const m)

end Ambient

/-! ### Between the restricted objects -/

section Restricted

variable {k : ℕ} {A M : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousSMul A M] [ContinuousAdd M]

/-- Base change of an element of `M ⊗[A] A⟨T₁, …, Tₖ⟩`, read in the ambient series, is
restricted. -/
private theorem isRestricted_mvPowerSeriesBaseChange_map
    (x : TensorProduct A M (restrictedMvPowerSeriesSubring k A)) :
    IsRestricted (mvPowerSeriesBaseChange
      (TensorProduct.map LinearMap.id restrictedMvPowerSeriesSubringVal.toLinearMap x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
      simpa using (mem_restrictedMvPowerSeriesSubring.mp f.2).mvPowerSeriesBaseChange_tmul m
  | add y z hy hz => simpa using hy.add hz

/-- **The comparison map of Wedhorn Remark 8.29**: `M ⊗[A] A⟨T₁, …, Tₖ⟩ →ₗ[A] M⟨T₁, …, Tₖ⟩`.

Mathlib's base-change map restricted on both sides. Remark 8.29 asserts that it is an isomorphism
when `M` is finitely generated over a complete strongly noetherian Tate ring, which is not proved
here. -/
noncomputable def restrictedMvPowerSeriesBaseChange :
    TensorProduct A M (restrictedMvPowerSeriesSubring k A) →ₗ[A]
      restrictedMvPowerSeriesSubmodule k A M :=
  LinearMap.codRestrict _
    (mvPowerSeriesBaseChange.comp
      (TensorProduct.map LinearMap.id restrictedMvPowerSeriesSubringVal.toLinearMap))
    fun x ↦ mem_restrictedMvPowerSeriesSubmodule.mpr
      (isRestricted_mvPowerSeriesBaseChange_map x)

/-- Read in the ambient series, `restrictedMvPowerSeriesBaseChange` is `mvPowerSeriesBaseChange`
of the underlying series. The definition's body is not exposed, so this is how a consumer computes
with it. -/
@[simp]
theorem coe_restrictedMvPowerSeriesBaseChange
    (x : TensorProduct A M (restrictedMvPowerSeriesSubring k A)) :
    ((restrictedMvPowerSeriesBaseChange x : restrictedMvPowerSeriesSubmodule k A M) :
        MvPowerSeries (Fin k) M)
      -- `codRestrict` and `LinearMap.comp` are projections.
      = mvPowerSeriesBaseChange
          (TensorProduct.map LinearMap.id restrictedMvPowerSeriesSubringVal.toLinearMap x) := (rfl)

/-- Read in the ambient series, `restrictedMvPowerSeriesBaseChange` agrees with
`mvPowerSeriesBaseChange` on a pure tensor. -/
theorem coe_restrictedMvPowerSeriesBaseChange_tmul (m : M)
    (f : restrictedMvPowerSeriesSubring k A) :
    ((restrictedMvPowerSeriesBaseChange (TensorProduct.tmul A m f) :
        restrictedMvPowerSeriesSubmodule k A M) : MvPowerSeries (Fin k) M)
      = mvPowerSeriesBaseChange (TensorProduct.tmul A m (f : MvPowerSeries (Fin k) A)) := by
  rw [coe_restrictedMvPowerSeriesBaseChange, TensorProduct.map_tmul]
  -- `simp` lands both sides on the coefficient function; the residue is the `MvPowerSeries`
  -- wrapper, which only full transparency crosses.
  simp
  rfl

end Restricted

end TauCeti.Huber

