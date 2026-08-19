/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
* `restrictedMvPowerSeriesFinPiEquiv` and `tensorFinPiEquiv` : the two identifications the finite
  free case runs through.

## Main results

* `mvPowerSeriesBaseChange_tmul`: the map sends `m ⊗ₜ f` to the coefficientwise scalar action
  `s ↦ coeff s f • m`, and `coeff_mvPowerSeriesBaseChange_tmul` reads off a single coefficient.
* `IsRestricted.mvPowerSeriesBaseChange_tmul`: that series is restricted whenever `f` is. It is
  where `ContinuousSMul A M` is used — continuity of `a ↦ a • m` in the *scalar*, which
  `ContinuousConstSMul` does not give.
* `coe_restrictedMvPowerSeriesBaseChange`, with `coe_restrictedMvPowerSeriesBaseChange_tmul`: read
  in the ambient series, the restricted map is the ambient one, at a general element and at a pure
  tensor; `coeff_restrictedMvPowerSeriesBaseChange_tmul` reads off a single coefficient.

* `restrictedMvPowerSeriesBaseChangeFinEquiv`, with
  `restrictedMvPowerSeriesBaseChange_fin_bijective`: **Remark 8.29's conclusion in the finite free
  case** — the comparison map packaged as a linear
  equivalence, and its bijectivity in the form a reduction argument consumes.
* `restrictedMvPowerSeriesFinPiEquiv_baseChange`: the transported equality behind it. For
  `M = Fin n → A` the comparison map is Mathlib's tensor-pi equivalence transported along
  `restrictedMvPowerSeriesFinPiEquiv`, so it is an isomorphism — the base case the finitely
  generated statement reduces to.

The isomorphism for a general finitely generated `M` — Remark 8.29 proper, which needs `M`
presented over a complete strongly noetherian Tate ring — is not proved here.

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

The finite free equality is stated as `finPiEquiv (baseChange x) = tensorFinPiEquiv x` rather
than through `(finPiEquiv …).symm`, because the equivalences' bodies are unexposed: `_apply`
computes across the module boundary while `_symm_apply` on a *composite* does not. The isomorphism
itself is then packaged separately, so consumers get a `LinearEquiv` without paying that cost.

Coefficients are read through the `(· : (Fin k →₀ ℕ) → M)` ascription, as `IsRestricted` itself is
phrased: `MvPowerSeries.coeff` is unavailable here because it is `R`-linear on `R`-valued series
and so asks for `Semiring` on the coefficients, which a module of coefficients does not have.

## Provenance

Nothing here is ported. The ambient map is Mathlib's `TensorProduct.piScalarRightHom`, and the
finite free case runs through Mathlib's `TensorProduct.comm` and `TensorProduct.piScalarRight`;
everything else — the restricted comparison map, its coefficient lemmas, and the identification
`restrictedMvPowerSeriesFinPiEquiv` — is this repository's own.

AINTLIB, the roadmap's designated prior formalisation for this layer, has no counterpart to
compare against: it states restricted power series only over a coefficient *ring*, never over a
module, so `M⟨T₁, …, Tₖ⟩` and hence Remark 8.29's comparison do not appear there. That was checked
against `RestrictedPowerSeries.lean` and the three `TateAlgebra*.lean` files, whose `Submodule`
occurrences are ideals of the coefficient ring viewed as submodules rather than module
coefficients.

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
theorem coeff_mvPowerSeriesBaseChange_tmul (m : M) (f : MvPowerSeries (Fin k) A) (s : Fin k →₀ ℕ) :
    (mvPowerSeriesBaseChange (TensorProduct.tmul A m f) : (Fin k →₀ ℕ) → M) s
      = MvPowerSeries.coeff s f • m := (rfl)

/-- A pure tensor with restricted second factor base-changes to a restricted series.

The hypothesis is `ContinuousSMul A M`, not `ContinuousConstSMul A M`: the continuity needed is of
`a ↦ a • m` in the **scalar** variable, since it is the coefficients that vary and the vector that
is fixed. `ContinuousConstSMul` gives continuity in the vector variable instead. -/
theorem IsRestricted.mvPowerSeriesBaseChange_tmul [ContinuousSMul A M] {f : MvPowerSeries (Fin k) A}
    (hf : IsRestricted f) (m : M) :
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
  -- Both sides land on the coefficient function; the residue is the `MvPowerSeries` wrapper,
  -- which only full transparency crosses.
  simp only [LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply,
    restrictedMvPowerSeriesSubringVal_apply, mvPowerSeriesBaseChange_tmul]
  rfl


/-- The coefficient of `restrictedMvPowerSeriesBaseChange (m ⊗ₜ f)` at `s`, read through the
function-type ascription that `IsRestricted` also uses. -/
@[simp]
theorem coeff_restrictedMvPowerSeriesBaseChange_tmul (m : M)
    (f : restrictedMvPowerSeriesSubring k A) (s : Fin k →₀ ℕ) :
    (((restrictedMvPowerSeriesBaseChange (TensorProduct.tmul A m f) :
        restrictedMvPowerSeriesSubmodule k A M) : MvPowerSeries (Fin k) M) :
      (Fin k →₀ ℕ) → M) s = MvPowerSeries.coeff s (f : MvPowerSeries (Fin k) A) • m := by
  rw [coe_restrictedMvPowerSeriesBaseChange_tmul]
  exact coeff_mvPowerSeriesBaseChange_tmul m _ s

end Restricted

/-! ### The finite free case of Remark 8.29 -/

section FiniteFree

variable {k n : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- `(Fin n → A)⟨T₁, …, Tₖ⟩ ≃ₗ[A] Fin n → A⟨T₁, …, Tₖ⟩`: a restricted series with finite-tuple
coefficients is the tuple of its component series. -/
noncomputable def restrictedMvPowerSeriesFinPiEquiv (k n : ℕ) (A : Type*) [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] :
    restrictedMvPowerSeriesSubmodule k A (Fin n → A) ≃ₗ[A]
      (Fin n → restrictedMvPowerSeriesSubring k A) :=
  (restrictedMvPowerSeriesSubmodulePiEquiv k A fun _ : Fin n ↦ A).trans
    (LinearEquiv.piCongrRight fun _ ↦ (restrictedMvPowerSeriesSubringLinearEquiv k A).symm)

/-- `(Fin n → A) ⊗[A] A⟨T₁, …, Tₖ⟩ ≃ₗ[A] Fin n → A⟨T₁, …, Tₖ⟩`, from Mathlib: the tensor factors
through the finite index. -/
noncomputable def tensorFinPiEquiv (k n : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] :
    TensorProduct A (Fin n → A) (restrictedMvPowerSeriesSubring k A) ≃ₗ[A]
      (Fin n → restrictedMvPowerSeriesSubring k A) :=
  (TensorProduct.comm A _ _).trans
    (TensorProduct.piScalarRight A A (restrictedMvPowerSeriesSubring k A) (Fin n))

/-- `restrictedMvPowerSeriesFinPiEquiv` reads off the `i`-th component series: its `s`-th
coefficient is the `i`-th entry of `f`'s. -/
@[simp]
theorem restrictedMvPowerSeriesFinPiEquiv_apply
    (f : restrictedMvPowerSeriesSubmodule k A (Fin n → A)) (i : Fin n) (s : Fin k →₀ ℕ) :
    ((restrictedMvPowerSeriesFinPiEquiv k n A f i : MvPowerSeries (Fin k) A) :
      (Fin k →₀ ℕ) → A) s =
      (((f : MvPowerSeries (Fin k) (Fin n → A)) : (Fin k →₀ ℕ) → Fin n → A) s) i := by
  -- The equivalence is a composite of two whose bodies are unexposed, so this is the lemma every
  -- consumer computes through rather than unfolding.
  simp only [restrictedMvPowerSeriesFinPiEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, coe_restrictedMvPowerSeriesSubringLinearEquiv_symm,
    restrictedMvPowerSeriesSubmodulePiEquiv_apply]

/-- `restrictedMvPowerSeriesFinPiEquiv.symm` assembles a tuple of component series into a
tuple-valued series: the `i`-th entry of its `s`-th coefficient is the `s`-th coefficient of the
`i`-th component. -/
@[simp]
theorem restrictedMvPowerSeriesFinPiEquiv_symm_apply
    (g : Fin n → restrictedMvPowerSeriesSubring k A) (i : Fin n) (s : Fin k →₀ ℕ) :
    ((((restrictedMvPowerSeriesFinPiEquiv k n A).symm g :
        restrictedMvPowerSeriesSubmodule k A (Fin n → A)) :
      MvPowerSeries (Fin k) (Fin n → A)) : (Fin k →₀ ℕ) → Fin n → A) s i =
      ((g i : MvPowerSeries (Fin k) A) : (Fin k →₀ ℕ) → A) s := by
  -- Derived from the forward lemma: the inverse of a composite equivalence does not compute
  -- definitionally the way the forward direction does.
  have h := restrictedMvPowerSeriesFinPiEquiv_apply
    ((restrictedMvPowerSeriesFinPiEquiv k n A).symm g) i s
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- `tensorFinPiEquiv` on a pure tensor is the scalar action componentwise. -/
@[simp]
theorem tensorFinPiEquiv_tmul (m : Fin n → A) (f : restrictedMvPowerSeriesSubring k A) (i : Fin n) :
    tensorFinPiEquiv k n A (TensorProduct.tmul A m f) i = m i • f := by
  simp only [tensorFinPiEquiv, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

/-- **Wedhorn Remark 8.29 for a finite free module**: transported along the two identifications,
the comparison map is Mathlib's tensor-pi equivalence. Both are isomorphisms, so the comparison
map is one too.

The whole content is commutativity of `A`: the tensor side produces `m i * coeff s f` and the
comparison map produces `coeff s f * m i`. -/
@[simp]
theorem restrictedMvPowerSeriesFinPiEquiv_baseChange
    (x : TensorProduct A (Fin n → A) (restrictedMvPowerSeriesSubring k A)) :
    restrictedMvPowerSeriesFinPiEquiv k n A (restrictedMvPowerSeriesBaseChange x) =
      tensorFinPiEquiv k n A x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
      funext i
      apply Subtype.ext
      funext s
      rw [restrictedMvPowerSeriesFinPiEquiv_apply, tensorFinPiEquiv_tmul,
        coeff_restrictedMvPowerSeriesBaseChange_tmul,
        coeff_coe_smul_restrictedMvPowerSeriesSubring]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_comm, MvPowerSeries.coeff_apply]
  | add y z hy hz => simp [hy, hz]

/-- **Remark 8.29 for a finite free module, as an isomorphism.** The comparison map
`restrictedMvPowerSeriesBaseChange` at `M = Fin n → A`, packaged as a linear equivalence; see
`restrictedMvPowerSeriesBaseChangeFinEquiv_apply` for the identification with the map itself. -/
noncomputable def restrictedMvPowerSeriesBaseChangeFinEquiv (k n : ℕ) (A : Type*) [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] :
    TensorProduct A (Fin n → A) (restrictedMvPowerSeriesSubring k A) ≃ₗ[A]
      restrictedMvPowerSeriesSubmodule k A (Fin n → A) :=
  (tensorFinPiEquiv k n A).trans (restrictedMvPowerSeriesFinPiEquiv k n A).symm

/-- The finite free isomorphism *is* the comparison map. -/
@[simp]
theorem restrictedMvPowerSeriesBaseChangeFinEquiv_apply
    (x : TensorProduct A (Fin n → A) (restrictedMvPowerSeriesSubring k A)) :
    restrictedMvPowerSeriesBaseChangeFinEquiv k n A x = restrictedMvPowerSeriesBaseChange x := by
  rw [restrictedMvPowerSeriesBaseChangeFinEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, restrictedMvPowerSeriesFinPiEquiv_baseChange]

/-- **The comparison map is bijective for a finite free module** — Remark 8.29's conclusion in the
base case, in the form a reduction argument consumes. -/
theorem restrictedMvPowerSeriesBaseChange_fin_bijective :
    Function.Bijective (restrictedMvPowerSeriesBaseChange :
      TensorProduct A (Fin n → A) (restrictedMvPowerSeriesSubring k A) →
        restrictedMvPowerSeriesSubmodule k A (Fin n → A)) := by
  have h : (restrictedMvPowerSeriesBaseChange :
      TensorProduct A (Fin n → A) (restrictedMvPowerSeriesSubring k A) →
        restrictedMvPowerSeriesSubmodule k A (Fin n → A)) =
      restrictedMvPowerSeriesBaseChangeFinEquiv k n A :=
    funext fun x ↦ (restrictedMvPowerSeriesBaseChangeFinEquiv_apply x).symm
  rw [h]
  exact (restrictedMvPowerSeriesBaseChangeFinEquiv k n A).bijective

end FiniteFree

end TauCeti.Huber

