/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Huber.Restricted.PowerSeries
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import TauCeti.RingTheory.Huber.ClosedSubmodule
import Mathlib.Algebra.FiveLemma
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Base change for restricted power series

Wedhorn's Remark 8.29 compares `M ⊗[A] A⟨T₁, …, Tₖ⟩` with `M⟨T₁, …, Tₖ⟩` for a finitely generated
module `M` over a complete noetherian Tate ring, and finds them isomorphic. This file builds the
comparison map in the generality where it exists — writing it down needs no finiteness and no
completeness, only continuity of the scalar action, beyond the hypotheses the two objects
themselves carry, namely that `A` is nonarchimedean (without which `A⟨T₁, …, Tₖ⟩` is not a
subring) and `ContinuousAdd M` (without which `M⟨T₁, …, Tₖ⟩` is not a submodule) — and then proves
Remark 8.29 by reducing along a strict finite presentation of `M`.

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
* `restrictedMvPowerSeriesSubmoduleMap_baseChange`: the comparison map is **natural in `M`** —
  an `A`-linear map continuous at `0` commutes with base change, which is what lets a
  presentation of `M`
  be pushed through the functor.
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

* `restrictedMvPowerSeriesBaseChange_surjective_of_presentation`: **Remark 8.29's comparison map
  is surjective** for an `M` presented by a surjection `Aᵐ ↠ M` that is continuous at `0` and
  pushes the neighbourhoods of `0` forward. Only the presentation is used — no noetherian
  hypothesis and no property of its kernel, both of which belong to injectivity.

* `restrictedMvPowerSeriesBaseChange_injective_of_presentation`: **the comparison map is
  injective** for an `M` presented by `Aⁿ →[u] Aᵐ →[p] M → 0` whose first map is strict onto its
  image. This is the half surjectivity leaves open, and it is where exactness of the presentation
  is used; it runs on Mathlib's four lemma rather than on a hand-rolled diagram chase. It asks `M`
  to be an `AddCommGroup`, unlike the rest of this file: a diagram chase subtracts.

* `restrictedMvPowerSeriesBaseChange_bijective`: **Remark 8.29** — over a complete noetherian
  Tate ring the comparison map is bijective for every finite `M` with its canonical topology,
  Mathlib's module topology. The two presentation-level halves are applied to the strict
  presentation `TauCeti.Huber.IsTateRing.exists_presentation_isStrictMap_isOpenMap` supplies;
  that is where the Tate, noetherian and completeness hypotheses on `A` enter, and the only place
  they do. Nothing beyond the module topology is asked of `M`.
* `restrictedMvPowerSeriesBaseChangeEquiv`: the same, packaged as
  `M ⊗[A] A⟨T₁, …, Tₖ⟩ ≃ₗ[A] M⟨T₁, …, Tₖ⟩` — the form the Layer 4.1 consequences consume — with
  `restrictedMvPowerSeriesBaseChangeEquiv_apply` identifying it with the comparison map.

The two presentation-level statements hypothesise the topological properties of the presentation,
`hmap` and `hstrict`, rather than deriving them, and so carry no Tate, noetherian or completeness
assumption; the headline theorem is where those are spent.

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

AINTLIB (`github.com/CBirkbeck/AINTLIB` @ `37bbdaeb9`, Apache-2.0), the roadmap's designated prior
formalisation for this layer, **does** have counterparts, and they were consulted rather than
ported: `Adic spaces/RestrictedModule.lean` defines `restrictedModule` and `restrictedModule.map`
at module coefficients with `restrictedModule_map_surjective`, and
`Adic spaces/Wedhorn828.lean` proves `muMap_bijective_of_finite` — Remark 8.29 in full, both
halves, for `Module.Finite A M`.

An earlier revision of this section claimed the opposite. That claim came from grepping this
repository's vocabulary (`restrictedMvPowerSeries`) against a source that names the same objects
`restrictedModule` and `muMap`, and it was wrong.

The hypotheses differ, which is why this is a separate development rather than a port. AINTLIB
fixes `M` to carry the *module topology* and assumes `Module.Finite A M`, deriving openness of
`Aⁿ ↠ M` from its own `IsModuleTopology.isOpenMap_of_surjective_of_finite`, which the pinned
Mathlib does not have; its section variables also include `HasLocLiftPowerBounded`, the typeclass
this repository deliberately replaced. The presentation-level statements here instead take a
strict presentation as a hypothesis and so carry no Tate, noetherian, completeness or
module-topology assumption at all; `restrictedMvPowerSeriesBaseChange_bijective` then discharges
that hypothesis for a finite `M` with its module topology over a complete noetherian Tate ring —
openness of `Aⁿ ↠ M` is now Mathlib's own `IsModuleTopology.isOpenMap_of_surjective`, and
strictness of the relation map comes from this repository's open mapping theorem on `Aᵐ`.

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
when `M` is finitely generated over a complete noetherian Tate ring; that is
`restrictedMvPowerSeriesBaseChange_bijective` below. -/
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

/-- **The comparison map is natural in `M`.** An `A`-linear `φ : M → N` continuous at `0`
commutes with
base change, so a presentation of `M` can be pushed through `M ↦ M⟨T₁, …, Tₖ⟩`. This is the
naturality the finitely generated case of Remark 8.29 runs on. -/
@[simp]
theorem restrictedMvPowerSeriesSubmoduleMap_baseChange {N : Type*} [AddCommMonoid N]
    [TopologicalSpace N] [Module A N] [ContinuousSMul A N] [ContinuousAdd N]
    (φ : M →ₗ[A] N) (hφ : ContinuousAt φ 0)
    (x : TensorProduct A M (restrictedMvPowerSeriesSubring k A)) :
    restrictedMvPowerSeriesSubmoduleMap φ hφ (restrictedMvPowerSeriesBaseChange x) =
      restrictedMvPowerSeriesBaseChange (TensorProduct.map φ LinearMap.id x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
      apply Subtype.ext
      funext s
      simp [coeff_restrictedMvPowerSeriesSubmoduleMap,
        coeff_restrictedMvPowerSeriesBaseChange_tmul]
  | add y z hy hz => simp [hy, hz]

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

/-- **Remark 8.29's comparison map is surjective for a finitely generated module.** If `M` is
presented by a surjection `Aᵐ ↠ M` that is continuous at `0` and pushes the neighbourhoods of `0`
forward, then every restricted series with coefficients in `M` comes from `M ⊗[A] A⟨T₁, …, Tₖ⟩`.

The three ingredients meet here and each supplies one thing. The presentation lifts a restricted
series over `M` to one over `Aᵐ` (`restrictedMvPowerSeriesSubmoduleMap_surjective`, where `hmap` is
what makes the lifted coefficients converge); the finite free case identifies that with a tensor
(`restrictedMvPowerSeriesBaseChange_fin_bijective`); and naturality carries it back down
(`restrictedMvPowerSeriesSubmoduleMap_baseChange`). No noetherian hypothesis and no property of
the kernel are needed — those enter only for *injectivity*, which is the other half of Remark 8.29
and is `restrictedMvPowerSeriesBaseChange_injective_of_presentation`.

`hmap` is stated as the filter inequality the proof consumes rather than as `IsOpenMap p`, which is
strictly stronger: `M` carries `ContinuousAdd` rather than `IsTopologicalAddGroup`, so without
translation invariance global openness does not follow from openness at `0`. A caller holding
`IsOpenMap p` passes `map_zero p ▸ hopen.nhds_le 0`; over a complete Tate ring that open map is
`TauCeti.Huber.IsTateRing.isOpenMap`. -/
theorem restrictedMvPowerSeriesBaseChange_surjective_of_presentation {m : ℕ} {M : Type*}
    [AddCommMonoid M] [TopologicalSpace M] [Module A M] [ContinuousAdd M]
    [ContinuousSMul A M] [(nhds (0 : Fin m → A)).IsCountablyGenerated]
    (p : (Fin m → A) →ₗ[A] M) (hp : ContinuousAt p 0) (hsurj : Function.Surjective p)
    (hmap : nhds (0 : M) ≤ Filter.map p (nhds (0 : Fin m → A))) :
    Function.Surjective (restrictedMvPowerSeriesBaseChange :
      TensorProduct A M (restrictedMvPowerSeriesSubring k A) →
        restrictedMvPowerSeriesSubmodule k A M) := by
  intro y
  obtain ⟨x, hx⟩ := restrictedMvPowerSeriesSubmoduleMap_surjective (k := k) p hp hsurj hmap y
  obtain ⟨z, hz⟩ := (restrictedMvPowerSeriesBaseChange_fin_bijective (k := k) (n := m)).2 x
  exact ⟨TensorProduct.map p LinearMap.id z, by
    rw [← restrictedMvPowerSeriesSubmoduleMap_baseChange p hp z, hz, hx]⟩

/-- **Remark 8.29's comparison map is injective for a finitely generated module.** Given a
presentation `Aⁿ →[u] Aᵐ →[p] M → 0` whose first map is strict onto its image, the comparison map
`M ⊗[A] A⟨T₁, …, Tₖ⟩ → M⟨T₁, …, Tₖ⟩` is injective. With
`restrictedMvPowerSeriesBaseChange_surjective_of_presentation` this gives Remark 8.29,
`restrictedMvPowerSeriesBaseChange_bijective`, once a strict presentation is in hand.

The proof is a four lemma applied to

```
Aⁿ ⊗ A⟨T⟩ ⟶ Aᵐ ⊗ A⟨T⟩ ⟶ M ⊗ A⟨T⟩ ⟶ 0
   ↓            ↓           ↓
Aⁿ⟨T⟩     ⟶ Aᵐ⟨T⟩     ⟶ M⟨T⟩
```

with the comparison map at `Aⁿ`, at `Aᵐ` and at `M` down the sides. Each input is already
available: the top row is exact because tensoring is right exact, the bottom row is
`restrictedMvPowerSeriesSubmoduleMap_range_eq_ker`, the two outer verticals are bijective by
`restrictedMvPowerSeriesBaseChange_fin_bijective`, and the squares commute by
`restrictedMvPowerSeriesSubmoduleMap_baseChange`.

`M` is asked to be an `AddCommGroup`, where the rest of this file works with `AddCommMonoid`: a
diagram chase subtracts, and Mathlib's four lemma is stated over `AddCommGroup` for that reason.
Nothing else here needs it.

`hstrict` is the one input the presentation does not supply. It holds as soon as `range u` is
closed in `Aᵐ`, and over a complete noetherian Tate ring every submodule of a finitely generated
module is closed (`TauCeti.Huber.isClosed_of_isNoetherian`). That deduction is made once, in
`TauCeti.Huber.IsTateRing.exists_presentation_isStrictMap_isOpenMap`; here strictness is
hypothesised, exactly as `restrictedMvPowerSeriesSubmoduleMap_range_eq_ker` hypothesises it, so
that this statement carries no hypothesis on `A` beyond the ambient ones. -/
theorem restrictedMvPowerSeriesBaseChange_injective_of_presentation {m : ℕ} {M : Type*}
    [AddCommGroup M] [TopologicalSpace M] [Module A M] [ContinuousAdd M] [ContinuousSMul A M]
    [(nhds (0 : Fin n → A)).IsCountablyGenerated] (u : (Fin n → A) →ₗ[A] (Fin m → A))
    (hu : ContinuousAt u 0) (p : (Fin m → A) →ₗ[A] M) (hp : ContinuousAt p 0)
    (hsurj : Function.Surjective p) (hexact : LinearMap.range u = LinearMap.ker p)
    (hstrict : nhds (0 : LinearMap.range u) ≤ Filter.map u.rangeRestrict (nhds 0)) :
    Function.Injective (restrictedMvPowerSeriesBaseChange :
      TensorProduct A M (restrictedMvPowerSeriesSubring k A) →
        restrictedMvPowerSeriesSubmodule k A M) :=
  LinearMap.injective_of_surjective_of_injective_of_right_exact
    (LinearMap.rTensor (restrictedMvPowerSeriesSubring k A) u)
    (LinearMap.rTensor (restrictedMvPowerSeriesSubring k A) p)
    (restrictedMvPowerSeriesSubmoduleMap (k := k) u hu)
    (restrictedMvPowerSeriesSubmoduleMap (k := k) p hp)
    restrictedMvPowerSeriesBaseChange restrictedMvPowerSeriesBaseChange
    restrictedMvPowerSeriesBaseChange
    (LinearMap.ext fun x ↦ restrictedMvPowerSeriesSubmoduleMap_baseChange u hu x)
    (LinearMap.ext fun x ↦ restrictedMvPowerSeriesSubmoduleMap_baseChange p hp x)
    (_root_.rTensor_exact (restrictedMvPowerSeriesSubring k A)
      (LinearMap.exact_iff.mpr hexact.symm) hsurj)
    (LinearMap.exact_iff.mpr
      (restrictedMvPowerSeriesSubmoduleMap_range_eq_ker (k := k) u hu p hp hexact hstrict).symm)
    (restrictedMvPowerSeriesBaseChange_fin_bijective (k := k) (n := n)).surjective
    (restrictedMvPowerSeriesBaseChange_fin_bijective (k := k) (n := m)).injective
    (LinearMap.rTensor_surjective _ hsurj)

end FiniteFree

section ModuleFinite

open scoped Uniformity

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [(𝓤 A).IsCountablyGenerated] [T0Space A] [NonarchimedeanRing A] [IsTateRing A]
  [IsNoetherianRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [TopologicalSpace M]
  [ContinuousAdd M] [IsModuleTopology A M]

/-- **Remark 8.29.** Over a complete noetherian Tate ring `A`, the comparison map
`M ⊗[A] A⟨T₁, …, Tₖ⟩ → M⟨T₁, …, Tₖ⟩` is bijective for every finitely generated `A`-module `M`
"endowed with its canonical topology (Proposition 6.18(1))" — Mathlib's module topology,
`IsModuleTopology A M`, which every complete first-countable module topology on `M` is
(`TauCeti.Huber.IsTateRing.isModuleTopology`).

This is Wedhorn's argument as he gives it: choose a presentation `Aⁿ →[u] Aᵐ →[p] M → 0` with `u`
strict and `p` open — `TauCeti.Huber.IsTateRing.exists_presentation_isStrictMap_isOpenMap`, which
is where `A` being Tate, noetherian and complete is spent — and apply the two presentation-level
halves, `restrictedMvPowerSeriesBaseChange_injective_of_presentation` and
`restrictedMvPowerSeriesBaseChange_surjective_of_presentation`. Openness of `p` is passed to the
latter as the filter inequality it consumes, and strictness of `u` to the former as the openness
at `0` of `u.rangeRestrict`, read off through
`LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict`.

No completeness or separation of `M` is assumed: the presentation is open because the module
topology is the quotient topology along `Aᵐ ↠ M`, and strict because its relations have closed
range in `Aᵐ`. `ContinuousAdd M` appears among the hypotheses only because `M⟨T₁, …, Tₖ⟩` is a
submodule under it; it follows from `IsModuleTopology A M` (`IsModuleTopology.toContinuousAdd`),
which instance search cannot use since `A` does not occur in the goal. -/
theorem restrictedMvPowerSeriesBaseChange_bijective :
    Function.Bijective (restrictedMvPowerSeriesBaseChange :
      TensorProduct A M (restrictedMvPowerSeriesSubring k A) →
        restrictedMvPowerSeriesSubmodule k A M) := by
  obtain ⟨n, m, u, p, hu, hp, hsurj, hexact, hstrict, hopen⟩ :=
    IsTateRing.exists_presentation_isStrictMap_isOpenMap (A := A) (M := M)
  exact ⟨restrictedMvPowerSeriesBaseChange_injective_of_presentation u hu.continuousAt p
      hp.continuousAt hsurj (LinearMap.exact_iff.mp hexact).symm (map_zero u.rangeRestrict ▸
        (LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp hstrict).isOpenMap.nhds_le 0),
    restrictedMvPowerSeriesBaseChange_surjective_of_presentation p hp.continuousAt hsurj
      (map_zero p ▸ hopen.nhds_le 0)⟩

variable (k A M) in
/-- **Remark 8.29**, packaged: `M ⊗[A] A⟨T₁, …, Tₖ⟩ ≃ₗ[A] M⟨T₁, …, Tₖ⟩` for a finite module `M`
with its module topology over a complete noetherian Tate ring. This is the form the Layer 4.1
consequences consume; `restrictedMvPowerSeriesBaseChange_bijective` is the content. -/
noncomputable def restrictedMvPowerSeriesBaseChangeEquiv :
    TensorProduct A M (restrictedMvPowerSeriesSubring k A) ≃ₗ[A]
      restrictedMvPowerSeriesSubmodule k A M :=
  LinearEquiv.ofBijective restrictedMvPowerSeriesBaseChange
    restrictedMvPowerSeriesBaseChange_bijective

/-- `restrictedMvPowerSeriesBaseChangeEquiv` *is* the comparison map. -/
@[simp]
theorem restrictedMvPowerSeriesBaseChangeEquiv_apply
    (x : TensorProduct A M (restrictedMvPowerSeriesSubring k A)) :
    restrictedMvPowerSeriesBaseChangeEquiv k A M x = restrictedMvPowerSeriesBaseChange x := by
  simp only [restrictedMvPowerSeriesBaseChangeEquiv, LinearEquiv.ofBijective_apply]

end ModuleFinite

end TauCeti.Huber

