/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

/-!
# Injective holomorphic maps as partial homeomorphisms

An injective holomorphic map on an open subset of `ℂ` is a biholomorphism onto its image. This
file packages that fact as an `OpenPartialHomeomorph ℂ ℂ`, so conformal-mapping results can carry
their source, target, inverse, and topological equivalence in one existing Mathlib object.

The forward map of `DifferentiableOn.toOpenPartialHomeomorph` is the original function, its source
is the given open set, its target is the image, and its inverse is `Function.invFunOn`. The inverse
is holomorphic by `TauCeti.DifferentiableOn.invFunOn`. Both directions are conformal: injectivity
on an open neighbourhood forces the complex derivative to be nonzero, so Mathlib's
`DifferentiableAt.conformalAt` applies.

This is the packaging prerequisite for the conformal companion to the Riemann mapping theorem.
It advances the `ConformalMapping/README.md` generality-bar requirement to derive packaged
equivalence and `ConformalAt` API from a holomorphic bijection.

## Main declarations

* `TauCeti.DifferentiableOn.toOpenPartialHomeomorph` packages an injective holomorphic map.
* `TauCeti.DifferentiableOn.toHomeomorphOfBijOn` packages a holomorphic bijection between open
  sets as a homeomorphism of their subtypes.
* `TauCeti.DifferentiableOn.conformalAt_of_isOpen_of_injOn` proves its pointwise conformality.
* `TauCeti.DifferentiableOn.conformalAt_toOpenPartialHomeomorph_symm` proves conformality of the
  inverse.

## Coordination with upstream Mathlib

This L0--L3 infrastructure overlaps the Riemann-mapping development in
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505). It is a temporary
shim: replace it with public human-curated Mathlib API, and refactor its consumers, if that
development exports the same packaging.
-/

public section

namespace TauCeti

open Complex Set

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- Package an injective holomorphic map on an open set as an open partial homeomorphism onto its
image.

On the image, `Function.invFunOn f U` selects the unique preimage in `U`; no injectivity of `f`
outside `U` is required. -/
noncomputable def DifferentiableOn.toOpenPartialHomeomorph
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) :
    OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U) hf.continuousOn
    (isOpenMap_restrict_of_differentiableOn_of_injOn hU hf hinj) hU

/-- The source of the partial homeomorphism associated to an injective holomorphic map is its
given domain. -/
@[simp]
theorem DifferentiableOn.toOpenPartialHomeomorph_source
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) :
    (TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj).source = U :=
  (rfl)

/-- The target of the partial homeomorphism associated to an injective holomorphic map is its
image. -/
@[simp]
theorem DifferentiableOn.toOpenPartialHomeomorph_target
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) :
    (TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj).target = f '' U :=
  (rfl)

/-- The partial homeomorphism associated to an injective holomorphic map applies as the original
map. -/
@[simp]
theorem DifferentiableOn.toOpenPartialHomeomorph_apply
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) (z : ℂ) :
    TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj z = f z :=
  (rfl)

/-- The underlying function of the partial homeomorphism associated to an injective holomorphic
map is the original map. -/
@[simp]
theorem DifferentiableOn.toOpenPartialHomeomorph_coe
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) :
    (TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj : ℂ → ℂ) = f :=
  funext (TauCeti.DifferentiableOn.toOpenPartialHomeomorph_apply hf hU hinj)

/-- The inverse of the partial homeomorphism associated to an injective holomorphic map is
`Function.invFunOn` for the specified domain. -/
@[simp]
theorem DifferentiableOn.toOpenPartialHomeomorph_symm_apply
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) (w : ℂ) :
    (TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj).symm w =
      Function.invFunOn f U w :=
  (rfl)

/-- The underlying inverse function of the partial homeomorphism associated to an injective
holomorphic map is `Function.invFunOn` for the specified domain. -/
@[simp]
theorem DifferentiableOn.toOpenPartialHomeomorph_coe_symm
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) :
    ((TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj).symm : ℂ → ℂ) =
      Function.invFunOn f U :=
  funext (TauCeti.DifferentiableOn.toOpenPartialHomeomorph_symm_apply hf hU hinj)

/-- Package a holomorphic bijection from an open set `U` onto a set `V` as a homeomorphism between
the corresponding subtypes.

This is the subtype equivalence carried by
`TauCeti.DifferentiableOn.toOpenPartialHomeomorph`, with its target identified using the supplied
`BijOn` hypothesis. -/
noncomputable def DifferentiableOn.toHomeomorphOfBijOn {V : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hbij : BijOn f U V) : U ≃ₜ V :=
  (TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hbij.injOn)
    |>.homeomorphOfImageSubsetSource
      (by
        rw [TauCeti.DifferentiableOn.toOpenPartialHomeomorph_source hf hU hbij.injOn])
      (by
        simpa only [TauCeti.DifferentiableOn.toOpenPartialHomeomorph_apply hf hU hbij.injOn]
          using hbij.image_eq)

/-- The homeomorphism induced by a holomorphic bijection applies as the original map. -/
@[simp]
theorem DifferentiableOn.toHomeomorphOfBijOn_apply {V : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hbij : BijOn f U V) (z : U) :
    ((TauCeti.DifferentiableOn.toHomeomorphOfBijOn hf hU hbij z : V) : ℂ) = f z :=
  (rfl)

/-- The inverse homeomorphism induced by a holomorphic bijection applies as
`Function.invFunOn`. -/
@[simp]
theorem DifferentiableOn.toHomeomorphOfBijOn_symm_apply {V : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hbij : BijOn f U V) (w : V) :
    (((TauCeti.DifferentiableOn.toHomeomorphOfBijOn hf hU hbij).symm w : U) : ℂ) =
      Function.invFunOn f U w :=
  (rfl)

/-- The inverse of the open partial homeomorphism associated to an injective holomorphic map is
holomorphic on its target. -/
theorem DifferentiableOn.differentiableOn_toOpenPartialHomeomorph_symm
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U) :
    DifferentiableOn ℂ
      (TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj).symm (f '' U) := by
  rw [TauCeti.DifferentiableOn.toOpenPartialHomeomorph_coe_symm hf hU hinj]
  exact TauCeti.DifferentiableOn.invFunOn hf hU hinj

/-- An injective holomorphic map on an open set is conformal at every point of that set. -/
theorem DifferentiableOn.conformalAt_of_isOpen_of_injOn
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U)
    {z : ℂ} (hz : z ∈ U) : ConformalAt f z := by
  exact (hf.analyticAt (hU.mem_nhds hz)).differentiableAt.conformalAt
    (deriv_ne_zero_of_injOn hf hU hinj hz)

/-- The open partial homeomorphism associated to an injective holomorphic map is conformal on its
source. -/
theorem DifferentiableOn.conformalAt_toOpenPartialHomeomorph
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U)
    {z : ℂ} (hz : z ∈ U) :
    ConformalAt (TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj) z := by
  rw [TauCeti.DifferentiableOn.toOpenPartialHomeomorph_coe hf hU hinj]
  exact TauCeti.DifferentiableOn.conformalAt_of_isOpen_of_injOn hf hU hinj hz

/-- The inverse of the open partial homeomorphism associated to an injective holomorphic map is
conformal on its target. -/
theorem DifferentiableOn.conformalAt_toOpenPartialHomeomorph_symm
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hinj : InjOn f U)
    {w : ℂ} (hw : w ∈ f '' U) :
    ConformalAt
      (TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj).symm w := by
  let e := TauCeti.DifferentiableOn.toOpenPartialHomeomorph hf hU hinj
  have hinv : InjOn e.symm (f '' U) := by
    simpa only [e, OpenPartialHomeomorph.symm_source,
      TauCeti.DifferentiableOn.toOpenPartialHomeomorph_target] using e.symm.injOn
  exact TauCeti.DifferentiableOn.conformalAt_of_isOpen_of_injOn
    (TauCeti.DifferentiableOn.differentiableOn_toOpenPartialHomeomorph_symm hf hU hinj)
    (isOpen_image_of_differentiableOn_of_injOn hU hf hinj) hinv hw

end TauCeti
