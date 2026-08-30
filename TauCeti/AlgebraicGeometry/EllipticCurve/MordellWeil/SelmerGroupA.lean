/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.BadPrimes
public import TauCeti.RingTheory.DedekindDomain.SelmerGroup
public import TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.Etale

/-!
# Step 6 of the weak Mordell–Weil theorem: the image of the descent map lies in `A(S,2)`

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, let `R` be a Dedekind domain with fraction field `K`, and let `S` be the
set of bad primes of `W` over `R`. The étale algebra `W.A = K[X] ⧸ (f)` splits as a product of
fields `K[X] ⧸ (p)`, one for each monic irreducible factor `p` of `f`, and correspondingly the
square classes `W.M` split as a product. Define `A(S,2)` to be the subgroup of `W.M` of classes
whose component at each factor lies in the `2`-Selmer group of that factor, relative to the
primes lying above `S`.

**Step 6** is `range_μ_le_selmerGroupA`: the image of the descent map `μ` is contained in
`A(S,2)`. Together with Step 4 (`ker_μ_eq`, the kernel is `2E(K)`) and the finiteness of
`A(S,2)`, this is what makes `E(K)/2E(K)` finite.

All the arithmetic has already been done in
`TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.BadPrimes`, which proves that at a prime `w`
of the ring of integers of a factor not lying above a bad prime the `w`-adic valuation of `x - θ`
is even (`even_valuationOfNeZero_sub_root`), and that on the `2`-torsion branch of `μ` the
component is a unit outright (`valuation_projFactor_torsion_eq_one`). What is left, and what this
file does, is to name the Selmer groups, record that evenness *is* Selmer membership
(`mem_selmerGroupFactor_unit_iff`, over `valuationOfNeZeroMod_mk_eq_one_iff`), and assemble the
componentwise statement into one about `W.M` along the decomposition `modPowEquivPiFactors`.

## Main definitions

* `WeierstrassCurve.Affine.selmerGroupFactor`: the `2`-Selmer group of one field factor,
  relative to the primes above the bad primes.
* `WeierstrassCurve.Affine.selmerGroupA`: `A(S,2)`, as a subgroup of `W.M`. This is
  `IsDedekindDomain.selmerGroupOfEquiv` at the decomposition of `W.A` into its field factors; the
  product over the factors is that file's `selmerGroupPi` and is not re-formed here.

## Main results

* `WeierstrassCurve.Affine.mem_selmerGroupFactor_unit_iff`: a class of units lies in the Selmer
  group of a factor exactly when its valuation is even at every good prime.
* `WeierstrassCurve.Affine.μX_component_mem_selmerGroupFactor`: each component of `μX x` lies in
  the Selmer group of its factor.
* `WeierstrassCurve.Affine.range_μ_le_selmerGroupA`: **Step 6**.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil), Step 6 of the weak
Mordell–Weil theorem.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeakMordellWeil.lean`, section `Selmer`. The source states the square
classes as `Units.modPow`, a local abbreviation of its own; this repository carries a single
spelling of square classes, `Mˣ ⧸ (powMonoidHom n).range`, so the statements are re-spelled to it
(see `TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT` for that decision). The source is
written against Lean `v4.32.0`; this is a forward port.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

open IsDedekindDomain

variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to this file, matching `BadPrimes`: for a monic irreducible factor `p` of `f`,
`𝕃 p` is the field factor `K[X] ⧸ (p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding,
and `θ p` is the image of the root `T` of `f` in `𝕃 p`. -/
local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])

section Selmer

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-- The image of the generic `x - T` representative in the field factor `K[X] ⧸ (p)` is `x - θ`.

`private`, and deliberately a named lemma rather than an inlined rewrite chain at its one use
site: `AdjoinRoot.projFactor` is not `@[expose]`, so the chain
`projFactor_mk, map_sub, mk_X, mk_C, algebraMap_eq` cannot be run underneath the `IsUnit.unit`
that the use site presents — `rw` reports `motive is not type correct` together with
`definitions were not unfolded ...: AdjoinRoot.projFactor`. Stated at the top level the equation
elaborates here, where `projFactor` is visible, and applies at the use site by `exact`. -/
private lemma projFactor_mk_C_sub_X (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p (AdjoinRoot.mk W.f (C x - X)) =
      ι p x - θ p := by
  rw [AdjoinRoot.projFactor_mk, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

/-- The image of the `2`-torsion `x - T` representative in the field factor `K[X] ⧸ (p)`.
`private`, for the same reason as `projFactor_mk_C_sub_X`. -/
private lemma projFactor_mk_C_sub_X_add_fCofactor (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p
        (AdjoinRoot.mk W.f (C x - X + W.fCofactor x)) =
      ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x) := by
  rw [AdjoinRoot.projFactor_mk, map_add, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/-- The `2`-Selmer group of the field factor `K[X] ⧸ (p)` of `W.A`, relative to the primes of its
ring of integers lying above the bad primes of `R`. -/
noncomputable def selmerGroupFactor (p : W.f.Factors) :
    Subgroup ((𝕃 p)ˣ ⧸ (powMonoidHom 2 : (𝕃 p)ˣ →* (𝕃 p)ˣ).range) :=
  selmerGroupAbove R (W.ringOfIntegersFactor R p) (𝕃 p) (W.badPrimes R) 2

/-- `A(S,2)`, as a subgroup of `W.M`: the classes whose image in each field factor lies in the
`2`-Selmer group of that factor. Step 6 asserts that `im μ ≤ A(S,2)`.

This is `IsDedekindDomain.selmerGroupOfEquiv` — the Selmer group of an étale algebra transported
along a decomposition into fields — specialised to the decomposition of `W.A` into the factors
`K[X] ⧸ (p)`. Stating it that way rather than re-forming the product and its comap by hand is
what makes `Finite (W.selmerGroupA R)` available directly from
`IsDedekindDomain.finite_selmerGroupOfEquiv`. -/
noncomputable def selmerGroupA : Subgroup W.M :=
  IsDedekindDomain.selmerGroupOfEquiv (fun p : W.f.Factors ↦ 𝕃 p)
    (fun p ↦ W.ringOfIntegersFactor R p)
    (fun p ↦ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) 2
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2)

/-- Membership in `A(S,2)`, componentwise: a square class lies in it exactly when each of its
components along the decomposition of `W.A` into field factors lies in the Selmer group of that
factor. -/
@[simp]
lemma mem_selmerGroupA_iff (m : W.M) :
    m ∈ W.selmerGroupA R ↔ ∀ p : W.f.Factors,
      AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 m p ∈
        W.selmerGroupFactor R p := by
  simp [selmerGroupA, selmerGroupFactor, IsDedekindDomain.selmerGroupAbove_def]

/-- **`A(S,2)` is finite**, given that each factor's ring of integers has finite class group and
finitely generated unit group.

This is the finiteness that bounds the image of the descent map, and hence `E(K)/2E(K)`. -/
theorem finite_selmerGroupA
    [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
    [(p : W.f.Factors) → Monoid.FG (W.ringOfIntegersFactor R p)ˣ] :
    Finite (W.selmerGroupA R) :=
  have : Finite W.f.Factors := Polynomial.Factors.finite W.f_ne_zero
  IsDedekindDomain.finite_selmerGroupOfEquiv (fun p : W.f.Factors ↦ 𝕃 p)
    (fun p ↦ W.ringOfIntegersFactor R p)
    (fun p ↦ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) 2
    (fun p ↦ HeightOneSpectrum.primesAbove_finite R (W.ringOfIntegersFactor R p)
      (W.finite_badPrimes R))
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2)

/-- Membership of the class of a unit in the `2`-Selmer group of a field factor: its valuation is
even at every prime of the ring of integers not lying above a bad prime.

Proved through `mem_selmerGroupAbove_iff` rather than by unfolding: `selmerGroupAbove` is not
`@[expose]`, so its definition is unavailable here, and only its characterising lemma is. -/
@[simp]
lemma mem_selmerGroupFactor_unit_iff (p : W.f.Factors) (u : (𝕃 p)ˣ) :
    (QuotientGroup.mk u : (𝕃 p)ˣ ⧸ (powMonoidHom 2 : (𝕃 p)ˣ →* (𝕃 p)ˣ).range) ∈
        W.selmerGroupFactor R p ↔
      ∀ w : HeightOneSpectrum (W.ringOfIntegersFactor R p),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R) →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  rw [selmerGroupFactor, mem_selmerGroupAbove_iff]
  exact forall₂_congr fun w _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff w 2 u

/-- Generic case of the arithmetic input: `f x ≠ 0`, so the `p`-component of `μX x` is the class
of `x - θ`. -/
lemma mem_selmerGroupFactor_of_eval_f_ne_zero {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) (p : W.f.Factors) :
    (QuotientGroup.mk ((isUnit_mk_sub_X_of_eval_f_ne_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        (𝕃 p)ˣ ⧸ (powMonoidHom 2 : (𝕃 p)ˣ →* (𝕃 p)ˣ).range) ∈ W.selmerGroupFactor R p := by
  rw [W.mem_selmerGroupFactor_unit_iff R p]
  refine W.even_valuationOfNeZero_sub_root R p h hx _ ?_
  exact W.projFactor_mk_C_sub_X x p

/-- `2`-torsion case of the arithmetic input: `f x = 0`.

Projecting the corrected representative to the factor gives `x - θ + fCofactor x`, which by
`valuation_projFactor_torsion_eq_one` is a unit at every prime `w` not lying above a bad prime.
Its valuation is therefore `0`, in particular even. -/
lemma mem_selmerGroupFactor_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) (p : W.f.Factors) :
    (QuotientGroup.mk ((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        (𝕃 p)ˣ ⧸ (powMonoidHom 2 : (𝕃 p)ˣ →* (𝕃 p)ˣ).range) ∈ W.selmerGroupFactor R p := by
  rw [W.mem_selmerGroupFactor_unit_iff R p]
  intro w hw
  set u := ((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
    (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit with hudef
  have hval : w.valuation (𝕃 p) (u : 𝕃 p) = 1 := by
    rw [hudef, IsUnit.unit_spec, W.projFactor_mk_C_sub_X_add_fCofactor x p]
    exact W.valuation_projFactor_torsion_eq_one R p hx hw
  simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1) (by simp [hval])

/-- The heart of Step 6: for a point `(x, y)` of `W` and a field factor `K[X] ⧸ (p)` of `W.A`,
the square class of the image of the `x - T` map lies in the `2`-Selmer group of that factor. -/
lemma μX_component_mem_selmerGroupFactor {x y : K} (h : W.Equation x y) (p : W.f.Factors) :
    AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 (W.μX x) p ∈
      W.selmerGroupFactor R p := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_eq_zero R hx p
  · rw [μX_of_eval_f_ne_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_ne_zero R h hx p

variable [DecidableEq K]

/-- **Step 6 of the weak Mordell–Weil theorem**: the image of the descent map `μ` is contained in
`A(S,2)`. -/
theorem range_μ_le_selmerGroupA : (μ (W := W)).range ≤ W.selmerGroupA R := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [μ_apply]
  match P with
  | 0 => rw [μ₀_zero]; exact one_mem _
  | .some x y h =>
    rw [μ₀_some, mem_selmerGroupA_iff]
    exact fun p ↦ W.μX_component_mem_selmerGroupFactor R h.1 p

end Selmer

end WeierstrassCurve.Affine

end
