/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Kaehler.Polynomial
public import TauCeti.RingTheory.Kaehler.FormallyEtale

/-!
# One-dimensionality of the Kähler differentials of a function field

Let `k` be a field and `F` a field extension of `k` containing an element `x` that is
transcendental over `k` and *separating*, meaning that `F` is separable algebraic over the
subfield `k(x)` it generates. This file proves that the module of Kähler differentials
`Ω[F⁄k]` is then one-dimensional over `F`, with basis the differential `d x`; every
differential is `(dy/dx) · dx` for a unique scalar.

An algebraic function field of one variable with a separating element is the motivating case:
there `F` is moreover finite over `k(x)`, which none of the proofs below needs, so finiteness is
not assumed. Separability is not cosmetic — it is what the base-change argument runs on, and
Stichtenoth's one-dimensional differential module is identified with the Kähler module only
under it — so it is carried as a hypothesis rather than bought with a blanket `PerfectField k`.

The proof is the base-change route: `k(x)/k` is a localization of the polynomial ring, whose
differentials are free of rank one on `d X`, and `F/k(x)` is separable, hence formally étale
(`Algebra.FormallyEtale.of_isSeparable`), so `Ω[F⁄k]` is the base change of `Ω[k(x)⁄k]` along
`k(x) → F` by `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.

## Main results

* `TauCeti.kaehlerBasisRatFunc`: `d X` is a basis of `Ω[k(X)⁄k]`.
* `TauCeti.finrank_kaehlerDifferential_eq_one_of_separating`: `dim_F Ω[F⁄k] = 1`.
* `TauCeti.kaehlerBasisOfSeparating`: `d x` is a basis of `Ω[F⁄k]`.
* `TauCeti.derivativeOfSeparating`: differentiation `y ↦ dy/dx` with respect to `x`, as a
  `k`-derivation of `F`, with `TauCeti.derivativeOfSeparating_smul_D` the identity
  `d y = (dy/dx) · dx` and `TauCeti.eq_derivativeOfSeparating` its uniqueness.

## References

The result is Stichtenoth, *Algebraic Function Fields and Codes*, second edition, GTM 254,
§IV.1: the differential module of a function field with a separating element `x` is
one-dimensional with basis `dx`. The proof here is not his — he builds a differential module by
hand from derivations, whereas this file reads the statement off Mathlib's base-change theory of
Kähler differentials.
-/

public section

noncomputable section

namespace TauCeti

open Module Polynomial KaehlerDifferential

open scoped IntermediateField nonZeroDivisors

variable (k : Type*) [Field k]

/-- `d X` is a basis of the module of Kähler differentials of the rational function field
`k(X)` over `k`. -/
def kaehlerBasisRatFunc : Basis Unit (RatFunc k) Ω[RatFunc k⁄k] :=
  haveI : Algebra.FormallyEtale k[X] (RatFunc k) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc k) (k[X])⁰
  kaehlerBasisOfFormallyEtale k k[X] (RatFunc k)
    ((Basis.singleton Unit k[X]).map (KaehlerDifferential.polynomialEquiv k).symm)

@[simp]
theorem kaehlerBasisRatFunc_apply (i : Unit) :
    kaehlerBasisRatFunc k i = D k (RatFunc k) RatFunc.X := by
  have : Algebra.FormallyEtale k[X] (RatFunc k) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc k) (k[X])⁰
  rw [kaehlerBasisRatFunc, kaehlerBasisOfFormallyEtale_apply]
  simp [KaehlerDifferential.map_D, RatFunc.algebraMap_X]

variable {k} {F : Type*} [Field F] [Algebra k F] {x : F}

/-- The differentials of `F` over `k` are free of rank one on `d x`, for `x` a separating
element. This is the whole content of the file; the public statements below are read off it. -/
private theorem exists_basis_unit_D (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    ∃ b : Basis Unit F Ω[F⁄k], b () = D k F x := by
  -- Realize the rational function field inside `F` along `X ↦ x`, and let `F` carry the
  -- resulting `RatFunc k`-algebra structure; it is separable, hence formally étale.
  let e : RatFunc k ≃ₐ[k] k⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  let : Algebra (RatFunc k) F := (k⟮x⟯.val.comp e.toAlgHom).toRingHom.toAlgebra
  have halg (r : RatFunc k) : algebraMap (RatFunc k) F r = (e r : F) := rfl
  have hX : algebraMap (RatFunc k) F RatFunc.X = x := by
    rw [halg]; exact RatFunc.algEquivOfTranscendental_X x hx
  have : IsScalarTower k (RatFunc k) F :=
    .of_algebraMap_eq fun c ↦ ((k⟮x⟯.val.comp e.toAlgHom).commutes c).symm
  have : Algebra.IsSeparable (RatFunc k) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F)
      (by ext r; simp [halg])
  have : Algebra.FormallyEtale (RatFunc k) F := .of_isSeparable _ _
  refine ⟨kaehlerBasisOfFormallyEtale k (RatFunc k) F (kaehlerBasisRatFunc k), ?_⟩
  rw [kaehlerBasisOfFormallyEtale_apply, kaehlerBasisRatFunc_apply, KaehlerDifferential.map_D, hX]

variable [Algebra.IsSeparable k⟮x⟯ F] (hx : Transcendental k x)
include hx

/-- The differential of a separating element is nonzero. -/
theorem D_ne_zero_of_separating : D k F x ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_basis_unit_D hx
  exact hb ▸ b.ne_zero ()

/-- **The Kähler differentials of a separably generated extension of transcendence degree one
are one-dimensional**: if `x` is transcendental over `k` and `F` is separable over `k(x)`, then
`Ω[F⁄k]` is a one-dimensional `F`-vector space. -/
theorem finrank_kaehlerDifferential_eq_one_of_separating : finrank F Ω[F⁄k] = 1 := by
  obtain ⟨b, -⟩ := exists_basis_unit_D hx
  simpa using finrank_eq_card_basis b

/-- The differential `d x` of a separating element `x` is a basis of `Ω[F⁄k]`; its coordinate
function sends `d y` to the derivative `dy/dx`. -/
def kaehlerBasisOfSeparating (hx : Transcendental k x) : Basis Unit F Ω[F⁄k] :=
  FiniteDimensional.basisSingleton Unit
    (finrank_kaehlerDifferential_eq_one_of_separating hx) (D k F x) (D_ne_zero_of_separating hx)

@[simp]
theorem kaehlerBasisOfSeparating_apply (i : Unit) : kaehlerBasisOfSeparating hx i = D k F x :=
  FiniteDimensional.basisSingleton_apply _ _ _ _ i

/-- The differential of a separating element spans all of `Ω[F⁄k]`. -/
theorem span_D_eq_top_of_separating : Submodule.span F {D k F x} = ⊤ := by
  have h := (kaehlerBasisOfSeparating hx).span_eq
  rwa [Set.range_unique, kaehlerBasisOfSeparating_apply] at h

/-- **Differentiation with respect to a separating element** `x`: the `k`-derivation of `F`
sending `y` to the coordinate `dy/dx` of `d y` in the basis `d x`. Its derivation structure
supplies the sum and product rules and the vanishing on `k`. -/
def derivativeOfSeparating (hx : Transcendental k x) : Derivation k F F :=
  ((kaehlerBasisOfSeparating hx).coord ()).compDer (D k F)

/-- The defining property of `dy/dx`: it is the coordinate of `d y` in the basis `d x`. -/
@[simp]
theorem derivativeOfSeparating_smul_D (y : F) :
    derivativeOfSeparating hx y • D k F x = D k F y := by
  simpa [derivativeOfSeparating] using (kaehlerBasisOfSeparating hx).sum_repr (D k F y)

/-- `dy/dx` is the only scalar taking `d x` to `d y`. -/
theorem eq_derivativeOfSeparating (y c : F) (hc : c • D k F x = D k F y) :
    c = derivativeOfSeparating hx y :=
  smul_left_injective F (D_ne_zero_of_separating hx)
    (hc.trans (derivativeOfSeparating_smul_D hx y).symm)

@[simp]
theorem derivativeOfSeparating_self : derivativeOfSeparating hx x = 1 :=
  (eq_derivativeOfSeparating hx x 1 (one_smul _ _)).symm

end TauCeti
