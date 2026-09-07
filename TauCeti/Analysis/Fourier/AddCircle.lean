/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# The continuous characters of the circle are the Fourier monomials

Mathlib's `fourier n : C(AddCircle T, ℂ)` is developed as a family of `L²` monomials: the lemmas
about it record how it behaves in the *index* `n` (`fourier_add`, `fourier_neg`) and what it
contributes to the Fourier basis. Read the other way, as a family of *characters* of the group
`AddCircle T` indexed by `n`, the two facts a representation-theoretic consumer needs are that the
family is **faithful** (distinct indices give distinct characters, so the corresponding
one-dimensional representations are pairwise inequivalent) and that it is **exhaustive** (there are
no other continuous characters). This file proves both, and packages them as an isomorphism of
groups between `Multiplicative ℤ` and the Pontryagin dual of the circle group.

Faithfulness is elementary: two monomials already differ at the point `T / 2 / (m - n)`.
Exhaustiveness is where analysis enters. A continuous character `χ` is in particular a nonzero
continuous function, so some Fourier coefficient `fourierCoeff χ n` is nonzero — that is Mathlib's
`fourierBasis`, a Hilbert basis of `L²`, together with the injectivity of the map
`C(AddCircle T, ℂ) → L²`. Translating that coefficient by `y` and using that both `fourier (-n)`
and `χ` turn a sum into a product rewrites `fourierCoeff χ n` as
`fourier (-n) y * χ y * fourierCoeff χ n`, whence `fourier (-n) y * χ y = 1`, and therefore
`χ y = fourier n y`.

Nothing here assumes that `χ` takes values in the unit circle: on a compact group that is
automatic, and here it comes out as a corollary, since a continuous character *is* a Fourier
monomial.

`TauCeti/RepresentationTheory/Compact/Circle.lean` reads this classification for the circle group
`Multiplicative (AddCircle T)`, where it says that the continuous representations of the circle on
`ℂ` are exactly the Fourier ones.

## Main definitions

* `TauCeti.fourierAddChar`: the `n`-th Fourier monomial as a bundled additive character
  `AddChar (AddCircle T) ℂ`.
* `TauCeti.fourierPontryaginDual`: the `n`-th Fourier monomial as an element of the Pontryagin dual
  `PontryaginDual (Multiplicative (AddCircle T))` of the circle group, i.e. as a continuous
  homomorphism to the unit circle.
* `TauCeti.fourierPontryaginDualEquiv`: the resulting isomorphism of groups between
  `Multiplicative ℤ` and that Pontryagin dual.

## Main statements

* `TauCeti.fourier_injective`: `n ↦ fourier n` is injective, so distinct indices give distinct
  characters.
* `ContinuousMap.eq_zero_of_forall_fourierCoeff_eq_zero`: a continuous function on the circle all
  of whose Fourier coefficients vanish is the zero function.
* `AddChar.exists_fourierAddChar_eq`: **every continuous additive character of the circle is a
  Fourier monomial.**
* `AddChar.norm_apply_eq_one_of_continuous`: consequently a continuous additive character of the
  circle takes values of modulus one.

## Tags

Fourier, additive circle, character, Pontryagin dual
-/

public section

open MeasureTheory AddCircle

variable {T : ℝ}

namespace TauCeti

/-- **Distinct indices give distinct Fourier monomials.** At the point `T / 2 / (m - n)` the two
monomials `fourier m` and `fourier n` differ by `Complex.exp (π * I) = -1`, so they are already
different there. Only `T ≠ 0` is needed: for `T = 0` the circle is trivial and every monomial is
the constant `1`. -/
theorem fourier_injective (hT : T ≠ 0) : Function.Injective (fourier (T := T)) := by
  intro m n hmn
  by_contra hne
  have hd : ((m : ℂ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  set y : ℝ := T / 2 / ((m : ℝ) - n) with hy
  have hx : fourier m (y : AddCircle T) = fourier n (y : AddCircle T) := by rw [hmn]
  rw [fourier_coe_apply, fourier_coe_apply] at hx
  have he : 2 * (Real.pi : ℂ) * Complex.I * m * y / T
      - 2 * (Real.pi : ℂ) * Complex.I * n * y / T = (Real.pi : ℂ) * Complex.I := by
    rw [hy]
    push_cast
    field_simp
  have hcontra : (-1 : ℂ) = 1 := by
    calc (-1 : ℂ) = Complex.exp ((Real.pi : ℂ) * Complex.I) := Complex.exp_pi_mul_I.symm
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * y / T)
            / Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * y / T) := by
          rw [← Complex.exp_sub, he]
      _ = 1 := by rw [hx, div_self (Complex.exp_ne_zero _)]
  norm_num at hcontra

/-- **The `n`-th Fourier monomial as a bundled additive character of the circle.** It is Mathlib's
`AddCircle.toCircle_addChar` precomposed with multiplication by `n` and postcomposed with the
inclusion of the unit circle into `ℂ`; `TauCeti.fourierAddChar_apply` identifies its value with
`fourier n`. -/
noncomputable def fourierAddChar (n : ℤ) : AddChar (AddCircle T) ℂ :=
  Circle.coeHom.compAddChar (toCircle_addChar.compAddMonoidHom (zsmulAddGroupHom n))

@[simp]
theorem fourierAddChar_apply (n : ℤ) (x : AddCircle T) :
    fourierAddChar n x = fourier n x := (rfl)

theorem continuous_fourierAddChar (n : ℤ) : Continuous (fourierAddChar (T := T) n) :=
  (fourier n).continuous

/-- **The `n`-th Fourier monomial as an element of the Pontryagin dual of the circle group.** The
circle group is `Multiplicative (AddCircle T)`, and this character sends `x` to
`AddCircle.toCircle (n • x)`, the value of `fourier n` read in the unit circle rather than in `ℂ`;
`TauCeti.coe_fourierPontryaginDual` identifies its value with `fourier n`. -/
noncomputable def fourierPontryaginDual (n : ℤ) :
    PontryaginDual (Multiplicative (AddCircle T)) where
  toFun x := toCircle (n • Multiplicative.toAdd x)
  map_one' := by simp
  map_mul' x y := by rw [toAdd_mul, smul_add, toCircle_add]
  continuous_toFun := (continuous_toCircle.comp (continuous_zsmul n) :
    Continuous fun x : AddCircle T => toCircle (n • x))

@[simp]
theorem coe_fourierPontryaginDual (n : ℤ) (x : Multiplicative (AddCircle T)) :
    (fourierPontryaginDual n x : ℂ) = fourier n (Multiplicative.toAdd x) := (rfl)

/-- Distinct indices give distinct elements of the Pontryagin dual: `TauCeti.fourier_injective`
again. -/
theorem fourierPontryaginDual_injective (hT : T ≠ 0) :
    Function.Injective (fourierPontryaginDual (T := T)) := fun _ _ h =>
  fourier_injective hT (ContinuousMap.ext fun x => by
    simpa using congrArg
      (fun ψ : PontryaginDual (Multiplicative (AddCircle T)) => (ψ (.ofAdd x) : ℂ)) h)

/-- Distinct indices give distinct additive characters: `TauCeti.fourier_injective` again. -/
theorem fourierAddChar_injective (hT : T ≠ 0) :
    Function.Injective (fourierAddChar (T := T)) := fun _ _ h =>
  fourier_injective hT (ContinuousMap.ext fun x => DFunLike.congr_fun h x)

end TauCeti

open TauCeti

variable [Fact (0 < T)]

namespace ContinuousMap

/-- **A continuous function on the circle with vanishing Fourier coefficients is zero.** The
separation statement for the Fourier coefficients of a continuous function, at the level of
`C(AddCircle T, ℂ)` rather than of `L²`; it is what makes a nonzero continuous function have a
nonzero Fourier coefficient. -/
theorem eq_zero_of_forall_fourierCoeff_eq_zero (F : C(AddCircle T, ℂ))
    (h : ∀ n : ℤ, fourierCoeff (⇑F) n = 0) : F = 0 := by
  refine ContinuousMap.toLp_injective (𝕜 := ℂ) (p := 2) haarAddCircle ?_
  refine fourierBasis.repr.injective ?_
  rw [map_zero, map_zero]
  ext n
  rw [fourierBasis_repr, fourierCoeff_toLp, h n]
  rfl

end ContinuousMap

namespace AddChar

/-- **Every continuous additive character of the circle is a Fourier monomial.** Continuity is the
only hypothesis: no unitarity is assumed, and none is needed. Together with
`TauCeti.fourierAddChar_injective` this identifies the continuous characters of `AddCircle T` with
`ℤ`, which is the content of `TauCeti.fourierPontryaginDualEquiv`. -/
theorem exists_fourierAddChar_eq (χ : AddChar (AddCircle T) ℂ) (hχ : Continuous χ) :
    ∃ n : ℤ, fourierAddChar n = χ := by
  have hcoeff : ∀ n : ℤ, fourierCoeff (⇑(⟨χ, hχ⟩ : C(AddCircle T, ℂ))) n
      = ∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle := fun _ => rfl
  have hFne : (⟨χ, hχ⟩ : C(AddCircle T, ℂ)) ≠ 0 := by
    intro h
    have hzero := DFunLike.congr_fun h (0 : AddCircle T)
    simp at hzero
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle ≠ 0 := by
    by_contra hcon
    refine hFne (ContinuousMap.eq_zero_of_forall_fourierCoeff_eq_zero ⟨χ, hχ⟩ fun n => ?_)
    rw [hcoeff n]
    by_contra hne
    exact hcon ⟨n, hne⟩
  refine ⟨n, AddChar.ext _ _ fun y => ?_⟩
  have hfactor : (∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle)
      = (fourier (-n) y * χ y) * ∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle :=
    calc (∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle)
        = ∫ x : AddCircle T, fourier (-n) (x + y) * χ (x + y) ∂haarAddCircle :=
          (integral_add_right_eq_self _ y).symm
      _ = ∫ x : AddCircle T, (fourier (-n) y * χ y) * (fourier (-n) x * χ x) ∂haarAddCircle :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            simp only [← fourierAddChar_apply, AddChar.map_add_eq_mul]; ring)
      _ = (fourier (-n) y * χ y) * ∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle :=
          integral_const_mul _ _
  have hone : fourier (-n) y * χ y = 1 :=
    mul_right_cancel₀ hn (by rw [one_mul]; exact hfactor.symm)
  have hprod : fourier (-n) y * fourier n y = 1 := by
    rw [← fourier_add, neg_add_cancel]
    exact fourier_zero
  have hne0 : fourier (-n) y ≠ 0 := by
    rw [fourier_apply]
    exact Circle.coe_ne_zero _
  exact mul_left_cancel₀ hne0 (hprod.trans hone.symm)

/-- The Fourier index of a continuous additive character of the circle is unique. -/
theorem existsUnique_fourierAddChar_eq (χ : AddChar (AddCircle T) ℂ) (hχ : Continuous χ) :
    ∃! n : ℤ, fourierAddChar n = χ := by
  obtain ⟨n, hn⟩ := exists_fourierAddChar_eq χ hχ
  exact ⟨n, hn, fun m hm =>
    fourierAddChar_injective (Fact.out (p := (0 < T))).ne' (hm.trans hn.symm)⟩

/-- **A continuous additive character of the circle takes values of modulus one.** No unitarity
hypothesis is needed anywhere above: continuity alone forces the character to be a Fourier
monomial, and `fourier n` is valued in the unit circle. -/
theorem norm_apply_eq_one_of_continuous (χ : AddChar (AddCircle T) ℂ) (hχ : Continuous χ)
    (x : AddCircle T) : ‖χ x‖ = 1 := by
  obtain ⟨n, rfl⟩ := exists_fourierAddChar_eq χ hχ
  rw [fourierAddChar_apply, fourier_apply]
  exact Circle.norm_coe _

end AddChar

namespace TauCeti

/-- **The Fourier monomials are the Pontryagin dual of the circle.** The map
`n ↦ fourierPontryaginDual n` is an isomorphism of groups from `Multiplicative ℤ` onto
`PontryaginDual (Multiplicative (AddCircle T))`, the group of continuous characters of the circle
group: it is a homomorphism because `fourier (m + n) = fourier m * fourier n`, injective by
`TauCeti.fourierPontryaginDual_injective`, and surjective by `AddChar.exists_fourierAddChar_eq`.

The multiplicative type tags are what make this a statement about groups: the dual multiplies
characters pointwise, and that multiplication corresponds to addition of Fourier indices. -/
noncomputable def fourierPontryaginDualEquiv :
    Multiplicative ℤ ≃* PontryaginDual (Multiplicative (AddCircle T)) :=
  MulEquiv.ofBijective
    ({ toFun := fun n => fourierPontryaginDual (Multiplicative.toAdd n)
       map_one' := PontryaginDual.ext fun _ => Circle.ext (by simp)
       map_mul' := fun m n => PontryaginDual.ext fun x => Circle.ext <| by
         -- the dual multiplies characters pointwise by definition, so this `change` only
         -- spells the right-hand side out; `fourier_add` then closes the goal through `simp`
         change ((fourierPontryaginDual (Multiplicative.toAdd (m * n)) x : Circle) : ℂ) =
           (fourierPontryaginDual (Multiplicative.toAdd m) x : ℂ) *
             (fourierPontryaginDual (Multiplicative.toAdd n) x : ℂ)
         simp } :
      Multiplicative ℤ →* PontryaginDual (Multiplicative (AddCircle T)))
    ⟨fun _ _ h => Multiplicative.toAdd.injective
        (fourierPontryaginDual_injective (Fact.out (p := (0 < T))).ne' h),
      fun ψ => by
        have hcoe : Continuous ((↑) : Circle → ℂ) := continuous_induced_dom
        have hcont : Continuous fun x : AddCircle T => (ψ (Multiplicative.ofAdd x) : ℂ) :=
          hcoe.comp (map_continuous ψ)
        obtain ⟨n, hn⟩ := AddChar.exists_fourierAddChar_eq
          { toFun := fun x : AddCircle T => (ψ (Multiplicative.ofAdd x) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by rw [ofAdd_add, map_mul, Circle.coe_mul] } hcont
        exact ⟨Multiplicative.ofAdd n, PontryaginDual.ext fun x => Circle.ext (by
          simpa using DFunLike.congr_fun hn (Multiplicative.toAdd x))⟩⟩

@[simp]
theorem fourierPontryaginDualEquiv_apply (n : Multiplicative ℤ) :
    fourierPontryaginDualEquiv (T := T) n = fourierPontryaginDual (Multiplicative.toAdd n) := (rfl)

/-- The inverse of `TauCeti.fourierPontryaginDualEquiv` returns the Fourier index of a continuous
character: the monomial at that index is the character one started from. -/
@[simp]
theorem fourierPontryaginDualEquiv_symm_apply
    (ψ : PontryaginDual (Multiplicative (AddCircle T))) :
    fourierPontryaginDual (Multiplicative.toAdd (fourierPontryaginDualEquiv.symm ψ)) = ψ :=
  fourierPontryaginDualEquiv.apply_symm_apply ψ

end TauCeti
