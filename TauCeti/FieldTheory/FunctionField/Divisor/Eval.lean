/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.FreeAbelianCharacter
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal

/-!
# Evaluating a function on a divisor

For a function `f` and a divisor `D` whose support avoids the zeros and poles of `f`, the
classical quantity

`f(D) = ∏_{P ∈ supp D} N_{F_P/k}(f(P)) ^ (coeff D P)`

is what Weil reciprocity `f(div g) = g(div f)` compares. This file defines it.

The norm is not decoration. `f(P)` lives in the residue field `F_P`, which varies with `P`, so
without pushing each value down to `k` the factors would live in different fields and the product
would not typecheck, let alone mean anything.

**The norm is the classical field norm exactly when `F_P` is finite over `k`.** `Algebra.norm` is
`LinearMap.det` of multiplication, so on a residue field that is *not* module-finite over `k` it
takes Mathlib's junk value `1` (`Algebra.norm_eq_one_of_not_module_finite`), and then so does
`normResidue`. That regime never arises where this API is meant to be used: over a function field
every place has finite residue degree, by `TauCeti.Place.finiteDimensional_residueField`. The
definitions below are stated without a finiteness hypothesis for the reason `TauCeti.Place.degree`
is — the hypothesis would be unused in the term, since `Algebra.norm` does not take one — so the
guarantee is recorded here and in `normResidue`'s own docstring rather than in its signature.

## Main definitions

* `TauCeti.Place.normResidue`: for `f` a unit at `P`, the norm to `k` of the residue `f(P)`, as a
  unit of `k`.
* `TauCeti.Place.normResidueOrOne`: the same, extended by `1` at the places where `f` is not a
  unit, so that it is a total function of the place.
* `TauCeti.Divisor.eval`: `f(D)`, as a unit of `k`.
* `TauCeti.Divisor.IsUnitAtSupport`: the admissibility condition — `f` is a unit at every place of
  `D`. This is exactly disjointness of `D` from the divisor of `f`
  (`isUnitAtSupport_iff_disjoint`).

## Main results

* `TauCeti.Divisor.eval_add`, `eval_neg`, `eval_sub`, `eval_zero`: `f(-)` is a homomorphism from
  the additive group of divisors to `kˣ`, unconditionally.
* `TauCeti.Divisor.eval_eq_prod_normResidue`: on an admissible divisor, the textbook product
  formula.

## Implementation notes

Three choices are load-bearing, and each rules out an alternative that does not work.

**Functions are taken in `Fˣ`, not `F`.** The admissibility condition is `P.ord f = 0`, and
`P.ord 0 = 0` by the junk-value convention on `ord`; so over `F` the condition would declare
`f = 0` admissible at every place. Taking `f : Fˣ` excludes that, and it matches
`TauCeti.Divisor.principal`, which is already stated for `Fˣ`.

**Values are taken in `kˣ`, not `k`, and the neutral value is `1`, not `0`.** The coefficient of a
place is an integer, so the local factor is raised to a possibly negative power, and the divisor law
has to survive that. With `0` as the neutral value in `k` it does not: at a place where `f` is not a
unit, `eval (single P 1) * eval (single P (-1))` would be `0` while `eval 0 = 1`. In `kˣ` every
`zpow` identity holds unconditionally and the law is automatic.

**The definition is total, with the admissibility hypothesis carried by the theorems.** Making the
hypothesis an argument of the definition would put a proof term inside `f(D)`, which then has to be
transported through every rewrite of `D` or `f`, and would block packaging `f(-)` as a homomorphism
at all. Instead `normResidueOrOne` is total, `eval` is a homomorphism outright, and
`eval_eq_prod_normResidue` recovers the textbook formula where the hypothesis holds.

Multiplicativity comes from `TauCeti.freeAbelianCharEquiv`: a divisor is a finitely supported
integer combination of places, so a homomorphism out of it to a commutative group is exactly a
choice of value at each place.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- A function that is a unit at `P` lies in the local ring `𝒪_P`. -/
theorem mem_integers_of_ord_eq_zero (P : Place k F) {f : Fˣ} (hf : P.ord (f : F) = 0) :
    (f : F) ∈ P.integers := by
  rw [P.mem_integers_iff, P.valuation_eq_exp_neg_ord (Units.ne_zero f), hf]
  simp

/-- **The residue `f(P)` of a function that is a unit at `P`**, as a unit of the residue field.
Being a unit is what makes the residue nonzero, which is what lets it be raised to a negative
power below. -/
noncomputable def residueUnit (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) :
    P.ResidueFieldˣ :=
  Units.map (IsLocalRing.residue P.integers)
    ((P.isUnit_iff_ord_eq_zero (Units.ne_zero f)).2
        (show P.ord ((⟨(f : F), P.mem_integers_of_ord_eq_zero hf⟩ : P.integers) : F) = 0 from
          hf)).unit

/-- **The norm to `k` of the residue of a function that is a unit at `P`.** The residue field
varies with `P`; the norm is what puts the value in `k`, the one field all the local factors of
`Divisor.eval` have to share.

This is the classical field norm precisely when `Module.Finite k P.ResidueField` — which
`TauCeti.Place.finiteDimensional_residueField` supplies for every place of a function field. Absent
that, `Algebra.norm` is the junk value `1`
(`Algebra.norm_eq_one_of_not_module_finite`), exactly as `TauCeti.Place.degree` is junk `0` absent
the same hypothesis. The hypothesis is not in the signature because `Algebra.norm` does not consume
one, so requiring it here would leave it unused. -/
noncomputable def normResidue (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) : kˣ :=
  Units.map (Algebra.norm k) (P.residueUnit f hf)

/-- Where the residue field is not finite over `k`, `normResidue` is `1` — the junk value of
`Algebra.norm`, not a field norm. Stated so that the boundary of the classical reading is a
theorem rather than a remark; `Place.finiteDimensional_residueField` rules this case out over a
function field. -/
theorem normResidue_eq_one_of_not_finite {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0)
    (h : ¬Module.Finite k P.ResidueField) : P.normResidue f hf = 1 := by
  ext
  exact Algebra.norm_eq_one_of_not_module_finite h _

/-- `normResidue` extended by `1` where `f` is not a unit, making it a total function of the place.
`1` is the only workable neutral value: see the implementation notes. -/
noncomputable def normResidueOrOne (P : Place k F) (f : Fˣ) : kˣ :=
  if hf : P.ord (f : F) = 0 then P.normResidue f hf else 1

theorem normResidueOrOne_of_ord_eq_zero {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) :
    P.normResidueOrOne f = P.normResidue f hf := by
  simp [normResidueOrOne, hf]

@[simp]
theorem normResidueOrOne_of_ord_ne_zero {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) ≠ 0) :
    P.normResidueOrOne f = 1 := by
  simp [normResidueOrOne, hf]

end Place

namespace Divisor

/-- **Evaluation of a function on divisors**, as a homomorphism from the divisor group written
multiplicatively. Being a homomorphism outright is what makes `eval_add` and `eval_neg`
hypothesis-free. -/
noncomputable def evalHom (f : Fˣ) : Multiplicative (Divisor k F) →* kˣ :=
  (freeAbelianCharEquiv (σ := Place k F) (M := kˣ)).symm fun P ↦ P.normResidueOrOne f

/-- **The value `f(D)` of a function on a divisor.** -/
noncomputable def eval (D : Divisor k F) (f : Fˣ) : kˣ :=
  evalHom f (Multiplicative.ofAdd D)

/-- `f(D)` is the product over the support of the local factors, each raised to its coefficient.

Deliberately **not** `@[simp]`, for the reason recorded on
`WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight`: tagging a defining equation makes
`eval` disappear on sight, which puts `eval_zero`, `eval_neg` and `eval_single` out of
simp-normal form and makes them redundant. The `#lint` environment linter reports exactly those
three if this carries `@[simp]`. -/
theorem eval_eq_finsuppProd (D : Divisor k F) (f : Fˣ) :
    eval D f = D.prod fun P n ↦ P.normResidueOrOne f ^ n := by
  simp [eval, evalHom]

@[simp]
theorem eval_zero (f : Fˣ) : eval (0 : Divisor k F) f = 1 :=
  map_one (evalHom f)

theorem eval_add (D E : Divisor k F) (f : Fˣ) : eval (D + E) f = eval D f * eval E f :=
  map_mul (evalHom f) _ _

@[simp]
theorem eval_neg (D : Divisor k F) (f : Fˣ) : eval (-D) f = (eval D f)⁻¹ :=
  map_inv (evalHom f) _

theorem eval_sub (D E : Divisor k F) (f : Fˣ) : eval (D - E) f = eval D f / eval E f :=
  map_div (evalHom f) _ _

@[simp]
theorem eval_single (P : Place k F) (n : ℤ) (f : Fˣ) :
    eval (Finsupp.single P n : Divisor k F) f = P.normResidueOrOne f ^ n := by
  simp [eval, evalHom]

/-- **`f` is a unit at every place of `D`** — the condition under which `f(D)` is the classical
product and Weil reciprocity is stated. -/
@[expose] def IsUnitAtSupport (D : Divisor k F) (f : Fˣ) : Prop :=
  ∀ P ∈ D.support, P.ord (f : F) = 0

/-- On an admissible divisor, `f(D)` is the textbook product `∏ N(f(P)) ^ n_P`. Indexing by
`D.support` as a subtype carries exactly the membership proof `normResidue` needs. -/
theorem eval_eq_prod_normResidue {D : Divisor k F} {f : Fˣ} (h : IsUnitAtSupport D f) :
    eval D f = ∏ P : D.support, P.1.normResidue f (h P.1 P.2) ^ WeilDivisor.coeff D P.1 := by
  -- the right-hand side depends on the membership proof, so it cannot be matched against a
  -- `Finset` product directly; convert the left-hand side to the subtype product instead.
  calc eval D f = D.prod fun P n ↦ P.normResidueOrOne f ^ n := eval_eq_finsuppProd D f
    _ = ∏ P ∈ D.support, P.normResidueOrOne f ^ WeilDivisor.coeff D P := rfl
    _ = ∏ P : D.support, P.1.normResidueOrOne f ^ WeilDivisor.coeff D P.1 :=
        (Finset.prod_coe_sort _ _).symm
    _ = ∏ P : D.support, P.1.normResidue f (h P.1 P.2) ^ WeilDivisor.coeff D P.1 :=
        Finset.prod_congr rfl fun P _ ↦ by
          rw [Place.normResidueOrOne_of_ord_eq_zero (h P.1 P.2)]

/-- **Admissibility is disjointness from the divisor of `f`.** This is the form the Weil-reciprocity
statement uses, where the two divisors are the principal divisors of the two functions. -/
theorem isUnitAtSupport_iff_disjoint (hF : IsFunctionField k F) (D : Divisor k F) (f : Fˣ) :
    IsUnitAtSupport D f ↔ Disjoint D.support (principal hF f).support := by
  simp only [IsUnitAtSupport, Finset.disjoint_left, mem_support_principal_iff hF]
  exact ⟨fun h P hP => not_not_intro (h P hP), fun h P hP => not_not.1 (h hP)⟩

end Divisor

end TauCeti
