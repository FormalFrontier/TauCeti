/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.FreeAbelianCharacter
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
public import TauCeti.FieldTheory.FunctionField.Place.Residue

/-!
# Evaluating a function on a divisor

For a function `f` and a divisor `D` whose support avoids the zeros and poles of `f`, the
classical quantity

`f(D) = ∏_{P ∈ supp D} N_{F_P/k}(f(P)) ^ (coeff D P)`

is what Weil reciprocity `f(div g) = g(div f)` compares. This file defines it. The local factors
`N_{F_P/k}(f(P))` are `TauCeti.Place.normResidueOrOne`, built in
`FieldTheory/FunctionField/Place/Residue.lean`, which also records when the norm is the classical
field norm.

## Main definitions

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
at all. Instead `Place.normResidueOrOne` is total, `eval` is a homomorphism outright, and
`eval_eq_prod_normResidue` recovers the textbook formula where the hypothesis holds.

Multiplicativity comes from `TauCeti.freeAbelianCharEquiv`: a divisor is a finitely supported
integer combination of places, so a homomorphism out of it to a commutative group is exactly a
choice of value at each place.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 — evaluation of a
  function on a divisor of disjoint support is the prerequisite of the divisor construction of the
  Weil pairing given there (III.8.1).
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- **Evaluation of a function on divisors**, as a homomorphism from the divisor group written
multiplicatively. Being a homomorphism outright is what makes `eval_add` and `eval_neg`
hypothesis-free. -/
noncomputable def evalHom (f : Fˣ) : Multiplicative (Divisor k F) →* kˣ :=
  (freeAbelianCharEquiv (σ := Place k F) (M := kˣ)).symm fun P ↦ P.normResidueOrOne f

/-- **The value `f(D)` of a function on a divisor.** -/
noncomputable def eval (D : Divisor k F) (f : Fˣ) : kˣ :=
  evalHom f (Multiplicative.ofAdd D)

-- Deliberately **not** `@[simp]`, for the reason recorded on
-- `WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight`: tagging a defining equation makes
-- `eval` disappear on sight, which puts `eval_zero`, `eval_neg` and `eval_single` out of
-- simp-normal form and makes them redundant. The `#lint` environment linter reports exactly
-- those three if this carries `@[simp]`.
/-- `f(D)` is the product over the support of the local factors, each raised to its coefficient. -/
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
def IsUnitAtSupport (D : Divisor k F) (f : Fˣ) : Prop :=
  ∀ P ∈ D.support, P.ord (f : F) = 0

/-- The interface to `IsUnitAtSupport`: it is exactly the pointwise condition. This is both the
introduction and the elimination rule, so the body of the definition is not exposed. -/
theorem isUnitAtSupport_iff {D : Divisor k F} {f : Fˣ} :
    IsUnitAtSupport D f ↔ ∀ P ∈ D.support, P.ord (f : F) = 0 := Iff.rfl

/-- On an admissible divisor, `f(D)` is the textbook product `∏ N(f(P)) ^ n_P`. Indexing by
`D.support` as a subtype carries exactly the membership proof `normResidue` needs. -/
theorem eval_eq_prod_normResidue {D : Divisor k F} {f : Fˣ} (h : IsUnitAtSupport D f) :
    eval D f
      = ∏ P : D.support, P.1.normResidue f (isUnitAtSupport_iff.1 h P.1 P.2)
          ^ WeilDivisor.coeff D P.1 := by
  -- the right-hand side depends on the membership proof, so it cannot be matched against a
  -- `Finset` product directly; convert the left-hand side to the subtype product instead.
  calc eval D f = D.prod fun P n ↦ P.normResidueOrOne f ^ n := eval_eq_finsuppProd D f
    _ = ∏ P ∈ D.support, P.normResidueOrOne f ^ WeilDivisor.coeff D P := rfl
    _ = ∏ P : D.support, P.1.normResidueOrOne f ^ WeilDivisor.coeff D P.1 :=
        (Finset.prod_coe_sort _ _).symm
    _ = ∏ P : D.support, P.1.normResidue f (isUnitAtSupport_iff.1 h P.1 P.2)
          ^ WeilDivisor.coeff D P.1 :=
        Finset.prod_congr rfl fun P _ ↦ by
          rw [Place.normResidueOrOne_of_ord_eq_zero (isUnitAtSupport_iff.1 h P.1 P.2)]

/-- **Admissibility is disjointness from the divisor of `f`.** This is the form the Weil-reciprocity
statement uses, where the two divisors are the principal divisors of the two functions. -/
theorem isUnitAtSupport_iff_disjoint (hF : IsFunctionField k F) (D : Divisor k F) (f : Fˣ) :
    IsUnitAtSupport D f ↔ Disjoint D.support (principal hF f).support := by
  simp only [isUnitAtSupport_iff, Finset.disjoint_left, mem_support_principal_iff hF]
  exact ⟨fun h P hP => not_not_intro (h P hP), fun h P hP => not_not.1 (h hP)⟩

end Divisor

end TauCeti
