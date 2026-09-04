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
`FieldTheory/FunctionField/Place/Residue.lean`.

The construction is total in `F`, and classical exactly where the local norms are: at a place
whose residue field is module-finite over `k`. `TauCeti.Place.finiteDimensional_residueField`
supplies that at every place of an algebraic function field; absent it, `Algebra.norm` is the junk
value `1` and the factor drops out silently, which is the convention `TauCeti.Place.degree`
already follows (junk `0` under the same hypothesis). No result below is stated only in the
classical regime — the divisor and function laws are formal and hold for every `F`.

## Main definitions

* `TauCeti.Divisor.eval`: `f(D)`, as a unit of `k`.
* `TauCeti.Divisor.evalHom`: the same as a bundled homomorphism in the divisor variable, so the
  divisor laws below hold with no admissibility hypothesis.
* `TauCeti.Divisor.IsUnitAtSupport`: the admissibility condition — `f` is a unit at every place of
  `D`. This is exactly disjointness of `D` from the divisor of `f`
  (`isUnitAtSupport_iff_disjoint`).

## Main results

* `TauCeti.Divisor.eval_add`, `eval_neg`, `eval_sub`, `eval_zero`: `f(-)` is a homomorphism from
  the additive group of divisors to `kˣ`, unconditionally.
* `TauCeti.Divisor.eval_eq_prod_normResidue`: on an admissible divisor, the textbook product
  formula.
* `TauCeti.Divisor.eval_one`, `eval_inv`, `eval_mul` and `eval_div`: the group laws in the
  *function* variable. The bundled homomorphism supplies the divisor variable; these supply the
  other one, and
  the two together are the bilinearity Weil reciprocity is stated against. Note the asymmetry:
  `eval_one` and `eval_inv` need no hypothesis, while `eval_mul` and `eval_div` need admissibility
  for both arguments.
* Admissibility is a subgroup condition in *each* variable, which is what makes those laws usable
  together: `isUnitAtSupport_one`, `IsUnitAtSupport.mul`, `isUnitAtSupport_inv_iff` and
  `IsUnitAtSupport.div` in the function, and `isUnitAtSupport_zero`, `IsUnitAtSupport.add`,
  `isUnitAtSupport_neg_iff` and `IsUnitAtSupport.sub` in the divisor. The divisor side is what
  moving a divisor within its class to obtain disjoint support needs.

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

**The definition is total, with admissibility carried by the theorems.** Admissibility depends on
the divisor, so a definition that demanded it could not be a homomorphism in the divisor variable
at all: its domain would shrink with each `f`. Instead `Place.normResidueOrOne` is total, `eval` is
a homomorphism outright, and `eval_eq_prod_normResidue` recovers the textbook formula wherever
admissibility holds.

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

-- Multiplicativity comes from `TauCeti.freeAbelianCharEquiv`: a divisor is a finitely supported
-- integer combination of places, so a homomorphism out of it into a commutative group is exactly
-- a choice of value at each place.
/-- **Evaluation of a function on divisors**, as a homomorphism from the divisor group written
multiplicatively. Being a homomorphism outright is what makes `eval_zero`, `eval_add`, `eval_neg`
and `eval_sub` hypothesis-free. The classical-regime caveat on `TauCeti.Divisor.eval` applies here
unchanged. -/
noncomputable def evalHom (f : Fˣ) : Multiplicative (Divisor k F) →* kˣ :=
  (freeAbelianCharEquiv (σ := Place k F) (M := kˣ)).symm fun P ↦ P.normResidueOrOne f

/-- **The value `f(D)` of a function on a divisor.**

This is the classical quantity exactly where the local factors are: at every place whose residue
field is module-finite over `k`, which `TauCeti.Place.finiteDimensional_residueField` supplies for
every place of an algebraic function field. Absent that, `Algebra.norm` degenerates to `1`
(`Algebra.norm_eq_one_of_not_module_finite`) and the corresponding factor drops out silently. See
`TauCeti.Place.normResidue` for the full statement of the convention, which is the one
`TauCeti.Place.degree` already follows. -/
noncomputable def eval (D : Divisor k F) (f : Fˣ) : kˣ :=
  evalHom f (Multiplicative.ofAdd D)

/-- `eval` is `evalHom` on the multiplicative copy of the divisor group. -/
@[simp]
theorem evalHom_ofAdd (D : Divisor k F) (f : Fˣ) :
    evalHom f (Multiplicative.ofAdd D) = eval D f := by
  rw [eval]

/-- `evalHom` is `eval` on the additive copy of the divisor group. -/
theorem evalHom_apply (D : Multiplicative (Divisor k F)) (f : Fˣ) :
    evalHom f D = eval (Multiplicative.toAdd D) f := by
  rw [← evalHom_ofAdd, ofAdd_toAdd]

-- Deliberately **not** `@[simp]`, for the reason recorded on
-- `WeierstrassCurve.Affine.Point.naiveHeight_eq_logHeight`: tagging a defining equation makes
-- `eval` disappear on sight, which puts `eval_zero`, `eval_neg` and `eval_single` out of
-- simp-normal form and makes them redundant. The `#lint` environment linter reports exactly
-- those three if this carries `@[simp]`.
/-- `f(D)` is the product over the support of the local factors, each raised to its coefficient. -/
theorem eval_eq_finsuppProd (D : Divisor k F) (f : Fˣ) :
    eval D f = D.prod fun P n ↦ P.normResidueOrOne f ^ n := by
  simp only [eval, evalHom, freeAbelianCharEquiv_symm_apply_ofAdd]

/-- `f(0) = 1`: the empty product. -/
@[simp]
theorem eval_zero (f : Fˣ) : eval (0 : Divisor k F) f = 1 :=
  map_one (evalHom f)

/-- `f(D + E) = f(D) · f(E)`: adding divisors multiplies values. -/
@[simp]
theorem eval_add (D E : Divisor k F) (f : Fˣ) : eval (D + E) f = eval D f * eval E f :=
  map_mul (evalHom f) _ _

/-- `f(-D) = f(D)⁻¹`: negating a divisor inverts the value. -/
@[simp]
theorem eval_neg (D : Divisor k F) (f : Fˣ) : eval (-D) f = (eval D f)⁻¹ :=
  map_inv (evalHom f) _

/-- `f(D - E) = f(D) / f(E)`. -/
@[simp]
theorem eval_sub (D E : Divisor k F) (f : Fˣ) : eval (D - E) f = eval D f / eval E f :=
  map_div (evalHom f) _ _

/-- On a single place with multiplicity, `f(n·P)` is the local factor raised to `n`. -/
@[simp]
theorem eval_single (P : Place k F) (n : ℤ) (f : Fˣ) :
    eval (Finsupp.single P n : Divisor k F) f = P.normResidueOrOne f ^ n := by
  simp [eval_eq_finsuppProd]

/-- **`f` is a unit at every place of `D`** — the condition under which `f(D)` is the classical
product and Weil reciprocity is stated. -/
def IsUnitAtSupport (D : Divisor k F) (f : Fˣ) : Prop :=
  ∀ P ∈ D.support, P.ord (f : F) = 0

/-- `IsUnitAtSupport D f` is exactly the pointwise condition `P.ord f = 0` at every place of `D`,
in both directions. -/
@[simp]
theorem isUnitAtSupport_iff {D : Divisor k F} {f : Fˣ} :
    IsUnitAtSupport D f ↔ ∀ P ∈ D.support, P.ord (f : F) = 0 := Iff.rfl

/-- On an admissible divisor, `f(D)` is the textbook product `∏ N(f(P)) ^ n_P`. -/
-- The product is indexed by `D.support` as a subtype because `normResidue` takes the place's
-- membership in the support as an argument.
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

/-- Every function is admissible for the zero divisor, which has empty support. -/
theorem isUnitAtSupport_zero (f : Fˣ) : IsUnitAtSupport (0 : Divisor k F) f := by
  simp

/-- Admissibility is closed under sums of divisors: `(D + E).support ⊆ D.support ∪ E.support`. -/
theorem IsUnitAtSupport.add {D E : Divisor k F} {f : Fˣ} (hD : IsUnitAtSupport D f)
    (hE : IsUnitAtSupport E f) : IsUnitAtSupport (D + E) f := fun P hP ↦ by
  -- `classical` only supplies the `DecidableEq (Place k F)` that `Finsupp.support_add`'s union
  -- mentions; the statement above is unaffected by it.
  classical
  rcases Finset.mem_union.1 (Finsupp.support_add hP) with h | h
  · exact hD P h
  · exact hE P h

/-- Admissibility is *invariant* under negating the divisor, not merely closed under it:
`(-D).support = D.support`. -/
theorem isUnitAtSupport_neg_iff {D : Divisor k F} {f : Fˣ} :
    IsUnitAtSupport (-D) f ↔ IsUnitAtSupport D f := by
  simp only [isUnitAtSupport_iff, Finsupp.support_neg]

/-- Admissibility is closed under differences of divisors. -/
theorem IsUnitAtSupport.sub {D E : Divisor k F} {f : Fˣ} (hD : IsUnitAtSupport D f)
    (hE : IsUnitAtSupport E f) : IsUnitAtSupport (D - E) f := by
  rw [sub_eq_add_neg]
  exact hD.add (isUnitAtSupport_neg_iff.2 hE)

-- None of the four "invariance" closure lemmas — this one, `isUnitAtSupport_inv_iff`,
-- `isUnitAtSupport_zero` and `isUnitAtSupport_neg_iff` — is `@[simp]`, and that is checked rather
-- than assumed: with `isUnitAtSupport_iff` tagged, `simp` proves them outright, and the
-- environment linter reports them as redundant simp lemmas if they carry the attribute. They are
-- kept as named lemmas because they are the closure facts a term-mode proof reaches for.
/-- `1` is admissible for every divisor. -/
theorem isUnitAtSupport_one (D : Divisor k F) : IsUnitAtSupport D (1 : Fˣ) :=
  fun _ _ ↦ by simp

/-- Admissibility is closed under products of functions. -/
theorem IsUnitAtSupport.mul {D : Divisor k F} {f g : Fˣ} (hf : IsUnitAtSupport D f)
    (hg : IsUnitAtSupport D g) : IsUnitAtSupport D (f * g) := fun P hP ↦ by
  rw [Units.val_mul, P.ord_mul (Units.ne_zero f) (Units.ne_zero g), hf P hP, hg P hP, add_zero]

-- Not `@[simp]`, for the reason recorded above `isUnitAtSupport_one`.
/-- Admissibility is *invariant* under inversion, not merely closed under it: `ord_P f⁻¹` vanishes
exactly when `ord_P f` does. -/
theorem isUnitAtSupport_inv_iff {D : Divisor k F} {f : Fˣ} :
    IsUnitAtSupport D f⁻¹ ↔ IsUnitAtSupport D f := by
  simp only [isUnitAtSupport_iff, Units.val_inv_eq_inv_val, Place.ord_inv, neg_eq_zero]

/-- Admissibility is closed under quotients of functions. -/
theorem IsUnitAtSupport.div {D : Divisor k F} {f g : Fˣ} (hf : IsUnitAtSupport D f)
    (hg : IsUnitAtSupport D g) : IsUnitAtSupport D (f / g) := by
  rw [div_eq_mul_inv]
  exact hf.mul (isUnitAtSupport_inv_iff.2 hg)

/-- **`f(D)` is multiplicative in the function**, on a divisor admissible for both factors:
`(f g)(D) = f(D) · g(D)`. This is the half of the divisor/function bilinearity that the
bundled homomorphism behind `eval` does not give for free: it is a homomorphism in `D`, and this
is the statement in `f`.

Both hypotheses are needed. At a place where `f` and `g` have opposite nonzero orders their
product is a unit while neither factor is, so the left side sees a genuine norm there and the
right side sees `1` twice. -/
theorem eval_mul {D : Divisor k F} {f g : Fˣ} (hf : IsUnitAtSupport D f)
    (hg : IsUnitAtSupport D g) : eval D (f * g) = eval D f * eval D g := by
  simp only [eval_eq_finsuppProd, Finsupp.prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P hP ↦ ?_
  rw [Place.normResidueOrOne_mul (hf P hP) (hg P hP), mul_zpow]

/-- `f(D)` at the constant function `1`, needing no hypothesis. -/
@[simp]
theorem eval_one (D : Divisor k F) : eval D (1 : Fˣ) = 1 := by
  simp [eval_eq_finsuppProd]

/-- **`f(D)` inverts with no hypothesis**, unlike `eval_mul`: admissibility is invariant under
inversion (`isUnitAtSupport_inv_iff`), and off the admissible places both sides are `1`. -/
@[simp]
theorem eval_inv (D : Divisor k F) (f : Fˣ) : eval D f⁻¹ = (eval D f)⁻¹ := by
  simp only [eval_eq_finsuppProd, Finsupp.prod, Place.normResidueOrOne_inv, inv_zpow,
    Finset.prod_inv_distrib]

/-- **`f(D)` respects quotients of functions**, on a divisor admissible for both. Like `eval_mul`
and unlike `eval_inv`, this needs both hypotheses: `f / g` can be admissible where neither `f` nor
`g` is. -/
theorem eval_div {D : Divisor k F} {f g : Fˣ} (hf : IsUnitAtSupport D f)
    (hg : IsUnitAtSupport D g) : eval D (f / g) = eval D f / eval D g := by
  rw [div_eq_mul_inv, eval_mul hf (isUnitAtSupport_inv_iff.2 hg), eval_inv, div_eq_mul_inv]

/-- **Admissibility is disjointness from the divisor of `f`.** This is the form the Weil-reciprocity
statement uses, where the two divisors are the principal divisors of the two functions. -/
theorem isUnitAtSupport_iff_disjoint (hF : IsFunctionField k F) (D : Divisor k F) (f : Fˣ) :
    IsUnitAtSupport D f ↔ Disjoint D.support (principal hF f).support := by
  simp only [isUnitAtSupport_iff, Finset.disjoint_left, mem_support_principal_iff hF]
  exact ⟨fun h P hP => not_not_intro (h P hP), fun h P hP => not_not.1 (h hP)⟩

end Divisor

end TauCeti
