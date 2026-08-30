/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.GroupTheory.QuotientGroup.PowMonoidHom
public import TauCeti.RingTheory.Polynomial.Factors

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The field factors of `K[X] ⧸ (f)` and its square classes

For `f` a nonzero squarefree polynomial over a field `K`, the Chinese Remainder Theorem identifies
`K[X] ⧸ (f)` with the product of the fields `K[X] ⧸ (p)` over the distinct monic irreducible
factors `p` of `f` (`Polynomial.Factors f`). This file records that decomposition, the
projections onto the factors, and the induced decomposition of the group of `n`-th power classes
of units — the group underlying the `2`-Selmer group of an étale algebra.

Throughout, the group of `n`-th power classes of units of a commutative monoid `α` is spelled
as the quotient `αˣ ⧸ (powMonoidHom n).range`, matching
`Mathlib.RingTheory.DedekindDomain.SelmerGroup`; the transport of that quotient along an
equivalence and its compatibility with products are in
`TauCeti.GroupTheory.QuotientGroup.PowMonoidHom`.

## Main definitions

* `AdjoinRoot.equivPiFactors`: `K[X] ⧸ (f) ≃ₐ[K] Π p, K[X] ⧸ (p)`.
* `AdjoinRoot.projFactor`: the projection onto the factor `K[X] ⧸ (p)`, as a `K`-algebra map.
* `AdjoinRoot.modPowEquivPiFactors`: the `n`-th power classes of units of `K[X] ⧸ (f)` are the
  product of those of its field factors.

## Main results

* `AdjoinRoot.isSeparable_of_separable`: each field factor is a separable extension of `K` when
  `f` is separable — the hypothesis `IsIntegralClosure.isDedekindDomain` needs.
* `AdjoinRoot.modPow_mk_eq_one_iff_forall_factors`: a class of units is trivial exactly when all
  its components at the field factors are.

## Implementation notes

`equivPiFactors_mk` and `projFactor_mk` hold by `rfl`, written `(rfl)`: the parenthesised form is
elaborated in this module, where the definitions it unfolds are visible, whereas a bare `rfl`
proof of an exported statement would ask for those definitions to be exposed downstream.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil): the `2`-descent map of the weak
Mordell–Weil theorem lands in the square classes of `K[X] ⧸ (f)` for `f` the Weierstrass cubic, and
is controlled one field factor at a time; `modPowEquivPiFactors` and
`modPow_mk_eq_one_iff_forall_factors` are what let a statement about the classes be checked
componentwise. Nothing here mentions a curve.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `EtaleDecomposition`. The source abbreviates the
group of `n`-th power classes as `Units.modPow`; here it is the quotient directly. The source is
written against Lean `v4.32.0`; this is a forward port.
-/

public section

open Polynomial

/-! ### The field factors of `K[X] ⧸ (f)` -/

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

instance instFiniteDimensional (p : f.Factors) : FiniteDimensional K (AdjoinRoot (p : K[X])) :=
  (powerBasis p.irreducible.ne_zero).finite

lemma minpoly_root_factor (p : f.Factors) : minpoly K (root (p : K[X])) = (p : K[X]) := by
  simpa using AdjoinRoot.minpoly_powerBasis_gen_of_monic p.monic

open IntermediateField in
/-- If `f` is separable, then each field factor of `K[X] ⧸ (f)` is a separable extension of `K`.
This is what `IsIntegralClosure.isDedekindDomain` needs. -/
lemma isSeparable_of_separable (hf : f.Separable) (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) := by
  have hsep : IsSeparable K (root (p : K[X])) := by
    rw [IsSeparable, minpoly_root_factor p]
    exact p.separable hf
  have htop : K⟮root (p : K[X])⟯ = ⊤ :=
    adjoin_eq_top_of_algebra (F := K) (S := {root (p : K[X])}) adjoinRoot_eq_top
  have h := (isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot (p : K[X]))).2 hsep
  rw [htop] at h
  exact (isSeparable_top (F := K) (E := AdjoinRoot (p : K[X]))).mp h

/-- **Chinese Remainder Theorem** for `AdjoinRoot`: for `f` nonzero and squarefree,
`K[X] ⧸ (f)` is the product of the fields `K[X] ⧸ (p)` over the monic irreducible factors `p`
of `f`. -/
noncomputable def equivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot (p : K[X])) :=
  have : Finite f.Factors := Factors.finite hf
  AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (Factors.span_eq_iInf_span hf hsq)).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hpq ↦ Factors.isCoprime_span hpq)
    fun _ ↦ rfl

@[simp]
lemma equivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    equivPiFactors hf hsq (mk f q) p = mk (p : K[X]) q :=
  (rfl)

/-- The projection of `K[X] ⧸ (f)` onto the field factor `K[X] ⧸ (p)`, as a `K`-algebra map. -/
noncomputable def projFactor (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) :
    AdjoinRoot f →ₐ[K] AdjoinRoot (p : K[X]) :=
  (Pi.evalAlgHom K _ p).comp (equivPiFactors hf hsq).toAlgHom

@[simp]
lemma projFactor_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    projFactor hf hsq p (mk f q) = mk (p : K[X]) q :=
  (rfl)

/-! ### Square classes, and `n`-th power classes, of the factors -/

/-- The `n`-th power classes of units of `K[X] ⧸ (f)` are the product of those of its
field factors. -/
noncomputable def modPowEquivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) :
    (AdjoinRoot f)ˣ ⧸ (powMonoidHom n : (AdjoinRoot f)ˣ →* _).range ≃*
      ((p : f.Factors) → (AdjoinRoot (p : K[X]))ˣ ⧸
        (powMonoidHom n : (AdjoinRoot (p : K[X]))ˣ →* _).range) :=
  (QuotientGroup.congrRangePowMonoidHom (Units.mapEquiv (equivPiFactors hf hsq).toMulEquiv) n).trans
    (Units.modPowPiEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X])) n)

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors. -/
@[simp]
lemma modPowEquivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (QuotientGroup.mk u) p =
      QuotientGroup.mk (Units.map (projFactor hf hsq p).toRingHom.toMonoidHom u) := by
  simp only [modPowEquivPiFactors, MulEquiv.trans_apply, QuotientGroup.congrRangePowMonoidHom_mk,
    Units.modPowPiEquiv_mk]
  exact congrArg QuotientGroup.mk (Units.ext rfl)

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors
(`IsUnit.unit` version of `modPowEquivPiFactors_mk`). -/
lemma modPowEquivPiFactors_unit (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) {a : AdjoinRoot f}
    (ha : IsUnit a) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (QuotientGroup.mk ha.unit) p =
      QuotientGroup.mk (ha.map (projFactor hf hsq p)).unit := by
  rw [modPowEquivPiFactors_mk]
  exact congrArg QuotientGroup.mk (Units.ext rfl)

/-- The class of a unit of `K[X] ⧸ (f)` is trivial exactly when its components at all field
factors are trivial. -/
lemma modPow_mk_eq_one_iff_forall_factors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) :
    (QuotientGroup.mk u : (AdjoinRoot f)ˣ ⧸ (powMonoidHom n : (AdjoinRoot f)ˣ →* _).range) = 1 ↔
      ∀ p : f.Factors,
        (QuotientGroup.mk (Units.map (projFactor hf hsq p).toRingHom.toMonoidHom u) :
          (AdjoinRoot (p : K[X]))ˣ ⧸
            (powMonoidHom n : (AdjoinRoot (p : K[X]))ˣ →* _).range) = 1 := by
  rw [← map_eq_one_iff (modPowEquivPiFactors hf hsq n) (modPowEquivPiFactors hf hsq n).injective,
    funext_iff]
  exact forall_congr' fun p ↦ by rw [modPowEquivPiFactors_mk, Pi.one_apply]

end AdjoinRoot

end
