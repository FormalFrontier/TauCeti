/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Alternating
-- Non-public: the reindexing of `ℤ[M]` by a Weyl-group element is an implementation device of the
-- proofs below, never part of the type of an exported declaration.
import Mathlib.Algebra.MonoidAlgebra.MapDomain

public section

/-!
# Weyl-invariant elements of the group algebra of a weight space

An element `f` of the integral group algebra `ℤ[M]` of the weight space of a root pairing is
**Weyl-invariant** when its coefficients are constant on the orbits of the *linear* action of the
Weyl group, `[e^{w x}] f = [e^x] f`. The formal character of a finite-dimensional module over a
semisimple Lie algebra is the motivating example.

The invariants are closed under the ring operations, and the point of this file is how they
interact with the *alternating* elements of
`TauCeti/LinearAlgebra/RootSystem/Weyl/Alternating.lean`, which transform by the sign character
under the shifted **dot** action `w ⬝ x = w(x + ρ) - ρ`: multiplying an alternating element by an
invariant one leaves it alternating (`TauCeti.IsWeylInvariant.mul_isDotAlternating`). That is the
step by which the Weyl character formula gets started, since the product `ch M · Δ` of a formal
character with the Weyl denominator is exactly such a product, and
`TauCeti.IsDotAlternating.eq_weylNumerator` can then identify it as a Weyl numerator from its
coefficients on the open dot chamber alone.

## The two actions

The mismatch between the linear and the dot action is only a translation, and that is what makes
the multiplication statement work. Writing `σ_w` for the reindexing of `ℤ[M]` along `x ↦ w x`, an
invariant element is a fixed point of every `σ_w`, whereas an alternating element satisfies
`e^{wρ - ρ} · σ_w g = sgn(w) · g`. Since `σ_w` is a ring homomorphism, the twisted operator
`h ↦ e^{wρ - ρ} · σ_w h` is linear over the invariants, and multiplying the first identity into
the second is the whole proof.

## Main definitions

* `TauCeti.IsWeylInvariant`: the coefficients of `f` are constant on the orbits of the linear Weyl
  action. `TauCeti.isWeylInvariant_iff` is the preferred way to introduce it and
  `TauCeti.IsWeylInvariant.coeff_smul` the preferred way to eliminate it, so that the definition
  itself need not be unfolded.
* `TauCeti.weylInvariantSubring`: the invariant elements as a subring of `ℤ[M]`.

## Main results

* `TauCeti.IsWeylInvariant.mul_isDotAlternating`: **an invariant element times an alternating
  element is alternating.**
* `TauCeti.isWeylInvariant_zero`, `TauCeti.isWeylInvariant_one`, `TauCeti.IsWeylInvariant.add`,
  `TauCeti.IsWeylInvariant.neg`, `TauCeti.IsWeylInvariant.sub`, `TauCeti.IsWeylInvariant.zsmul`,
  `TauCeti.IsWeylInvariant.mul` and `TauCeti.isWeylInvariant_sum`: the invariants are closed under
  the ring operations of `ℤ[M]`.

## References

This is the "a product of a Weyl-invariant and an alternating element" step of the Weyl character
formula route fixed by Layer 6 ("the Weyl character, dimension, and Kostant formulas") of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`. As with `TauCeti.weylNumerator`
and `TauCeti.weylDenominator`, nothing here needs a Lie algebra, so it is stated for an abstract
root pairing and the Lie-algebra statement is a specialization rather than a rebuild.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.2.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII, §7.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N)

/-! ### Reindexing the group algebra along the linear Weyl action -/

/-- The reindexing of `ℤ[M]` along the linear action of a Weyl-group element, as a ring
isomorphism. Private: it is only a device for relating the linear and the dot action inside the
proofs of this file, and every exported statement is phrased on coefficients instead. -/
private noncomputable def weylReindex (w : P.weylGroup) :
    AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (DistribMulAction.toAddEquiv M w)

private lemma coeff_weylReindex (w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) (x : M) :
    (weylReindex P w f).coeff x = f.coeff (w⁻¹ • x) := by
  simp [weylReindex]

/-! ### Weyl invariance -/

/-- An element of the integral group algebra of the weight space is **Weyl-invariant** when its
coefficients are constant on the orbits of the linear action of the Weyl group,
`[e^{w x}] f = [e^x] f`.

The linear action is used here, not the dot action `w ⬝ x = w(x + ρ) - ρ` of
`TauCeti.IsDotAlternating`: it is the linear action that the weight multiplicity function of a
finite-dimensional module is invariant under. -/
def IsWeylInvariant (f : AddMonoidAlgebra ℤ M) : Prop :=
  ∀ (w : P.weylGroup) (x : M), f.coeff (w • x) = f.coeff x

/-- The defining condition of `TauCeti.IsWeylInvariant`, as an `Iff`: this is the preferred way to
introduce the predicate, and `TauCeti.IsWeylInvariant.coeff_smul` the preferred way to eliminate
it, so that callers need not unfold the definition.

Not a `simp` lemma: unfolding the predicate would dissolve `IsWeylInvariant` out of the goals its
own API is stated about. -/
lemma isWeylInvariant_iff (f : AddMonoidAlgebra ℤ M) :
    IsWeylInvariant P f ↔ ∀ (w : P.weylGroup) (x : M), f.coeff (w • x) = f.coeff x := Iff.rfl

/-- The zero element is invariant. -/
theorem isWeylInvariant_zero : IsWeylInvariant P (0 : AddMonoidAlgebra ℤ M) := by
  intro w x
  simp

/-- The unit of `ℤ[M]` is invariant: it sits at the weight `0`, which every Weyl-group element
fixes. -/
theorem isWeylInvariant_one : IsWeylInvariant P (1 : AddMonoidAlgebra ℤ M) := by
  intro w x
  have h : w • x = 0 ↔ x = 0 := smul_eq_zero_iff_eq w
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  · rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne (h.not.mpr hx), Finsupp.single_eq_of_ne hx]

/-- Invariance is fixedness under every reindexing `TauCeti.weylReindex`; this is the form the
closure under multiplication is read off from. -/
private lemma isWeylInvariant_iff_weylReindex_eq {f : AddMonoidAlgebra ℤ M} :
    IsWeylInvariant P f ↔ ∀ w : P.weylGroup, weylReindex P w f = f := by
  refine ⟨fun hf w ↦ AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ ?_), fun hf w x ↦ ?_⟩
  · rw [coeff_weylReindex, ← hf w⁻¹ x]
  · rw [← congr(($(hf w)).coeff (w • x)), coeff_weylReindex, inv_smul_smul]

section Closure

variable {P} {f g : AddMonoidAlgebra ℤ M}

namespace IsWeylInvariant

/-- The defining identity of an invariant element, as an elimination rule. -/
theorem coeff_smul (hf : IsWeylInvariant P f) (w : P.weylGroup) (x : M) :
    f.coeff (w • x) = f.coeff x := hf w x

/-- A sum of invariant elements is invariant. -/
theorem add (hf : IsWeylInvariant P f) (hg : IsWeylInvariant P g) : IsWeylInvariant P (f + g) := by
  intro w x
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf.coeff_smul w x, hg.coeff_smul w x]

/-- The negative of an invariant element is invariant. -/
theorem neg (hf : IsWeylInvariant P f) : IsWeylInvariant P (-f) := by
  intro w x
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hf.coeff_smul w x]

/-- A difference of invariant elements is invariant. -/
theorem sub (hf : IsWeylInvariant P f) (hg : IsWeylInvariant P g) : IsWeylInvariant P (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- An integer multiple of an invariant element is invariant. -/
theorem zsmul (hf : IsWeylInvariant P f) (c : ℤ) : IsWeylInvariant P (c • f) := by
  intro w x
  simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, hf.coeff_smul w x]

/-- A product of invariant elements is invariant. -/
theorem mul (hf : IsWeylInvariant P f) (hg : IsWeylInvariant P g) : IsWeylInvariant P (f * g) :=
  (isWeylInvariant_iff_weylReindex_eq P).mpr fun w ↦ by
    rw [map_mul, (isWeylInvariant_iff_weylReindex_eq P).mp hf w,
      (isWeylInvariant_iff_weylReindex_eq P).mp hg w]

end IsWeylInvariant

/-- A finite sum of invariant elements is invariant. -/
theorem isWeylInvariant_sum {α : Type*} {s : Finset α} {g : α → AddMonoidAlgebra ℤ M}
    (hg : ∀ a ∈ s, IsWeylInvariant P (g a)) : IsWeylInvariant P (∑ a ∈ s, g a) :=
  Finset.sum_induction g (IsWeylInvariant P) (fun _ _ ha hb ↦ ha.add hb)
    (isWeylInvariant_zero P) hg

variable (P) in
/-- **The Weyl-invariant elements of the integral group algebra `ℤ[M]`, as a subring.** The
closure properties are `TauCeti.isWeylInvariant_zero`, `TauCeti.isWeylInvariant_one`,
`TauCeti.IsWeylInvariant.add`, `TauCeti.IsWeylInvariant.neg` and `TauCeti.IsWeylInvariant.mul`. -/
def weylInvariantSubring : Subring (AddMonoidAlgebra ℤ M) where
  carrier := {f | IsWeylInvariant P f}
  zero_mem' := isWeylInvariant_zero P
  one_mem' := isWeylInvariant_one P
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

/-- Membership in `TauCeti.weylInvariantSubring` is Weyl invariance. -/
@[simp]
lemma mem_weylInvariantSubring : f ∈ weylInvariantSubring P ↔ IsWeylInvariant P f := Iff.rfl

end Closure

/-! ### Invariant multiples of alternating elements -/

section Alternating

variable [Finite ι] [CharZero R] [IsDomain R] [Invertible (2 : R)] [P.IsCrystallographic]
  [P.IsReduced] (b : P.Base)

/-- The reindexing of `ℤ[M]` along the dot action of a Weyl-group element: the linear reindexing
`TauCeti.weylReindex` corrected by the translation `e^{wρ - ρ}` that turns the linear action into
the dot action. Private, like `TauCeti.weylReindex`. -/
private noncomputable def dotReindex (f : AddMonoidAlgebra ℤ M) (w : P.weylGroup) :
    AddMonoidAlgebra ℤ M :=
  AddMonoidAlgebra.single (w • weylVector P b - weylVector P b) 1 * weylReindex P w f

omit [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- The defining property of `TauCeti.dotReindex`: its coefficient at `x` is the coefficient of
`f` at `w⁻¹ ⬝ x`. -/
private lemma coeff_dotReindex (f : AddMonoidAlgebra ℤ M) (w : P.weylGroup) (y : M) :
    (dotReindex P b f w).coeff y = f.coeff (dotAction P b w⁻¹ y) := by
  have hy : w⁻¹ • (-(w • weylVector P b - weylVector P b) + y) = dotAction P b w⁻¹ y := by
    simp only [dotAction_def, neg_sub, smul_add, smul_sub, inv_smul_smul]
    abel
  rw [dotReindex, AddMonoidAlgebra.coeff_single_mul_apply, coeff_weylReindex, one_mul, hy]

variable {P b} {f g : AddMonoidAlgebra ℤ M}

/-- `TauCeti.dotReindex` at `w⁻¹` carries an alternating element to its `sgn(w)`-multiple. -/
private lemma dotReindex_inv_eq_zsmul_of_isDotAlternating (hg : IsDotAlternating P b g)
    (w : P.weylGroup) : dotReindex P b g w⁻¹ = ((weylSign P b w : ℤ)) • g :=
  AddMonoidAlgebra.ext (Finsupp.ext fun y ↦ by
    rw [coeff_dotReindex, inv_inv, hg.coeff_dotAction w y, AddMonoidAlgebra.coeff_smul_apply,
      smul_eq_mul])

/-- **A Weyl-invariant element times an alternating element is alternating.**

This is the mechanism that starts the Weyl character formula: the formal character of a
finite-dimensional module is invariant and the Weyl denominator is alternating
(`TauCeti.isDotAlternating_weylDenominator`), so their product is alternating, which is the
hypothesis `TauCeti.IsDotAlternating.eq_weylNumerator` consumes. -/
theorem IsWeylInvariant.mul_isDotAlternating (hf : IsWeylInvariant P f)
    (hg : IsDotAlternating P b g) : IsDotAlternating P b (f * g) := by
  have hmul : ∀ w : P.weylGroup,
      dotReindex P b (f * g) w = f * dotReindex P b g w := fun w ↦ by
    rw [dotReindex, dotReindex, map_mul, (isWeylInvariant_iff_weylReindex_eq P).mp hf w]
    ring
  refine (isDotAlternating_iff P b _).mpr fun w x ↦ ?_
  calc (f * g).coeff (dotAction P b w x)
      = (dotReindex P b (f * g) w⁻¹).coeff x := by rw [coeff_dotReindex, inv_inv]
    _ = (f * (((weylSign P b w : ℤ)) • g)).coeff x := by
        rw [hmul, dotReindex_inv_eq_zsmul_of_isDotAlternating hg]
    _ = ((weylSign P b w : ℤ)) * (f * g).coeff x := by
        rw [mul_smul_comm, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]

end Alternating

end TauCeti
