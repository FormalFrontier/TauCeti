/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.DotAction
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Sign

/-!
# Reflections of the Weyl denominator

The Weyl denominator
`Δ = ∏_{α > 0} (1 - e^{-α})` is alternating under the dot action of the Weyl group. This file
establishes the simple-reflection case, the cancellation step behind the Weyl denominator identity
`Δ = N(0)`.

A simple reflection `sᵢ` permutes all positive roots other than `αᵢ` and sends `αᵢ` to `-αᵢ`.
Consequently its linear action on the integral group algebra sends

`Δ` to `-e^{αᵢ} Δ`.

The dot action includes the compensating translation by `-αᵢ`, so the coefficients of `Δ` at
`x` and `sᵢ ⬝ x` are negatives of one another.

The consequences of that transformation law — in particular the vanishing of a coefficient at a
weight fixed by an odd Weyl-group element, so on a dot-action wall — are proved once for every
alternating element in `TauCeti/LinearAlgebra/RootSystem/Weyl/Alternating.lean`, and reach `Δ`
through `TauCeti.isDotAlternating_weylDenominator`.

## Main results

* `TauCeti.mapDomain_reflection_weylDenominator`: a simple reflection sends `Δ` to
  `-e^{αᵢ} Δ`.
* `TauCeti.coeff_weylDenominator_dotAction`: the coefficient function of `Δ` transforms by the
  sign character under the dot action of the whole Weyl group.

## References

This is the simple-reflection cancellation step in the combinatorial Weyl denominator identity
required by `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, Layer 6 ("the Weyl
character formula").

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)
  [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection permutes the denominator factors away from its own simple root. -/
private lemma prod_erase_reflection_weylDenominator [DecidableEq ι] {i : ι}
    (hi : i ∈ b.support) :
    ∏ j ∈ (posRootsFinset P b).erase i,
        (1 - AddMonoidAlgebra.single (-(P.reflection i) (P.root j)) (1 : ℤ)) =
      ∏ j ∈ (posRootsFinset P b).erase i,
        (1 - AddMonoidAlgebra.single (-P.root j) (1 : ℤ)) := by
  let s := (posRootsFinset P b).erase i
  let e := P.reflectionPerm i
  refine Finset.prod_bij (fun j _ ↦ e j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_erase] at hj ⊢
    have hmap := (bijOn_reflectionPerm_posRoots_diff_singleton P b hi).mapsTo ⟨
      (mem_posRootsFinset P b _).mp hj.2, by simpa using hj.1⟩
    exact ⟨by simpa using hmap.2, (mem_posRootsFinset P b _).mpr hmap.1⟩
  · intro j _ k _ h
    exact e.injective h
  · intro j hj
    rw [Finset.mem_erase] at hj
    have hjset : j ∈ posRoots P b \ {i} := ⟨
      (mem_posRootsFinset P b _).mp hj.2, by simpa using hj.1⟩
    obtain ⟨k, hk, hkj⟩ :=
      (bijOn_reflectionPerm_posRoots_diff_singleton P b hi).surjOn hjset
    refine ⟨k, ?_, hkj⟩
    rw [Finset.mem_erase]
    exact ⟨by simpa using hk.2, (mem_posRootsFinset P b _).mpr hk.1⟩
  · intro j _
    rw [RootPairing.root_reflectionPerm]

/-- **A simple reflection sends the Weyl denominator to `-e^{αᵢ} Δ`.**

The reflection permutes the factors belonging to the positive roots other than `αᵢ`. Its one
exceptional factor changes from `1 - e^{-αᵢ}` to `1 - e^{αᵢ}`, and
`1 - e^{αᵢ} = -e^{αᵢ}(1 - e^{-αᵢ})`. -/
@[simp]
theorem mapDomain_reflection_weylDenominator {i : ι} (hi : i ∈ b.support) :
    AddMonoidAlgebra.mapDomain (P.reflection i) (weylDenominator P b) =
      -AddMonoidAlgebra.single (P.root i) 1 * weylDenominator P b := by
  classical
  let A := AddMonoidAlgebra ℤ M
  let F : ι → A := fun j ↦ 1 - AddMonoidAlgebra.single (-P.root j) 1
  have hiPos : i ∈ posRootsFinset P b :=
    (mem_posRootsFinset P b i).mpr (support_subset_posRoots P b hi)
  -- Read the reflection as a ring homomorphism of the group algebra to distribute over the
  -- product of denominator factors.
  have hring : AddMonoidAlgebra.mapDomain (R := ℤ) (P.reflection i) (weylDenominator P b) =
      AddMonoidAlgebra.mapDomainRingHom ℤ (P.reflection i).toAddEquiv.toAddMonoidHom
        (weylDenominator P b) := rfl
  rw [hring, weylDenominator_def, map_prod]
  simp only [map_sub, map_one, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, map_neg]
  -- `mapDomainRingHom` retains the additive-hom coercion; expose the underlying linear map so
  -- the reflected-root API rewrites the product factors.
  change (∏ x ∈ posRootsFinset P b,
    (1 - AddMonoidAlgebra.single (-(P.reflection i) (P.root x)) 1)) = _
  rw [← Finset.prod_erase_mul (posRootsFinset P b) (fun j ↦
    1 - AddMonoidAlgebra.single (-(P.reflection i) (P.root j)) 1) hiPos]
  rw [prod_erase_reflection_weylDenominator P b hi]
  rw [RootPairing.reflection_apply_self, neg_neg]
  rw [← Finset.prod_erase_mul (posRootsFinset P b) F hiPos]
  dsimp only [F, A]
  have hfactor :
      1 - AddMonoidAlgebra.single (P.root i) (1 : ℤ) =
        -AddMonoidAlgebra.single (P.root i) 1 *
          (1 - AddMonoidAlgebra.single (-P.root i) 1) := by
    rw [mul_sub, mul_one, neg_mul, AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.one_def]
    simp
    ring
  rw [hfactor]
  ring

variable [Invertible (2 : R)]

/-- **The coefficients of the Weyl denominator are alternating under a simple reflection for the
dot action:** the coefficients at `x` and `sᵢ ⬝ x` are negatives of one another.

The translation in the dot action exactly cancels the monomial `e^{αᵢ}` in
`TauCeti.mapDomain_reflection_weylDenominator`. -/
theorem coeff_weylDenominator_dotAction_ofIdx {i : ι} (hi : i ∈ b.support) (x : M) :
    (weylDenominator P b).coeff
        (dotAction P b (RootPairing.weylGroup.ofIdx P i) x) =
      -(weylDenominator P b).coeff x := by
  have h := congrArg (fun f : AddMonoidAlgebra ℤ M ↦
    f.coeff ((P.reflection i) x)) (mapDomain_reflection_weylDenominator P b hi)
  -- Expose the underlying `Finsupp.mapDomain` to read its coefficient at the image of `x`.
  change (Finsupp.mapDomain (P.reflection i) (weylDenominator P b).coeff)
      ((P.reflection i) x) = _ at h
  rw [Finsupp.mapDomain_apply (P.reflection i).injective] at h
  simp only [neg_mul, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul] at h
  rw [dotAction_ofIdx P b hi]
  have harg : -P.root i + (x - P.coroot' i x • P.root i) =
      x - (P.coroot' i x + 1) • P.root i := by
    module
  rw [RootPairing.reflection_apply, harg] at h
  omega

/-- **The coefficients of the Weyl denominator transform by the sign character under the dot
action of the whole Weyl group:**
`[e^{w ⬝ x}] Δ = sgn(w) [e^x] Δ`.

Every Weyl-group element is a product of simple reflections. The result therefore follows by
iterating `TauCeti.coeff_weylDenominator_dotAction_ofIdx`; the parity of the word is recorded by
`TauCeti.weylSign`. -/
@[simp]
theorem coeff_weylDenominator_dotAction (w : P.weylGroup) (x : M) :
    (weylDenominator P b).coeff (dotAction P b w x) =
      (weylSign P b w : ℤ) * (weylDenominator P b).coeff x := by
  obtain ⟨l, rfl⟩ := exists_wordProd_eq P b w
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [wordProd_cons, dotAction_mul,
        coeff_weylDenominator_dotAction_ofIdx P b i.2, ih, map_mul,
        weylSign_ofIdx P b]
      norm_num

end TauCeti
