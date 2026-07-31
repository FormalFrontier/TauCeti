/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.Basic

public section

/-!
# The root-level exchange step

Right multiplication by a simple reflection changes the number of positive roots sent to
negative roots by exactly one. Reflection bijects the two inversion sets away from its defining
simple root, while that root itself changes sides.

This is the exchange step that underlies the Coxeter presentation of a Weyl group and the later
identification of Coxeter length with the number of inversions.

## Main results

* `TauCeti.mem_inversions_mul_ofIdx_iff_not_mem` shows that the defining simple root toggles
  membership in the inversion set.
* `TauCeti.ncard_inversions_mul_ofIdx` proves that the inversion count changes by one.

## References

This file implements the exchange target in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The mathematical convention follows
Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (w : P.weylGroup)

variable [CharZero R] (b : P.Base)

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- Membership criterion for the punctured inversion sets: a positive root other than the
reflecting one stays positive and away from it, so only its image needs to be negative. -/
private lemma reflectionPerm_mem_inversions_sdiff (v : P.weylGroup) {i j : ι}
    (hi : i ∈ b.support) (hj : b.IsPos j) (hji : j ≠ i)
    (hneg : ¬ b.IsPos (P.weylGroupToPerm v (P.reflectionPerm i j))) :
    P.reflectionPerm i j ∈ inversions P b v \ {i} :=
  ⟨(mem_inversions P b _ _).mpr ⟨hj.reflectionPerm hi hji, hneg⟩, by
    simpa using reflectionPerm_ne_of_mem_posRoots P b hi ((mem_posRoots P b j).mpr hj)⟩

/-- Away from the distinguished simple root, reflection bijects the inversion sets before and
after right multiplication by that simple reflection. -/
private noncomputable def puncturedInversionsEquiv {i : ι} (hi : i ∈ b.support) :
    ↥(inversions P b (w * RootPairing.weylGroup.ofIdx P i) \ {i}) ≃
      ↥(inversions P b w \ {i}) where
  toFun x := ⟨P.reflectionPerm i x.1, by
    obtain ⟨hx, hxi⟩ := x.2
    have hx' := (mem_inversions P b _ _).mp hx
    refine reflectionPerm_mem_inversions_sdiff P b w hi hx'.1 (by simpa using hxi) ?_
    rw [RootPairing.weylGroupToPerm_mul_ofIdx_apply] at hx'
    exact hx'.2⟩
  invFun x := ⟨P.reflectionPerm i x.1, by
    obtain ⟨hx, hxi⟩ := x.2
    have hx' := (mem_inversions P b _ _).mp hx
    refine reflectionPerm_mem_inversions_sdiff P b (w * RootPairing.weylGroup.ofIdx P i) hi
      hx'.1 (by simpa using hxi) ?_
    rw [RootPairing.weylGroupToPerm_mul_ofIdx_apply, P.reflectionPerm_self]
    exact hx'.2⟩
  left_inv x := by
    apply Subtype.ext
    exact P.reflectionPerm_self i x.1
  right_inv x := by
    apply Subtype.ext
    exact P.reflectionPerm_self i x.1

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- Right multiplication by a simple reflection toggles whether its defining simple root is an
inversion. -/
lemma mem_inversions_mul_ofIdx_iff_not_mem {i : ι} (hi : i ∈ b.support) :
    i ∈ inversions P b (w * RootPairing.weylGroup.ofIdx P i) ↔
      i ∉ inversions P b w := by
  classical
  letI := P.indexNeg
  simp only [mem_inversions, b.isPos_of_mem_support hi, true_and,
    RootPairing.weylGroupToPerm_mul_ofIdx_apply, ← RootPairing.indexNeg_neg,
    RootPairing.weylGroupToPerm_neg, RootPairing.Base.IsPos.neg_iff_not]

/-- Right multiplication by a simple reflection changes the number of inversions by exactly
one. -/
theorem ncard_inversions_mul_ofIdx {i : ι} (hi : i ∈ b.support) :
    (inversions P b (w * RootPairing.weylGroup.ofIdx P i)).ncard =
        (inversions P b w).ncard + 1 ∨
      (inversions P b (w * RootPairing.weylGroup.ofIdx P i)).ncard + 1 =
        (inversions P b w).ncard := by
  classical
  have hpunctured :
      (inversions P b (w * RootPairing.weylGroup.ofIdx P i) \ {i}).ncard =
        (inversions P b w \ {i}).ncard :=
    Set.ncard_congr' (puncturedInversionsEquiv P w b hi)
  by_cases hiw : i ∈ inversions P b w
  · right
    have hiws : i ∉ inversions P b (w * RootPairing.weylGroup.ofIdx P i) := by
      intro h
      exact (mem_inversions_mul_ofIdx_iff_not_mem P w b hi).mp h hiw
    calc
      (inversions P b (w * RootPairing.weylGroup.ofIdx P i)).ncard + 1 =
          (inversions P b (w * RootPairing.weylGroup.ofIdx P i) \ {i}).ncard + 1 := by
            rw [Set.sdiff_singleton_eq_self hiws]
      _ = (inversions P b w \ {i}).ncard + 1 := congrArg (· + 1) hpunctured
      _ = (inversions P b w).ncard :=
        Set.ncard_sdiff_singleton_add_one hiw
  · left
    have hiws : i ∈ inversions P b (w * RootPairing.weylGroup.ofIdx P i) :=
      (mem_inversions_mul_ofIdx_iff_not_mem P w b hi).mpr hiw
    calc
      (inversions P b (w * RootPairing.weylGroup.ofIdx P i)).ncard =
          (inversions P b (w * RootPairing.weylGroup.ofIdx P i) \ {i}).ncard + 1 :=
        (Set.ncard_sdiff_singleton_add_one hiws).symm
      _ = (inversions P b w \ {i}).ncard + 1 := congrArg (· + 1) hpunctured
      _ = (inversions P b w).ncard + 1 := by
        rw [Set.sdiff_singleton_eq_self hiw]

end TauCeti
