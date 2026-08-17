/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.DominantChamber
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

public section

/-!
# The dot action of the Weyl group on weights

The **dot action** of the Weyl group of a base is the linear action conjugated by the translation
by the Weyl vector `ρ`:
`w ⬝ x = w (x + ρ) - ρ`.
It is the action that the highest-weight theory runs on, because it is the linear action recentred
at the point `-ρ` rather than at the origin: `-ρ` is its fixed point
(`TauCeti.dotAction_neg_weylVector`), and a simple reflection acts by
`sᵢ ⬝ x = x - (⟨x, αᵢ^∨⟩ + 1) αᵢ`, so its wall is `⟨x, αᵢ^∨⟩ = -1` instead of `⟨x, αᵢ^∨⟩ = 0`.

Everything about it is a transport of the linear theory along the bijection `x ↦ x + ρ`, and that
is how this file is organized: `TauCeti.dotAction_add_weylVector` is the equivariance of the shift,
and every later statement is read off from a linear one through it. The one place where the dot
action is genuinely better behaved than the linear action is the closed dominant chamber. The
linear action is free only on the *interior* of the chamber — a weight on a wall is fixed by the
reflection in that wall — whereas the dot action is free on the whole closed chamber
(`TauCeti.eq_one_of_dotAction_eq_self_of_mem_dominantChamber`), because the `ρ`-shift of a dominant
weight is strictly dominant. That freeness is the separation statement the highest-weight theory
needs: distinct dominant weights lie in distinct dot orbits.

## Main definitions

* `TauCeti.dotAction`: the dot action `w ⬝ x = w (x + ρ) - ρ` of a Weyl-group element on a weight.
* `TauCeti.dotActionPerm`: the same, packaged as a group homomorphism into `Equiv.Perm M`. The dot
  action is not registered as a `MulAction` instance, since the weight space already carries the
  linear action of the Weyl group.

## Main results

* `TauCeti.dotAction_add_weylVector`: `w ⬝ x + ρ = w (x + ρ)`, the equivariance of the `ρ`-shift,
  from which the action laws `TauCeti.dotAction_one` and `TauCeti.dotAction_mul` follow.
* `TauCeti.dotAction_ofIdx`: a simple reflection acts by `sᵢ ⬝ x = x - (⟨x, αᵢ^∨⟩ + 1) αᵢ`, and
  `TauCeti.coroot'_dotAction_ofIdx`: it sends the pairing `⟨x, αᵢ^∨⟩` to `-⟨x, αᵢ^∨⟩ - 2`.
* `TauCeti.dotAction_ofIdx_eq_self_iff`: the wall of `sᵢ` for the dot action is `⟨x, αᵢ^∨⟩ = -1`.
* `TauCeti.eq_one_of_dotAction_mem_dominantChamber` and
  `TauCeti.eq_one_of_dotAction_eq_self_of_mem_dominantChamber`: **the dot action is free on the
  closed dominant chamber**, and no nontrivial element keeps a dominant weight dominant.
* `TauCeti.eq_of_dotAction_eq_of_mem_dominantChamber` and
  `TauCeti.dotAction_eq_dotAction_iff_of_mem_dominantChamber`: **a dominant weight is the only
  dominant weight in its dot orbit**, and it is reached by a unique Weyl-group element.

## Implementation notes

The dot action is deliberately *not* a `MulAction` instance on `M`: the weight space already
carries the linear action of `P.weylGroup`, and a second instance on the same pair of types would
be ambiguous. The action laws are therefore stated as plain lemmas, and
`TauCeti.dotActionPerm` collects them into a group homomorphism for consumers that want to speak of
orbits or stabilizers.

The definition needs `2` to be invertible in the coefficient ring, since `ρ` does; nothing else
here asks for more than the statement it appears in. In particular the action laws and the
`ρ`-shift equivariance are proved with no crystallographic, reduced or order hypothesis, the
simple-reflection formulas add only what `TauCeti.reflection_weylVector` needs, and the ordered
hypotheses appear only in the dominant-chamber section.

## References

This file supplies the root-pairing-level prerequisite of the `dotAction` target of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose Layer 7 states "the **dot
action** `w · λ = w(λ+ρ) - ρ` is the linear Weyl action recentred at `-ρ`" and whose
`Suggested.lean` pins `dotAction (base) (w) (lam)` on `Module.Dual K H`; as with
`TauCeti.weylVector`, the combinatorics lives at the level of an abstract root pairing, so the
Lie-algebra target is a specialization rather than a rebuild. The freeness on the closed dominant
chamber is what the roadmap's `centralCharacter_injOn_isDominantIntegral` consumes.

The argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, Ch. III, §13.2 and Ch. VI, §23.3.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N)

variable [CharZero R] (b : P.Base) [Finite ι] [Invertible (2 : R)]

/-! ### The dot action and its action laws -/

/-- **The dot action** of the Weyl group on weights: `w ⬝ x = w (x + ρ) - ρ`, the linear action
conjugated by the translation by the Weyl vector `TauCeti.weylVector`.

This is not a `MulAction` instance: the weight space already carries the linear action of the Weyl
group, and the two would be ambiguous. `TauCeti.dotActionPerm` packages the action laws as a group
homomorphism. -/
noncomputable def dotAction (w : P.weylGroup) (x : M) : M :=
  w • (x + weylVector P b) - weylVector P b

/-- The dot action is the linear action conjugated by the translation by `ρ`, by definition. -/
lemma dotAction_def (w : P.weylGroup) (x : M) :
    dotAction P b w x = w • (x + weylVector P b) - weylVector P b := by
  rw [dotAction]

/-- **The `ρ`-shift is equivariant** from the dot action to the linear action: `w ⬝ x + ρ` is
`w (x + ρ)`. Every statement below is read off from a linear statement through this identity. -/
theorem dotAction_add_weylVector (w : P.weylGroup) (x : M) :
    dotAction P b w x + weylVector P b = w • (x + weylVector P b) := by
  rw [dotAction_def, sub_add_cancel]

/-- The dot action of a Weyl-group element on `x`, compared with a candidate value `y`, is the
linear action compared on the `ρ`-shifts. -/
theorem dotAction_eq_iff {w : P.weylGroup} {x y : M} :
    dotAction P b w x = y ↔ w • (x + weylVector P b) = y + weylVector P b := by
  rw [← dotAction_add_weylVector P b w x, add_left_inj]

/-- The identity acts trivially for the dot action. -/
@[simp]
theorem dotAction_one (x : M) : dotAction P b 1 x = x := by
  rw [dotAction_def, one_smul, add_sub_cancel_right]

/-- The dot action is an action: it turns multiplication in the Weyl group into composition. -/
theorem dotAction_mul (v w : P.weylGroup) (x : M) :
    dotAction P b (v * w) x = dotAction P b v (dotAction P b w x) := by
  rw [dotAction_def, dotAction_def P b v, dotAction_add_weylVector, mul_smul]

/-- Undoing the dot action of `w` by the dot action of `w⁻¹`. -/
@[simp]
theorem dotAction_inv_dotAction (w : P.weylGroup) (x : M) :
    dotAction P b w⁻¹ (dotAction P b w x) = x := by
  rw [← dotAction_mul, inv_mul_cancel, dotAction_one]

/-- Undoing the dot action of `w⁻¹` by the dot action of `w`. -/
@[simp]
theorem dotAction_dotAction_inv (w : P.weylGroup) (x : M) :
    dotAction P b w (dotAction P b w⁻¹ x) = x := by
  rw [← dotAction_mul, mul_inv_cancel, dotAction_one]

/-- **The dot action, as a group homomorphism into the permutations of the weight space.** This is
the packaging of `TauCeti.dotAction_one` and `TauCeti.dotAction_mul` that lets a consumer speak of
dot orbits and dot stabilizers without a second `MulAction` instance on the weight space. -/
noncomputable def dotActionPerm : P.weylGroup →* Equiv.Perm M where
  toFun w :=
    { toFun := dotAction P b w
      invFun := dotAction P b w⁻¹
      left_inv := dotAction_inv_dotAction P b w
      right_inv := dotAction_dotAction_inv P b w }
  map_one' := Equiv.ext fun x ↦ dotAction_one P b x
  map_mul' v w := Equiv.ext fun x ↦ dotAction_mul P b v w x

@[simp]
lemma dotActionPerm_apply (w : P.weylGroup) (x : M) :
    dotActionPerm P b w x = dotAction P b w x := (rfl)

@[simp]
lemma dotActionPerm_symm_apply (w : P.weylGroup) (x : M) :
    (dotActionPerm P b w).symm x = dotAction P b w⁻¹ x := (rfl)

/-- The dot action of a Weyl-group element is injective on weights. -/
theorem dotAction_injective (w : P.weylGroup) : Function.Injective (dotAction P b w) :=
  (dotActionPerm P b w).injective

/-- **The dot action is faithful.** A Weyl-group element fixing every weight for the dot action
fixes every weight for the linear action, hence is the identity. -/
theorem dotActionPerm_injective : Function.Injective (dotActionPerm P b) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ ?_
  refine _root_.TauCeti.RootPairing.weylGroup.eq_one_of_smul_eq_self fun y ↦ ?_
  have h := congrArg (fun e : Equiv.Perm M ↦ e (y - weylVector P b)) hw
  simp only [dotActionPerm_apply, Equiv.Perm.coe_one, id_eq] at h
  rw [dotAction_eq_iff, sub_add_cancel] at h
  exact h

/-- **`-ρ` is the fixed point of the dot action**: the dot action is the linear action recentred
there. -/
@[simp]
theorem dotAction_neg_weylVector (w : P.weylGroup) :
    dotAction P b w (-weylVector P b) = -weylVector P b := by
  rw [dotAction_def, neg_add_cancel, smul_zero, zero_sub]

/-- A Weyl-group element fixes a weight for the dot action exactly when it fixes its `ρ`-shift for
the linear action. -/
theorem dotAction_eq_self_iff {w : P.weylGroup} {x : M} :
    dotAction P b w x = x ↔ w • (x + weylVector P b) = x + weylVector P b :=
  dotAction_eq_iff P b

/-! ### Simple reflections -/

/-- A simple reflection is an involution for the dot action, as it is for the linear one. -/
theorem dotAction_ofIdx_involutive (i : ι) :
    Function.Involutive (dotAction P b (_root_.RootPairing.weylGroup.ofIdx P i)) := fun x ↦ by
  rw [← dotAction_mul, _root_.TauCeti.RootPairing.weylGroup.ofIdx_mul_self, dotAction_one]

section Reduced

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **A simple reflection acts by `sᵢ ⬝ x = x - (⟨x, αᵢ^∨⟩ + 1) αᵢ`** for the dot action: the
linear formula with the pairing raised by one. -/
theorem dotAction_ofIdx {i : ι} (hi : i ∈ b.support) (x : M) :
    dotAction P b (_root_.RootPairing.weylGroup.ofIdx P i) x
      = x - (P.coroot' i x + 1) • P.root i := by
  rw [dotAction_def, _root_.RootPairing.weylGroup.ofIdx_smul,
    _root_.RootPairing.Equiv.reflection_smul]
  exact reflection_add_weylVector_sub_weylVector P b hi x

/-- **A simple reflection sends the pairing `⟨x, αᵢ^∨⟩` to `-⟨x, αᵢ^∨⟩ - 2`** for the dot action.
For `sl₂`, where `α^∨` is the standard coroot, this is the statement that the dot action of the
nontrivial Weyl element sends the weight `m` to `-m - 2`. -/
theorem coroot'_dotAction_ofIdx {i : ι} (hi : i ∈ b.support) (x : M) :
    P.coroot' i (dotAction P b (_root_.RootPairing.weylGroup.ofIdx P i) x)
      = -P.coroot' i x - 2 := by
  rw [dotAction_ofIdx P b hi, map_sub, map_smul, smul_eq_mul,
    _root_.RootPairing.root_coroot'_eq_pairing, _root_.RootPairing.pairing_same]
  ring

/-- **The wall of `sᵢ` for the dot action is `⟨x, αᵢ^∨⟩ = -1`**, not `⟨x, αᵢ^∨⟩ = 0`: the dot
action is the linear action recentred at `-ρ`, and `⟨ρ, αᵢ^∨⟩ = 1`. -/
theorem dotAction_ofIdx_eq_self_iff {i : ι} (hi : i ∈ b.support) (x : M) :
    dotAction P b (_root_.RootPairing.weylGroup.ofIdx P i) x = x ↔ P.coroot' i x = -1 := by
  rw [dotAction_ofIdx P b hi, sub_eq_self]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h2 := congrArg (P.coroot' i) h
    rw [map_smul, smul_eq_mul, _root_.RootPairing.root_coroot'_eq_pairing,
      _root_.RootPairing.pairing_same, map_zero] at h2
    have h3 := congrArg (fun r : R ↦ r * ⅟(2 : R)) h2
    simp only [mul_assoc, mul_invOf_self, mul_one, zero_mul] at h3
    exact eq_neg_of_add_eq_zero_left h3
  · rw [h, neg_add_cancel, zero_smul]

end Reduced

/-! ### Freeness on the dominant chamber -/

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R] [P.IsCrystallographic] [P.IsReduced]

/-- The `ρ`-shift of a weight whose dot translate is dominant is carried into the closed dominant
chamber by the linear action. This is the bridge to the linear freeness statements. -/
theorem smul_add_weylVector_mem_dominantChamber {w : P.weylGroup} {x : M}
    (hw : dotAction P b w x ∈ dominantChamber P b) :
    w • (x + weylVector P b) ∈ dominantChamber P b := by
  rw [← dotAction_add_weylVector]
  exact add_mem_dominantChamber P b hw
    (openDominantChamber_subset_dominantChamber P b (weylVector_mem_openDominantChamber P b))

variable [P.flip.IsReduced]

/-- **A Weyl-group element carrying a dominant weight to a dominant weight for the dot action is
the identity.** Unlike the linear action, where a weight on a wall of the chamber is fixed by the
reflection in that wall, the dot action leaves the closed dominant chamber no room: the `ρ`-shift
of a dominant weight is *strictly* dominant, and the linear action is free there. -/
theorem eq_one_of_dotAction_mem_dominantChamber (w : P.weylGroup) {x : M}
    (hx : x ∈ dominantChamber P b) (hw : dotAction P b w x ∈ dominantChamber P b) : w = 1 :=
  eq_one_of_smul_mem_dominantChamber P b w (add_weylVector_mem_openDominantChamber P b hx)
    (smul_add_weylVector_mem_dominantChamber P b hw)

/-- **The dot action is free on the closed dominant chamber**: a Weyl-group element fixing a
dominant weight for the dot action is the identity. -/
theorem eq_one_of_dotAction_eq_self_of_mem_dominantChamber (w : P.weylGroup) {x : M}
    (hx : x ∈ dominantChamber P b) (hw : dotAction P b w x = x) : w = 1 :=
  eq_one_of_dotAction_mem_dominantChamber P b w hx (by rw [hw]; exact hx)

/-- A Weyl-group element carrying a dominant weight to a dominant weight for the dot action fixes
it. -/
theorem dotAction_eq_self_of_mem_dominantChamber (w : P.weylGroup) {x : M}
    (hx : x ∈ dominantChamber P b) (hw : dotAction P b w x ∈ dominantChamber P b) :
    dotAction P b w x = x := by
  rw [eq_one_of_dotAction_mem_dominantChamber P b w hx hw, dotAction_one]

/-- **A dominant weight is the only dominant weight in its dot orbit.** This is the separation
statement the highest-weight theory consumes: two dominant weights with the same central character
lie in one dot orbit, hence are equal. -/
theorem eq_of_dotAction_eq_of_mem_dominantChamber {w : P.weylGroup} {x y : M}
    (hx : x ∈ dominantChamber P b) (hy : y ∈ dominantChamber P b)
    (h : dotAction P b w x = y) : y = x := by
  rw [← h]
  exact dotAction_eq_self_of_mem_dominantChamber P b w hx (h ▸ hy)

/-- **The dot action separates dominant weights, and does so with a unique Weyl-group element.**
Two dot translates of dominant weights agree exactly when the weights agree and the Weyl-group
elements agree; in particular distinct dominant weights lie in distinct dot orbits. -/
theorem dotAction_eq_dotAction_iff_of_mem_dominantChamber {v w : P.weylGroup} {x y : M}
    (hx : x ∈ dominantChamber P b) (hy : y ∈ dominantChamber P b) :
    dotAction P b v x = dotAction P b w y ↔ x = y ∧ v = w := by
  refine ⟨fun h ↦ ?_, fun ⟨hxy, hvw⟩ ↦ by rw [hxy, hvw]⟩
  have key : dotAction P b (w⁻¹ * v) x = y := by
    rw [dotAction_mul, h, dotAction_inv_dotAction]
  have hxy := (eq_of_dotAction_eq_of_mem_dominantChamber P b hx hy key).symm
  refine ⟨hxy, ?_⟩
  have := eq_one_of_dotAction_mem_dominantChamber P b (w⁻¹ * v) hx (key ▸ hy)
  rw [inv_mul_eq_one] at this
  exact this.symm

end Ordered

end TauCeti
