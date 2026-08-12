/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Weights.Killing
public import TauCeti.Algebra.Lie.InnerAutomorphism

public section

/-!
# The Weyl automorphism of an `sl₂` triple

Let `t : IsSl2Triple h e f` be an `sl₂` triple in a Lie algebra `L` whose raising and lowering
elements act nilpotently. Its **Weyl automorphism** is the inner automorphism

`TauCeti.weylAut he hf = exp (ad e) ∘ exp (ad (-f)) ∘ exp (ad e)`,

Chevalley's `τ` and the Lie-algebra shadow of the group element `n_α = x_α(1) x_{-α}(-1) x_α(1)`
that represents the reflection `s_α` in the Weyl group. It negates the whole triple,

`h ↦ -h`, `e ↦ -f`, `f ↦ -e`,

and fixes everything centralised by both `e` and `f`. Those two facts are the whole content: the
reflection formula `TauCeti.weylAut_apply_of_lie_eq_smul` says that an element `y` acting on `e`
and `f` by the opposite scalars `c` and `-c` is sent to `y - c • h`, which on a Cartan subalgebra
is the coreflection in `α`, and `TauCeti.lie_weylAut_apply` then transports a simultaneous
eigenvector along it: a `z` with `⁅y, z⁆ = d • z` and `⁅h, z⁆ = m • z` has

`⁅y, weylAut he hf z⁆ = (d - c * m) • weylAut he hf z`,

so `weylAut he hf z` is again an eigenvector, now for the reflected weight `β - β(h) • α`.

Everything up to that point is stated for a bare `sl₂` triple over a commutative ring, in terms of
brackets alone: no Cartan subalgebra, no weight-space decomposition and no finiteness. The final
section specialises to a Lie algebra with non-degenerate Killing form over a field of
characteristic zero, where the eigenvector hypotheses are automatic for elements of the Cartan
subalgebra and the conclusion becomes `TauCeti.weylAut_mem_rootSpace`: the Weyl automorphism of the
`sl₂` triple of a root `α` carries the root space of `β` into the root space of `β - β(α^∨) • α`.
Since a nonzero root always admits such a triple, every reflection in the Weyl group is realised by
an automorphism of `L` (`TauCeti.exists_lieEquiv_forall_mem_rootSpace`), which is Humphreys'
Proposition 14.3.

This is the step of the Chevalley basis theorem that makes the structure constants of `L` behave
under the Weyl group: `weylAut` matches a root vector of `β` with one of `s_α β`, and applied to
the triple of `α` itself it is the source of the relation `N (α, β) = -N (-α, -β)` between
structure constants (Humphreys §25.2).

## Main definitions

* `TauCeti.weylAut`: the automorphism `exp (ad e) ∘ exp (ad (-f)) ∘ exp (ad e)`.

## Main results

* `TauCeti.weylAut_apply_h`, `TauCeti.weylAut_apply_e`, `TauCeti.weylAut_apply_f`: the Weyl
  automorphism negates and swaps the triple.
* `TauCeti.weylAut_apply_of_lie_eq_zero`: it fixes the joint centraliser of `e` and `f`.
* `TauCeti.weylAut_apply_of_lie_eq_smul`: the reflection formula `y ↦ y - c • h`.
* `TauCeti.lie_weylAut_apply`: the reflected weight of the image of an eigenvector.
* `TauCeti.weylAut_mem_rootSpace` and `TauCeti.exists_lieEquiv_forall_mem_rootSpace`: in the
  Killing setting, `weylAut` carries root spaces to reflected root spaces.

## References

* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972], §§14.3
  and 25.2.
* [R. W. Carter, *Simple Groups of Lie Type*][carter1972], §4.1.
-/

namespace TauCeti

open LieAlgebra LieModule

section CommRing

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] [LieAlgebra ℚ L] {h e f : L}

omit [LieAlgebra ℚ L] in
/-- The adjoint action of `-x` is nilpotent as soon as that of `x` is. -/
lemma isNilpotent_ad_neg {x : L} (hx : IsNilpotent (ad K L x)) : IsNilpotent (ad K L (-x)) := by
  simpa using hx.neg

/-- The **Weyl automorphism** `exp (ad e) ∘ exp (ad (-f)) ∘ exp (ad e)` of a pair of
`ad`-nilpotent elements.

The name records the intended input, an `sl₂` triple `IsSl2Triple h e f`, for which this is the
automorphism realising the reflection in the root of `e`; the construction itself does not need the
triple relations, and every result below that uses them assumes them explicitly. -/
noncomputable def weylAut (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f)) :
    L ≃ₗ⁅K⁆ L :=
  (expAd e he).trans ((expAd (-f) (isNilpotent_ad_neg hf)).trans (expAd e he))

variable (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f))

/-- The Weyl automorphism as the threefold composite it is defined to be. -/
lemma weylAut_apply (y : L) :
    weylAut he hf y = expAd e he (expAd (-f) (isNilpotent_ad_neg hf) (expAd e he y)) := by
  rw [weylAut]
  rfl

/-! ### The two exponentials on the triple

The values of `exp (ad e)` and `exp (ad (-f))` on `h`, `e` and `f`. Each of these vectors is killed
by at most three brackets, so the truncations of `TauCeti/Algebra/Lie/InnerAutomorphism.lean`
apply; the two remaining values `exp (ad e) e = e` and `exp (ad (-f)) (-f) = -f` are
`TauCeti.expAd_apply_self`. -/

/-- `exp (ad e)` sends `h` to `h - 2 e`. -/
lemma expAd_e_apply_h (t : IsSl2Triple h e f) : expAd e he h = h - 2 • e := by
  have h₂ : ⁅e, h⁆ = -(2 • e) := by rw [← lie_skew e h, t.lie_h_e_nsmul]
  rw [expAd_apply_of_lie_lie_eq_zero he (by rw [h₂]; simp), h₂]
  abel

/-- `exp (ad e)` sends `f` to `f + h - e`. -/
lemma expAd_e_apply_f (t : IsSl2Triple h e f) : expAd e he f = f + h - e := by
  have h₁ : ⁅e, f⁆ = h := t.lie_e_f
  have h₂ : ⁅e, h⁆ = -(2 • e) := by rw [← lie_skew e h, t.lie_h_e_nsmul]
  rw [expAd_apply_of_lie_lie_lie_eq_zero he (by rw [h₁, h₂]; simp), h₁, h₂,
    show ((2 : ℕ) • e) = (2 : ℚ) • e by rw [← Nat.cast_smul_eq_nsmul ℚ]; norm_num,
    smul_neg, smul_smul]
  norm_num
  abel

/-- `exp (ad (-f))` sends `h` to `h - 2 f`. -/
lemma expAd_neg_f_apply_h (t : IsSl2Triple h e f) :
    expAd (-f) (isNilpotent_ad_neg hf) h = h - 2 • f := by
  have h₂ : ⁅-f, h⁆ = -(2 • f) := by rw [neg_lie, ← lie_skew f h, t.lie_h_f_nsmul]; simp
  rw [expAd_apply_of_lie_lie_eq_zero (isNilpotent_ad_neg hf) (by rw [h₂]; simp), h₂]
  abel

/-- `exp (ad (-f))` fixes `f`. -/
lemma expAd_neg_f_apply_f : expAd (-f) (isNilpotent_ad_neg hf) f = f :=
  expAd_apply_of_lie_eq_zero (isNilpotent_ad_neg hf) (by simp)

/-- `exp (ad (-f))` sends `e` to `e + h - f`. -/
lemma expAd_neg_f_apply_e (t : IsSl2Triple h e f) :
    expAd (-f) (isNilpotent_ad_neg hf) e = e + h - f := by
  have h₁ : ⁅-f, e⁆ = h := by rw [neg_lie, lie_skew, t.lie_e_f]
  have h₂ : ⁅-f, h⁆ = -(2 • f) := by rw [neg_lie, ← lie_skew f h, t.lie_h_f_nsmul]; simp
  rw [expAd_apply_of_lie_lie_lie_eq_zero (isNilpotent_ad_neg hf) (by rw [h₁, h₂]; simp), h₁, h₂,
    show ((2 : ℕ) • f) = (2 : ℚ) • f by rw [← Nat.cast_smul_eq_nsmul ℚ]; norm_num,
    smul_neg, smul_smul]
  norm_num
  abel

/-! ### The Weyl automorphism on the triple -/

/-- The Weyl automorphism negates `h`. -/
lemma weylAut_apply_h (t : IsSl2Triple h e f) : weylAut he hf h = -h := by
  have s₁ : expAd (-f) (isNilpotent_ad_neg hf) (h - 2 • e) = -h - 2 • e := by
    simp only [map_sub, map_nsmul, expAd_neg_f_apply_h hf t, expAd_neg_f_apply_e hf t]
    abel
  have s₂ : expAd e he (-h - 2 • e) = -h := by
    simp only [map_sub, map_neg, map_nsmul, expAd_e_apply_h he t, expAd_apply_self e he]
    abel
  rw [weylAut_apply he hf, expAd_e_apply_h he t, s₁, s₂]

/-- The Weyl automorphism sends the raising element to minus the lowering element. -/
lemma weylAut_apply_e (t : IsSl2Triple h e f) : weylAut he hf e = -f := by
  have s₁ : expAd e he (e + h - f) = -f := by
    simp only [map_sub, map_add, expAd_apply_self e he, expAd_e_apply_h he t,
      expAd_e_apply_f he t]
    abel
  rw [weylAut_apply he hf, expAd_apply_self e he, expAd_neg_f_apply_e hf t, s₁]

/-- The Weyl automorphism sends the lowering element to minus the raising element. -/
lemma weylAut_apply_f (t : IsSl2Triple h e f) : weylAut he hf f = -e := by
  have s₁ : expAd (-f) (isNilpotent_ad_neg hf) (f + h - e) = -e := by
    simp only [map_sub, map_add, expAd_neg_f_apply_f hf, expAd_neg_f_apply_h hf t,
      expAd_neg_f_apply_e hf t]
    abel
  rw [weylAut_apply he hf, expAd_e_apply_f he t, s₁, map_neg, expAd_apply_self e he]

/-- The Weyl automorphism fixes the joint centraliser of `e` and `f`. -/
lemma weylAut_apply_of_lie_eq_zero {y : L} (hye : ⁅y, e⁆ = 0) (hyf : ⁅y, f⁆ = 0) :
    weylAut he hf y = y := by
  have hey : ⁅e, y⁆ = 0 := by rw [← lie_skew e y, hye, neg_zero]
  rw [weylAut_apply he hf, expAd_apply_of_lie_eq_zero he hey,
    expAd_apply_of_lie_eq_zero (isNilpotent_ad_neg hf)
      (by rw [neg_lie, ← lie_skew f y, hyf]; simp),
    expAd_apply_of_lie_eq_zero he hey]

/-! ### The reflection formula -/

/-- **The reflection formula.** An element acting on `e` by a scalar `c` and on `f` by `-c` — for
an `sl₂` triple of a root `α` inside a Cartan subalgebra, an element `y` with `α y = c` — is sent
by the Weyl automorphism to `y - c • h`. This is the coreflection `y ↦ y - α y • α^∨`. -/
lemma weylAut_apply_of_lie_eq_smul (t : IsSl2Triple h e f) {y : L} {c : K}
    (hye : ⁅y, e⁆ = c • e) (hyf : ⁅y, f⁆ = -(c • f)) :
    weylAut he hf y = y - c • h := by
  have hey : ⁅e, y⁆ = -(c • e) := by rw [← lie_skew e y, hye]
  have hfy : ⁅-f, y⁆ = -(c • f) := by rw [neg_lie, ← lie_skew f y, hyf]; simp
  have h₁ : expAd e he y = y - c • e := by
    rw [expAd_apply_of_lie_lie_eq_zero he (by rw [hey]; simp), hey, sub_eq_add_neg]
  have h₂ : expAd (-f) (isNilpotent_ad_neg hf) y = y - c • f := by
    rw [expAd_apply_of_lie_lie_eq_zero (isNilpotent_ad_neg hf) (by rw [hfy]; simp), hfy,
      sub_eq_add_neg]
  have h₃ : expAd (-f) (isNilpotent_ad_neg hf) (y - c • e) = y - c • f - c • (e + h - f) := by
    rw [map_sub, map_smul, h₂, expAd_neg_f_apply_e hf t]
  have h₄ : expAd e he (y - c • f - c • (e + h - f)) = y - c • h := by
    simp only [map_sub, map_add, map_smul, h₁, expAd_apply_self e he, expAd_e_apply_h he t,
      expAd_e_apply_f he t]
    module
  rw [weylAut_apply he hf, h₁, h₃, h₄]

/-- The Weyl automorphism is an involution on the elements the reflection formula applies to. -/
lemma weylAut_apply_sub_smul (t : IsSl2Triple h e f) {y : L} {c : K}
    (hye : ⁅y, e⁆ = c • e) (hyf : ⁅y, f⁆ = -(c • f)) :
    weylAut he hf (y - c • h) = y := by
  have h₁ : ⁅y - c • h, e⁆ = (-c) • e := by
    rw [sub_lie, hye, smul_lie, t.lie_h_e_smul K, smul_smul, neg_smul]
    module
  have h₂ : ⁅y - c • h, f⁆ = -((-c) • f) := by
    rw [sub_lie, hyf, smul_lie, t.lie_lie_smul_f K, smul_neg, smul_smul, neg_smul]
    module
  rw [weylAut_apply_of_lie_eq_smul he hf t h₁ h₂, neg_smul]
  abel

/-- **The reflected weight.** If `y` acts on `e` and `f` by `c` and `-c`, and `z` is a simultaneous
eigenvector of `y` and `h` with eigenvalues `d` and `m`, then the image of `z` under the Weyl
automorphism is again an eigenvector of `y`, with the reflected eigenvalue `d - c * m`. -/
lemma lie_weylAut_apply (t : IsSl2Triple h e f) {y z : L} {c d m : K}
    (hye : ⁅y, e⁆ = c • e) (hyf : ⁅y, f⁆ = -(c • f)) (hyz : ⁅y, z⁆ = d • z)
    (hhz : ⁅h, z⁆ = m • z) :
    ⁅y, weylAut he hf z⁆ = (d - c * m) • weylAut he hf z := by
  have key : ⁅y - c • h, z⁆ = (d - c * m) • z := by
    rw [sub_lie, hyz, smul_lie, hhz, smul_smul, sub_smul]
  calc ⁅y, weylAut he hf z⁆
      = ⁅weylAut he hf (y - c • h), weylAut he hf z⁆ := by
        rw [weylAut_apply_sub_smul he hf t hye hyf]
    _ = weylAut he hf ⁅y - c • h, z⁆ := (LieEquiv.map_lie _ _ _).symm
    _ = (d - c * m) • weylAut he hf z := by rw [key, map_smul]

end CommRing

section Killing

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L] {h e f : L}

open IsKilling in
/-- **The Weyl automorphism reflects root spaces.** For the `sl₂` triple of a nonzero root `α`, the
Weyl automorphism carries the root space of a weight `β` into the root space of the reflection
`β - β(α^∨) • α`. -/
theorem weylAut_mem_rootSpace [LieAlgebra ℚ L] {α : Weight K H L} (t : IsSl2Triple h e f)
    (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α)) (hα : α.IsNonZero)
    (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f))
    {β : H → K} {z : L} (hz : z ∈ rootSpace H β) :
    weylAut he hf z ∈ rootSpace H (β - β (coroot α) • ⇑α) := by
  have hh : h = (coroot α : L) := t.h_eq_coroot hα heα hfα
  have hhz : ⁅h, z⁆ = β (coroot α) • z := by
    rw [hh]; exact lie_eq_smul_of_mem_rootSpace hz (coroot α)
  refine weightSpace_le_genWeightSpace (M := L) _ ((mem_weightSpace _ _).mpr fun y ↦ ?_)
  have hye : ⁅(y : L), e⁆ = α y • e := lie_eq_smul_of_mem_rootSpace heα y
  have hyf : ⁅(y : L), f⁆ = -(α y • f) := by
    have := lie_eq_smul_of_mem_rootSpace hfα y
    simpa using this
  have hyz : ⁅(y : L), z⁆ = β y • z := lie_eq_smul_of_mem_rootSpace hz y
  have key := lie_weylAut_apply he hf t hye hyf hyz hhz
  rw [H.coe_bracket_of_module, key]
  simp [mul_comm]

open IsKilling in
/-- Every reflection of the root system of `(L, H)` is realised by an automorphism of `L`: for a
nonzero root `α` there is an automorphism carrying the root space of every weight `β` into the root
space of `β - β(α^∨) • α`. This is the `sl₂` triple of `α` fed to `TauCeti.weylAut`, and it needs
no `ℚ`-structure hypothesis, `TauCeti.ratLieAlgebra` supplying one. -/
theorem exists_lieEquiv_forall_mem_rootSpace {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ τ : L ≃ₗ⁅K⁆ L, ∀ (β : H → K) (z : L), z ∈ rootSpace H β →
      τ z ∈ rootSpace H (β - β (coroot α) • ⇑α) := by
  let _ : LieAlgebra ℚ L := ratLieAlgebra K L
  obtain ⟨h, e, f, t, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have he : IsNilpotent (ad K L e) :=
    isNilpotent_ad_of_mem_rootSpace H (χ := ⇑α) hα heα
  have hf : IsNilpotent (ad K L f) :=
    isNilpotent_ad_of_mem_rootSpace H (χ := ⇑(-α)) hα.neg hfα
  exact ⟨weylAut he hf, fun β z hz ↦ weylAut_mem_rootSpace t heα hfα hα he hf hz⟩

end Killing

end TauCeti
