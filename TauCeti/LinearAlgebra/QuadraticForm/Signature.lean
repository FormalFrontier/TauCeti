/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Definiteness and the signature of a quadratic form

This file characterizes positive and negative semidefiniteness by the vanishing of the
opposite index of inertia. It also characterizes positive-definiteness by the negative
index and the radical. These are convenient consequences of Sylvester's law of inertia which
complement Mathlib's definitions of `QuadraticMap.PosDef`, `sigPos`, and `sigNeg`.

It also proves that restriction to a subspace cannot increase either index of inertia, that
quotienting a quadratic form by its radical preserves both indices, and that multiplication by a
positive scalar preserves both indices while multiplication by a negative scalar exchanges them.
Finally, both indices are additive under orthogonal products.

## Main results

* `TauCeti.QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero`: nonnegativity is characterized by
  vanishing negative index of inertia.
* `TauCeti.QuadraticForm.forall_nonpos_iff_sigPos_eq_zero`: nonpositivity is characterized by
  vanishing positive index of inertia.
* `TauCeti.QuadraticForm.sigPos_restrict_le`: restriction to a subspace cannot increase the
  positive index of inertia.
* `TauCeti.QuadraticForm.sigNeg_restrict_le`: restriction to a subspace cannot increase the
  negative index of inertia.
* `TauCeti.QuadraticForm.sigPos_smul_of_pos` and
  `TauCeti.QuadraticForm.sigNeg_smul_of_pos`: positive scaling preserves both indices.
* `TauCeti.QuadraticForm.sigPos_smul_of_neg` and
  `TauCeti.QuadraticForm.sigNeg_smul_of_neg`: negative scaling exchanges the two indices.
* `TauCeti.QuadraticForm.sigPos_lift_radical`: quotienting by the radical preserves the positive
  index of inertia.
* `TauCeti.QuadraticForm.sigNeg_lift_radical`: quotienting by the radical preserves the negative
  index of inertia.
* `TauCeti.QuadraticForm.sigPos_prod` and `TauCeti.QuadraticForm.sigNeg_prod`: the indices of
  inertia are additive under orthogonal products.
* `TauCeti.QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot`: positive-definiteness
  is characterized by vanishing negative index and trivial radical.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Finset QuadraticMap

namespace TauCeti

namespace QuadraticForm

open _root_.QuadraticForm

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

omit [FiniteDimensional K M] in
/-- Multiplication by a positive scalar preserves positive-definiteness. Thus a quadratic form is
positive-definite if and only if its positive scalar multiple is. -/
@[simp]
theorem posDef_smul_iff_of_pos (Q : _root_.QuadraticForm K M) {a : K} (ha : 0 < a) :
    (a • Q).PosDef ↔ Q.PosDef := by
  constructor
  · intro hQ x hx
    have h := hQ x hx
    simp only [smul_apply, smul_eq_mul] at h
    exact pos_of_mul_pos_right h ha.le
  · exact fun hQ ↦ hQ.smul ha

/-- Multiplication by a positive scalar preserves the positive index of inertia. -/
@[simp]
theorem sigPos_smul_of_pos (Q : _root_.QuadraticForm K M) {a : K} (ha : 0 < a) :
    sigPos (a • Q) = sigPos Q := by
  apply le_antisymm
  · obtain ⟨U, hUrank, hU⟩ := exists_finrank_eq_sigPos_and_posDef (a • Q)
    rw [← hUrank]
    apply le_sigPos_of_posDef
    exact (posDef_smul_iff_of_pos (Q.restrict U) ha).mp hU
  · obtain ⟨U, hUrank, hU⟩ := exists_finrank_eq_sigPos_and_posDef Q
    rw [← hUrank]
    apply le_sigPos_of_posDef
    exact (posDef_smul_iff_of_pos (Q.restrict U) ha).mpr hU

/-- Multiplication by a positive scalar preserves the negative index of inertia. -/
@[simp]
theorem sigNeg_smul_of_pos (Q : _root_.QuadraticForm K M) {a : K} (ha : 0 < a) :
    sigNeg (a • Q) = sigNeg Q := by
  calc
    sigNeg (a • Q) = sigPos (-(a • Q)) := (sigPos_neg (Q := a • Q)).symm
    _ = sigPos (a • (-Q)) := by rw [smul_neg]
    _ = sigPos (-Q) := sigPos_smul_of_pos (-Q) ha
    _ = sigNeg Q := sigPos_neg

/-- Multiplication by a negative scalar exchanges the positive and negative indices of inertia. -/
@[simp]
theorem sigPos_smul_of_neg (Q : _root_.QuadraticForm K M) {a : K} (ha : a < 0) :
    sigPos (a • Q) = sigNeg Q := by
  have hpos : 0 < -a := neg_pos.mpr ha
  have hform : a • Q = (-a) • (-Q) := by simp
  rw [hform, sigPos_smul_of_pos (-Q) hpos, sigPos_neg]

/-- Multiplication by a negative scalar exchanges the negative and positive indices of inertia. -/
@[simp]
theorem sigNeg_smul_of_neg (Q : _root_.QuadraticForm K M) {a : K} (ha : a < 0) :
    sigNeg (a • Q) = sigPos Q := by
  have hpos : 0 < -a := neg_pos.mpr ha
  calc
    sigNeg (a • Q) = sigPos (-(a • Q)) := (sigPos_neg (Q := a • Q)).symm
    _ = sigPos ((-a) • Q) := congrArg sigPos (neg_smul a Q).symm
    _ = sigPos Q := sigPos_smul_of_pos Q hpos

/-- A quadratic form is nonnegative exactly when its negative index of inertia vanishes. -/
theorem forall_nonneg_iff_sigNeg_eq_zero (Q : _root_.QuadraticForm K M) :
    (∀ x, 0 ≤ Q x) ↔ sigNeg Q = 0 := by
  constructor
  · intro hQ
    have h := sigPos_add_finrank_le_of_nonpos (Q := -Q) (V := ⊤) (fun x _ ↦ by
      simp only [neg_apply]
      exact neg_nonpos.mpr (hQ x))
    rw [sigPos_neg, finrank_top] at h
    omega
  · intro hsig x
    by_contra hlt
    have hQx : 0 < -Q x := neg_pos.mpr (not_le.mp hlt)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, neg_zero] at hQx
      exact lt_irrefl 0 hQx
    have hpos : ((-Q).restrict (Submodule.span K {x})).PosDef := by
      rintro ⟨v, hv⟩ hv0
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hv0 (by simp)
      rw [restrict_apply, neg_apply, Q.map_smul, smul_eq_mul]
      have : -(c * c * Q x) = (c * c) * -Q x := by ring
      rw [this]
      exact mul_pos (mul_self_pos.mpr hc0) hQx
    have hrank : Module.finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx0
    have hle := le_sigNeg_of_negDef (Q := Q) hpos
    rw [hrank, hsig] at hle
    omega

/-- A quadratic form is nonpositive exactly when its positive index of inertia vanishes. -/
theorem forall_nonpos_iff_sigPos_eq_zero (Q : _root_.QuadraticForm K M) :
    (∀ x, Q x ≤ 0) ↔ sigPos Q = 0 := by
  simpa only [neg_apply, neg_nonneg, sigNeg_neg] using forall_nonneg_iff_sigNeg_eq_zero (-Q)

omit [IsStrictOrderedRing K] in
/-- Restricting a quadratic form to a subspace cannot increase its positive index. -/
theorem sigPos_restrict_le (Q : _root_.QuadraticForm K M) (W : Subspace K M) :
    sigPos (Q.restrict W) ≤ sigPos Q := by
  obtain ⟨U, hUrank, hUpos⟩ := exists_finrank_eq_sigPos_and_posDef (Q.restrict W)
  rw [← hUrank, ← Submodule.finrank_map_subtype_eq W U]
  apply le_sigPos_of_posDef (V := U.map W.subtype)
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ hx0
  rw [restrict_apply]
  exact hUpos ⟨x, hx⟩ (by simpa using hx0)

omit [IsStrictOrderedRing K] in
/-- Restricting a quadratic form to a subspace cannot increase its negative index. -/
theorem sigNeg_restrict_le (Q : _root_.QuadraticForm K M) (W : Subspace K M) :
    sigNeg (Q.restrict W) ≤ sigNeg Q := by
  have hneg : (-Q).restrict W = -(Q.restrict W) := by
    ext x
    simp only [QuadraticMap.restrict_apply, neg_apply]
  simpa only [hneg, sigPos_neg] using sigPos_restrict_le (-Q) W

section Prod

variable {M' : Type*} [AddCommGroup M'] [Module K M'] [FiniteDimensional K M']

/-- The product of two subspaces, as a subspace of the product ambient space, is linearly
equivalent to the product of their underlying types. -/
private def subspaceProdEquiv (U : Subspace K M) (W : Subspace K M') :
    (U × W) ≃ₗ[K] U.prod W where
  toFun p := ⟨(p.1, p.2), p.1.2, p.2.2⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sum of the positive indices of two quadratic forms is a lower bound for the positive
index of their orthogonal product. -/
private theorem add_sigPos_le_sigPos_prod (Q : _root_.QuadraticForm K M)
    (Q' : _root_.QuadraticForm K M') :
    sigPos Q + sigPos Q' ≤ sigPos (Q.prod Q') := by
  obtain ⟨U, hUrank, hUpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
  obtain ⟨W, hWrank, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q'
  have hprod : ((Q.prod Q').restrict (U.prod W)).PosDef := by
    intro p hp
    let u : U := ⟨p.1.1, p.2.1⟩
    let w : W := ⟨p.1.2, p.2.2⟩
    have hp' : u ≠ 0 ∨ w ≠ 0 := by
      contrapose! hp
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val hp.1) (congrArg Subtype.val hp.2)
    rcases hp' with hp' | hp'
    · have hpos := hUpos u hp'
      have hnonneg := hWpos.nonneg w
      simpa only [QuadraticMap.restrict_apply, QuadraticMap.prod_apply] using
        add_pos_of_pos_of_nonneg hpos hnonneg
    · have hnonneg := hUpos.nonneg u
      have hpos := hWpos w hp'
      simpa only [QuadraticMap.restrict_apply, QuadraticMap.prod_apply] using
        add_pos_of_nonneg_of_pos hnonneg hpos
  calc
    sigPos Q + sigPos Q' = Module.finrank K U + Module.finrank K W := by
      rw [hUrank, hWrank]
    _ = Module.finrank K (U × W) := Module.finrank_prod.symm
    _ = Module.finrank K (U.prod W) := LinearEquiv.finrank_eq (subspaceProdEquiv U W)
    _ ≤ sigPos (Q.prod Q') := le_sigPos_of_posDef (Q := Q.prod Q') hprod

/-- The sum of the negative indices of two quadratic forms is a lower bound for the negative
index of their orthogonal product. -/
private theorem add_sigNeg_le_sigNeg_prod (Q : _root_.QuadraticForm K M)
    (Q' : _root_.QuadraticForm K M') :
    sigNeg Q + sigNeg Q' ≤ sigNeg (Q.prod Q') := by
  have hneg : (-Q).prod (-Q') = -(Q.prod Q') := by
    ext p
    simp only [QuadraticMap.prod_apply, neg_apply, neg_add]
  simpa only [← sigPos_neg, hneg] using add_sigPos_le_sigPos_prod (-Q) (-Q')

/-- The positive index of inertia is additive under orthogonal products. -/
@[simp]
theorem sigPos_prod (Q : _root_.QuadraticForm K M) (Q' : _root_.QuadraticForm K M') :
    sigPos (Q.prod Q') = sigPos Q + sigPos Q' := by
  have hpos := add_sigPos_le_sigPos_prod Q Q'
  have hneg := add_sigNeg_le_sigNeg_prod Q Q'
  have hsum := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q.prod Q')
  have hsumQ := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have hsumQ' := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q')
  have hrad : Module.finrank K (Q.prod Q').radical =
      Module.finrank K Q.radical + Module.finrank K Q'.radical := by
    let _ : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
    rw [QuadraticMap.radical_prod, ← LinearEquiv.finrank_eq
      (subspaceProdEquiv Q.radical Q'.radical),
      Module.finrank_prod]
  rw [hrad, Module.finrank_prod] at hsum
  omega

/-- The negative index of inertia is additive under orthogonal products. -/
@[simp]
theorem sigNeg_prod (Q : _root_.QuadraticForm K M) (Q' : _root_.QuadraticForm K M') :
    sigNeg (Q.prod Q') = sigNeg Q + sigNeg Q' := by
  have hneg : (-Q).prod (-Q') = -(Q.prod Q') := by
    ext p
    simp only [QuadraticMap.prod_apply, neg_apply, neg_add]
  rw [← sigPos_neg, ← hneg, sigPos_prod, sigPos_neg, sigPos_neg]

end Prod

end QuadraticForm

namespace QuadraticForm

open _root_.QuadraticForm

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- An arbitrarily chosen complement to the radical, used only to compare inertia indices. -/
private noncomputable def radicalComplement (Q : _root_.QuadraticForm K M) : Subspace K M :=
  (Submodule.exists_isCompl Q.radical).choose

/-- The chosen radical complement is complementary to the radical. -/
private theorem isCompl_radical_radicalComplement (Q : _root_.QuadraticForm K M) :
    IsCompl Q.radical (radicalComplement Q) :=
  (Submodule.exists_isCompl Q.radical).choose_spec

/-- The quotient by the radical is isometric to the restriction to the chosen complement. -/
private noncomputable def liftRadicalIsometryEquiv (Q : _root_.QuadraticForm K M) :
    (Q.restrict (radicalComplement Q)).IsometryEquiv (Q.lift Q.radical le_rfl) where
  toLinearEquiv :=
    (Q.radical.quotientEquivOfIsCompl (radicalComplement Q)
      (isCompl_radical_radicalComplement Q)).symm
  map_app' x := by
    have he :
        (Q.radical.quotientEquivOfIsCompl (radicalComplement Q)
          (isCompl_radical_radicalComplement Q)).symm x =
          Submodule.Quotient.mk (x : M) :=
      LinearMap.congr_fun (Submodule.toLinearMap_symm_quotientEquivOfIsCompl
        (isCompl_radical_radicalComplement Q)) x
    -- Expose the linear-equivalence application hidden by the isometry-equivalence coercion.
    change Q.lift Q.radical le_rfl
      ((Q.radical.quotientEquivOfIsCompl (radicalComplement Q)
        (isCompl_radical_radicalComplement Q)).symm x) = _
    rw [he]
    simp only [QuadraticMap.lift_mk, QuadraticMap.restrict_apply]

/-- The restriction to the chosen complement of the radical has trivial radical. -/
private theorem radical_restrict_radicalComplement_eq_bot (Q : _root_.QuadraticForm K M)
    (h2 : Invertible (2 : K)) :
    (Q.restrict (radicalComplement Q)).radical = ⊥ := by
  let _ := h2
  let B : LinearMap.BilinForm K M := QuadraticMap.associated Q
  have hsymm : B.IsSymm := ⟨fun x y ↦ QuadraticMap.associated_isSymm K Q x y⟩
  have hrad : (Q.restrict (radicalComplement Q)).radical =
      (B.restrict (radicalComplement Q)).ker := by
    rw [QuadraticMap.radical_eq_ker_associated]
    congr 1
  rw [hrad, Submodule.eq_bot_iff]
  intro x hx
  have hxrad : (x : M) ∈ Q.radical := by
    rw [QuadraticMap.radical_eq_ker_associated, LinearMap.mem_ker, LinearMap.ext_iff]
    intro y
    obtain ⟨r, w, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl
      (isCompl_radical_radicalComplement Q) y
    have hr : (r : M) ∈ B.ker := by
      rw [← QuadraticMap.radical_eq_ker_associated]
      exact r.2
    have hrx : B r x = 0 := DFunLike.congr_fun (LinearMap.mem_ker.mp hr) (x : M)
    have hxzero : (B.restrict (radicalComplement Q)) x = 0 := LinearMap.mem_ker.mp hx
    have hxw : B x w = 0 := DFunLike.congr_fun hxzero w
    rw [map_add, hsymm.eq x r, hrx, zero_add, hxw, LinearMap.zero_apply]
  have hxbot : (x : M) ∈ Q.radical ⊓ radicalComplement Q := ⟨hxrad, x.2⟩
  rw [(isCompl_radical_radicalComplement Q).disjoint.eq_bot, Submodule.mem_bot] at hxbot
  exact Subtype.ext hxbot

variable [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K M]

/-- Quotienting a quadratic form by its radical preserves its positive index of inertia. -/
theorem sigPos_lift_radical (Q : _root_.QuadraticForm K M) :
    sigPos (Q.lift Q.radical le_rfl) = sigPos Q := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  have hquot : sigPos (Q.lift Q.radical le_rfl) =
      sigPos (Q.restrict (radicalComplement Q)) :=
    (QuadraticMap.Equivalent.sigPos_eq (⟨liftRadicalIsometryEquiv Q⟩ :
      (Q.restrict (radicalComplement Q)).Equivalent (Q.lift Q.radical le_rfl))).symm
  have hpos := sigPos_restrict_le Q (radicalComplement Q)
  have hneg := sigNeg_restrict_le Q (radicalComplement Q)
  have hsum := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have hsumW := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := Q.restrict (radicalComplement Q))
  rw [radical_restrict_radicalComplement_eq_bot Q inferInstance, finrank_bot, add_zero] at hsumW
  have hdim := Submodule.finrank_add_eq_of_isCompl (isCompl_radical_radicalComplement Q)
  omega

/-- Lifting by a subspace known to be the radical preserves the positive index of inertia. -/
theorem sigPos_lift_of_eq_radical (Q : _root_.QuadraticForm K M) (N : Subspace K M)
    (hN : N = Q.radical) : sigPos (Q.lift N hN.le) = sigPos Q := by
  subst N
  simpa using sigPos_lift_radical Q

/-- Quotienting a quadratic form by its radical preserves its negative index of inertia. -/
theorem sigNeg_lift_radical (Q : _root_.QuadraticForm K M) :
    sigNeg (Q.lift Q.radical le_rfl) = sigNeg Q := by
  have hlift : (-Q).lift Q.radical (radical_neg Q).symm.le =
      -(Q.lift Q.radical le_rfl) := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      simp only [QuadraticMap.lift_mk, neg_apply]
  rw [← sigPos_neg, ← hlift,
    sigPos_lift_of_eq_radical (-Q) Q.radical (radical_neg Q).symm,
    sigPos_neg]

/-- Lifting by a subspace known to be the radical preserves the negative index of inertia. -/
theorem sigNeg_lift_of_eq_radical (Q : _root_.QuadraticForm K M) (N : Subspace K M)
    (hN : N = Q.radical) : sigNeg (Q.lift N hN.le) = sigNeg Q := by
  subst N
  simpa using sigNeg_lift_radical Q

/-- A quadratic form is positive-definite exactly when its negative index vanishes and its
radical is trivial. -/
@[grind =]
theorem posDef_iff_sigNeg_eq_zero_and_radical_eq_bot (Q : _root_.QuadraticForm K M) :
    Q.PosDef ↔ sigNeg Q = 0 ∧ Q.radical = ⊥ := by
  constructor
  · intro hQ
    refine ⟨(forall_nonneg_iff_sigNeg_eq_zero Q).mp hQ.nonneg, ?_⟩
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hQ.anisotropic x (QuadraticMap.mem_radical_iff'.mp hx).1
  · rintro ⟨hneg, hrad⟩
    obtain ⟨W, hWrank, hWpos⟩ := exists_finrank_eq_sigPos_and_posDef Q
    have hsig := sigPos_add_sigNeg_add_radical (Q := Q)
    rw [hneg, hrad] at hsig
    have hsig' : sigPos Q = Module.finrank K M := by
      simpa only [add_zero, finrank_bot] using hsig
    have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (hWrank.trans hsig')
    intro x hx
    have hxW : x ∈ W := hWtop.symm ▸ Submodule.mem_top
    exact hWpos ⟨x, hxW⟩ (by simpa only [ne_eq, Submodule.mk_eq_zero])

end QuadraticForm

namespace LinearMap.BilinForm

open _root_.QuadraticForm

section Semiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [LE R]

/-- A symmetric bilinear form is positive-semidefinite if and only if its values on all vectors
are nonnegative. -/
@[grind =]
theorem isPosSemidef_iff_forall_nonneg (B : LinearMap.BilinForm R M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ ∀ x, 0 ≤ B x x := by
  rw [LinearMap.BilinForm.isPosSemidef_def, LinearMap.BilinForm.isNonneg_def]
  simp only [hB, true_and]

end Semiring

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- A symmetric bilinear form is positive-semidefinite if and only if the negative index of its
associated quadratic form vanishes. -/
@[grind =]
theorem isPosSemidef_iff_sigNeg_eq_zero (B : LinearMap.BilinForm K M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ _root_.sigNeg B.toQuadraticMap = 0 := by
  rw [isPosSemidef_iff_forall_nonneg B hB]
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using
    QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero B.toQuadraticMap

/-- The quadratic form of a symmetric bilinear form is positive-definite if and only if the
bilinear form is positive-semidefinite and nondegenerate. -/
@[grind =]
theorem posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate (B : LinearMap.BilinForm K M)
    (hB : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ B.IsPosSemidef ∧ B.Nondegenerate := by
  have _ : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  rw [isPosSemidef_iff_sigNeg_eq_zero B hB,
    QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    _root_.LinearMap.BilinForm.radical_toQuadraticMap B hB]

/-- The quadratic form of a symmetric bilinear form is positive-definite if and only if the
kernel of the bilinear form and the negative index of the quadratic form both vanish. -/
@[grind =]
theorem posDef_toQuadraticMap_iff_finrank_ker_eq_zero_and_sigNeg_eq_zero
    (B : LinearMap.BilinForm K M) (hB : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ Module.finrank K B.ker = 0 ∧ _root_.sigNeg B.toQuadraticMap = 0 := by
  rw [posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate B hB,
    isPosSemidef_iff_sigNeg_eq_zero B hB,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    Submodule.finrank_eq_zero, and_comm]

end LinearMap.BilinForm

end TauCeti
