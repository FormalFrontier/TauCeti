/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Group
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.GroupTheory.Perm.Subgroup

/-!
# The standard parametrisation of `Aut(𝔻)` is a bijection

`Conformal/UnitDisc/Automorphism/Group.lean` identifies the automorphism group of the open unit
disc with the standard family: `TauCeti.coe_unitDiscAut` exhibits `Aut(𝔻)` as the *range* of

`(u, a) ↦ (z ↦ u * (z - a) / (1 - conj a * z))`,

a map `Circle × 𝔻 → Equiv.Perm 𝔻`.  This file shows that map is *injective*, so that the
description `Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}` is a genuine parametrisation: the rotation `u` and the
centre `a` are uniquely determined by the automorphism, not merely available for it.

## Why uniqueness is a separate matter

Surjectivity onto `Aut(𝔻)` is the Schwarz-lemma classification and is already merged.  Injectivity
is elementary, but it is not formal: the family is indexed by two parameters and *a priori* nothing
prevents different pairs from naming the same map — a family of Möbius maps of `ℂ` written in
homogeneous coordinates is a genuine example of a parametrisation that is not injective.  What
makes this one injective is that the two parameters can be read off geometrically: the centre is
`a = e⁻¹ 0`, and once the centre is known the rotation is recovered by the circle acting freely on
the nonzero points of the disc.  The second half is exactly the faithfulness of the `Circle` action
on `Complex.UnitDisc`, which is recorded here as an instance and which Mathlib does not have.

## Main results

* `TauCeti.instFaithfulSMulCircleUnitDisc` — the circle acts faithfully on the disc (with
  `TauCeti.circle_smul_left_injective` the pointwise form: a rotation is determined by its value at
  any one nonzero point), together with the `Nontrivial` instance the disc was missing.
* `TauCeti.unitDiscStandardAutomorphismEquiv_eq_iff` and
  `TauCeti.unitDiscStandardAutomorphismEquiv_injective` — the parameters of a standard automorphism
  are unique, and `TauCeti.existsUnique_eq_unitDiscStandardAutomorphismEquiv` records the
  classification and this uniqueness together as an `∃!`.
* `TauCeti.unitDiscAutEquivProd` — the resulting bijection `Aut(𝔻) ≃ Circle × 𝔻`, with
  `TauCeti.unitDiscAutEquivProd_apply_snd` naming the centre coordinate as `e⁻¹ 0`.
* `TauCeti.circleMulEquivUnitDiscRotation` — the group-level half: the rotation subgroup of
  `Aut(𝔻)` *is* the circle group, an isomorphism rather than just a surjection.
* `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt` — a holomorphic automorphism of the disc with
  two distinct fixed points is the identity.  This is the rigidity statement uniqueness is usually
  wanted for: it is what forces a normalisation at two points to determine a conformal map, and it
  is proved here by moving one fixed point to the origin and applying faithfulness at the other.

## Generality

The `Nontrivial` and `FaithfulSMul` instances are about Mathlib's `Complex.UnitDisc` and its
`Circle` action, so they are stated at that generality; everything else concerns `Aut(𝔻)` and is
`ℂ`-scalar, as the conformal-mapping roadmap's generality bar fixes for layers L0--L6.

This completes the conformal-mapping roadmap's L2 description of the disc automorphism group
`Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}` (see `ConformalMapping/README.md`), whose existence half is
`TauCeti.mem_unitDiscAut_iff`.  As with the rest of the L0--L3 conformal-mapping material it is
coordinated with the upstream Mathlib Riemann-mapping effort
leanprover-community/mathlib4#33505, whose preceding human-curated work is
`Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`; neither contains
a disc automorphism group, and should one land upstream these declarations are a temporary shim to
be deleted and their consumers refactored onto it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §2.
-/

public section

namespace TauCeti

/-! ### The circle acts faithfully on the disc -/

/-- The open unit disc has more than one point: `0` and `1 / 2` are both in it. -/
instance instNontrivialUnitDisc : Nontrivial Complex.UnitDisc := by
  have h : ‖(2⁻¹ : ℂ)‖ < 1 := by
    rw [norm_inv, Complex.norm_ofNat]
    norm_num
  exact ⟨⟨Complex.UnitDisc.mk (2⁻¹ : ℂ) h, 0, by simp⟩⟩

/-- **A rotation is determined by its value at a single nonzero point of the disc.** Multiplication
by a nonzero complex number is injective, and the disc inherits that from `ℂ`. -/
theorem circle_smul_left_injective {z : Complex.UnitDisc} (hz : z ≠ 0) :
    Function.Injective fun u : Circle => u • z := by
  intro u v h
  have hz' : (z : ℂ) ≠ 0 := fun hc => hz (Complex.UnitDisc.coe_eq_zero.1 hc)
  have h' : (u : ℂ) * (z : ℂ) = (v : ℂ) * (z : ℂ) := by
    simpa only [Complex.UnitDisc.coe_circle_smul] using
      congrArg (fun w : Complex.UnitDisc => (w : ℂ)) h
  exact Circle.ext (mul_right_cancel₀ hz' h')

/-- Two rotations agreeing at one nonzero point of the disc are equal. -/
theorem circle_smul_left_inj {u v : Circle} {z : Complex.UnitDisc} (hz : z ≠ 0) :
    u • z = v • z ↔ u = v :=
  ⟨fun h => circle_smul_left_injective hz h, fun h => by rw [h]⟩

/-- **The circle acts faithfully on the unit disc.** Only the trivial rotation fixes the whole
disc, because the disc contains a nonzero point. -/
instance instFaithfulSMulCircleUnitDisc : FaithfulSMul Circle Complex.UnitDisc where
  eq_of_smul_eq_smul h := by
    obtain ⟨z, hz⟩ := exists_ne (0 : Complex.UnitDisc)
    exact circle_smul_left_injective hz (h z)

/-! ### Uniqueness of the parameters -/

variable {u v : Circle} {a b : Complex.UnitDisc}

/-- **The centre of a standard automorphism is the preimage of the origin.** This is the geometric
description of the parameter `a`; it is the half of the uniqueness that needs no computation. -/
theorem unitDiscStandardAutomorphismEquiv_symm_apply_zero (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismEquiv u a).symm 0 = a :=
  (Equiv.symm_apply_eq _).2 (unitDiscStandardAutomorphismEquiv_self u a).symm

/-- **The parameters of a standard disc automorphism are unique.** Two standard automorphisms
coincide exactly when their rotations and their centres do.

The centres agree because each is the preimage of the origin; the rotations then agree because
they act identically on the nonzero point `M_a⁻¹ w`, and the circle acts freely there. -/
theorem unitDiscStandardAutomorphismEquiv_eq_iff :
    unitDiscStandardAutomorphismEquiv u a = unitDiscStandardAutomorphismEquiv v b ↔
      u = v ∧ a = b := by
  refine ⟨fun h => ?_, fun ⟨hu, ha⟩ => by rw [hu, ha]⟩
  have hab : a = b := by
    have h0 := congrArg (fun e : Complex.UnitDisc ≃ Complex.UnitDisc => e.symm 0) h
    simpa only [unitDiscStandardAutomorphismEquiv_symm_apply_zero] using h0
  subst hab
  obtain ⟨w, hw⟩ := exists_ne (0 : Complex.UnitDisc)
  have hmoe : unitDiscMoebius a ((unitDiscMoebiusEquiv a).symm w) = w := by
    rw [← unitDiscMoebiusEquiv_apply, Equiv.apply_symm_apply]
  have hval := congrArg
    (fun e : Complex.UnitDisc ≃ Complex.UnitDisc => e ((unitDiscMoebiusEquiv a).symm w)) h
  simp only [unitDiscStandardAutomorphismEquiv_apply, hmoe] at hval
  exact ⟨circle_smul_left_injective hw hval, rfl⟩

/-- **The standard parametrisation of `Aut(𝔻)` is injective**: distinct pairs `(u, a)` name
distinct automorphisms.  With `TauCeti.coe_unitDiscAut`, which says the parametrisation has
`Aut(𝔻)` as its range, this is the statement that `Circle × 𝔻` parametrises the group. -/
theorem unitDiscStandardAutomorphismEquiv_injective :
    Function.Injective fun p : Circle × Complex.UnitDisc =>
      unitDiscStandardAutomorphismEquiv p.1 p.2 := by
  rintro ⟨u, a⟩ ⟨v, b⟩ h
  obtain ⟨rfl, rfl⟩ := unitDiscStandardAutomorphismEquiv_eq_iff.1 h
  rfl

/-- The standard automorphism with trivial rotation and centre at the origin is the identity.

This is deliberately not a `simp` lemma: `TauCeti.unitDiscStandardAutomorphismEquiv_zero` already
rewrites its left-hand side to `MulAction.toPerm 1`. -/
theorem unitDiscStandardAutomorphismEquiv_one_zero :
    unitDiscStandardAutomorphismEquiv (1 : Circle) (0 : Complex.UnitDisc) = 1 := by
  ext z
  simp

/-- A standard automorphism is the identity exactly at the trivial parameters. -/
theorem unitDiscStandardAutomorphismEquiv_eq_one_iff :
    unitDiscStandardAutomorphismEquiv u a = 1 ↔ u = 1 ∧ a = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← unitDiscStandardAutomorphismEquiv_one_zero] at h
    exact unitDiscStandardAutomorphismEquiv_eq_iff.1 h
  · rintro ⟨rfl, rfl⟩
    exact unitDiscStandardAutomorphismEquiv_one_zero

/-- **The classification of disc automorphisms, with uniqueness.** A holomorphic automorphism of
the disc is a standard automorphism for exactly one rotation and one centre. -/
theorem existsUnique_eq_unitDiscStandardAutomorphismEquiv {e : Equiv.Perm Complex.UnitDisc}
    (he : e ∈ unitDiscAut) :
    ∃! p : Circle × Complex.UnitDisc, e = unitDiscStandardAutomorphismEquiv p.1 p.2 := by
  obtain ⟨u, a, rfl⟩ := mem_unitDiscAut_iff.1 he
  refine ⟨(u, a), rfl, fun q hq => ?_⟩
  exact (unitDiscStandardAutomorphismEquiv_injective hq).symm

/-! ### The bijection `Aut(𝔻) ≃ Circle × 𝔻` -/

/-- **`Aut(𝔻) ≃ Circle × 𝔻`.** The automorphism group of the unit disc is parametrised by a
rotation and a centre, bijectively: the inverse map is `(u, a) ↦ (z ↦ u * (z - a) /
(1 - conj a * z))`.

This is only a bijection of types, not a group isomorphism: the composition law on `Aut(𝔻)` does
not become the product law on `Circle × 𝔻`, since already
`TauCeti.unitDiscStandardAutomorphismEquiv_symm_eq` shows that inversion mixes the two
coordinates. -/
@[expose] noncomputable def unitDiscAutEquivProd : unitDiscAut ≃ Circle × Complex.UnitDisc :=
  (Equiv.ofBijective
    (fun p : Circle × Complex.UnitDisc =>
      (⟨unitDiscStandardAutomorphismEquiv p.1 p.2,
        unitDiscStandardAutomorphismEquiv_mem_unitDiscAut p.1 p.2⟩ : unitDiscAut))
    ⟨fun _ _ h => unitDiscStandardAutomorphismEquiv_injective (congrArg Subtype.val h),
      fun e => by
        obtain ⟨u, a, ha⟩ := mem_unitDiscAut_iff.1 e.2
        exact ⟨(u, a), Subtype.ext ha.symm⟩⟩).symm

@[simp]
theorem coe_unitDiscAutEquivProd_symm (p : Circle × Complex.UnitDisc) :
    (unitDiscAutEquivProd.symm p : Equiv.Perm Complex.UnitDisc) =
      unitDiscStandardAutomorphismEquiv p.1 p.2 :=
  rfl

/-- The centre coordinate of an automorphism is its preimage of the origin. -/
theorem unitDiscAutEquivProd_apply_snd (e : unitDiscAut) :
    (unitDiscAutEquivProd e).2 = (e : Equiv.Perm Complex.UnitDisc).symm 0 := by
  conv_rhs => rw [← unitDiscAutEquivProd.symm_apply_apply e]
  rw [coe_unitDiscAutEquivProd_symm, unitDiscStandardAutomorphismEquiv_symm_apply_zero]

/-- The parametrisation, read as a characterisation of the coordinates of an automorphism. -/
theorem unitDiscAutEquivProd_eq_iff {e : unitDiscAut} {p : Circle × Complex.UnitDisc} :
    unitDiscAutEquivProd e = p ↔
      (e : Equiv.Perm Complex.UnitDisc) = unitDiscStandardAutomorphismEquiv p.1 p.2 := by
  rw [Equiv.apply_eq_iff_eq_symm_apply, Subtype.ext_iff, coe_unitDiscAutEquivProd_symm]

/-! ### The rotation subgroup is the circle group -/

/-- **The rotation subgroup of `Aut(𝔻)` is the circle group.** Mathlib's Cayley-theorem
construction `Equiv.Perm.subgroupOfMulAction` turns the faithfulness of the circle action into an
isomorphism onto the image of `Circle` in the permutations of the disc, and
`TauCeti.unitDiscRotation` is by definition that image, so it is that construction verbatim.

Together with `TauCeti.stabilizer_zero_eq_unitDiscRotation_subgroupOf`, this says the stabiliser of
the origin in `Aut(𝔻)` is a circle: the standard "rotations are the only automorphisms fixing the
centre, and distinct rotations are distinct automorphisms". -/
@[expose] noncomputable def circleMulEquivUnitDiscRotation : Circle ≃* unitDiscRotation :=
  Equiv.Perm.subgroupOfMulAction Circle Complex.UnitDisc

@[simp]
theorem coe_circleMulEquivUnitDiscRotation (u : Circle) :
    (circleMulEquivUnitDiscRotation u : Equiv.Perm Complex.UnitDisc) = MulAction.toPerm u :=
  rfl

/-! ### Rigidity: two fixed points force the identity -/

/-- **A holomorphic automorphism of the disc with two distinct fixed points is the identity.**

Conjugating by the Möbius factor centred at one fixed point moves it to the origin, so the
conjugate is an automorphism fixing `0`, hence a rotation by the classification.  That rotation
fixes the image of the second fixed point, which is nonzero because the two points are distinct,
so it is trivial by faithfulness of the circle action. -/
theorem eq_one_of_mem_unitDiscAut_of_isFixedPt {e : Equiv.Perm Complex.UnitDisc}
    (he : e ∈ unitDiscAut) {z w : Complex.UnitDisc} (hzw : z ≠ w)
    (hz : Function.IsFixedPt e z) (hw : Function.IsFixedPt e w) :
    e = 1 := by
  set M : Equiv.Perm Complex.UnitDisc := unitDiscMoebiusEquiv z with hM
  have hMmem : M ∈ unitDiscAut := by
    rw [hM, ← unitDiscStandardAutomorphismEquiv_one]
    exact unitDiscStandardAutomorphismEquiv_mem_unitDiscAut 1 z
  have hMz : M z = 0 := by rw [hM, unitDiscMoebiusEquiv_apply, unitDiscMoebius_self]
  have hMinv : M⁻¹ 0 = z := by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    exact hMz.symm
  have hMw : M w ≠ 0 := by
    rw [hM, unitDiscMoebiusEquiv_apply, Ne, unitDiscMoebius_eq_zero_iff]
    exact fun h => hzw h.symm
  -- The conjugate of `e` by `M` is an automorphism fixing the origin, hence a rotation.
  have hfmem : M * e * M⁻¹ ∈ unitDiscAut := mul_mem (mul_mem hMmem he) (inv_mem hMmem)
  have hf0 : (M * e * M⁻¹) 0 = 0 := by
    simp only [Equiv.Perm.mul_apply, hMinv, hz.eq, hMz]
  obtain ⟨u, a, hua⟩ := mem_unitDiscAut_iff.1 hfmem
  have ha : a = 0 := by
    have h0 : unitDiscStandardAutomorphismEquiv u a 0 = 0 := by rw [← hua]; exact hf0
    exact ((unitDiscStandardAutomorphismEquiv_eq_zero_iff u a 0).1 h0).symm
  subst ha
  -- The rotation fixes the nonzero point `M w`, so it is trivial.
  have hfMw : (M * e * M⁻¹) (M w) = M w := by
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hw.eq]
  have hu : u = 1 := by
    rw [hua] at hfMw
    simp only [unitDiscStandardAutomorphismEquiv_apply, unitDiscMoebius_zero] at hfMw
    refine circle_smul_left_injective hMw ?_
    change u • M w = (1 : Circle) • M w
    rw [hfMw, one_smul]
  have hone : M * e * M⁻¹ = 1 := by
    rw [hua, hu, unitDiscStandardAutomorphismEquiv_one_zero]
  exact mul_left_cancel ((mul_inv_eq_one.1 hone).trans (mul_one M).symm)

end TauCeti
