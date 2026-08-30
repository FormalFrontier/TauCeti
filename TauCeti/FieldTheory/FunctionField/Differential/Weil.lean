/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.FieldTheory.FunctionField.Repartition.Basic

/-!
# Weil differentials of an algebraic function field

A **Weil differential** of an algebraic function field `F / k` is a `k`-linear form on the
repartition space `A_F` that vanishes on `A_F(D) + F` for some divisor `D`.  Writing

`Ω_F(D) = {ω : A_F →ₗ[k] k | ω vanishes on (A_F(D) + F) ∩ A_F}`,

the space of all Weil differentials is `Ω_F = ⨆_D Ω_F(D)`, and multiplying repartitions by a
function `f ∈ F` makes `Ω_F` a vector space over `F` itself, by `(f · ω) a := ω (f · a)`.

This file constructs `Ω_F(D)`, `Ω_F` and that `F`-action.  It is Stichtenoth, *Algebraic Function
Fields and Codes*, 2nd ed., Definitions 1.5.6 and 1.5.8.  The two theorems that make the objects
built here compute — `dim_k Ω_F(D) = i(D)` (Lemma 1.5.7) and `dim_F Ω_F = 1` (Proposition 1.5.9)
— rest on the quotient interpretation `i(D) = dim_k (A_F ⧸ (A_F(D) + F))` of the index of
specialty, and are proved in `TauCeti/FieldTheory/FunctionField/Differential/Dimension.lean`.

## Main definitions

* `TauCeti.weilDifferentialFiltration`: the space `Ω_F(D)` of Weil differentials bounded by a
  divisor (Definition 1.5.6), as a `k`-subspace of the dual of `A_F`.
* `TauCeti.weilDifferentialSpace`: the space `Ω_F` of all Weil differentials.
* `TauCeti.repartitionDualMul`: the action of `F` on the `k`-linear forms on `A_F`, induced by
  multiplication of repartitions by a function (Definition 1.5.8).
* `TauCeti.weilDifferentialSpaceMul` and `TauCeti.weilDifferentialSpaceModule`: its restriction
  to `Ω_F`, and the resulting `F`-vector space structure.

## Main results

* `TauCeti.mem_weilDifferentialFiltration_of_apply_eq_zero` with
  `TauCeti.weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration` and
  `TauCeti.weilDifferentialFiltration_apply_eq_zero_of_mem_diagonalRepartitions`: membership in
  `Ω_F(D)` is vanishing on the repartitions bounded by `D` together with vanishing on the
  constants.
* `TauCeti.weilDifferentialFiltration_antitone` and `TauCeti.mem_weilDifferentialSpace_iff`: the
  filtration is antitone and directed, so a `k`-linear form is a Weil differential exactly when
  some single divisor bounds it.
* `TauCeti.weilDifferentialFiltration_eq_bot_iff`: `Ω_F(D) = 0` exactly when every repartition
  differs from a constant by one bounded by `D`.
* `TauCeti.repartitionDualMul_mem_weilDifferentialFiltration_iff`: for `z ∈ Fˣ`, a linear form
  lies in `Ω_F(D)` exactly when `z · ω` lies in `Ω_F(D + div z)`, so `Ω_F` is stable under the
  action (`TauCeti.repartitionDualMul_mem_weilDifferentialSpace`).

## Implementation notes

`Ω_F(D)` is the annihilator, in the sense of `Submodule.dualAnnihilator`, of the subspace
`(A_F(D) + F) ∩ A_F` of `A_F`, which is
`TauCeti.submoduleOfAdeleFiltrationSupDiagonalRepartitions`.  The intersection with `A_F` is not
a restriction: the constants are repartitions as soon as `F / k` is a function field
(`TauCeti.diagonalRepartitions_le_repartitionSpace`), and taking it means the definition of
`Ω_F(D)` itself needs no such hypothesis.  Because the definition is an annihilator —
`TauCeti.weilDifferentialFiltration_eq_dualAnnihilator` —
`Submodule.dualQuotEquivDualAnnihilator` identifies `Ω_F(D)` with the dual of the cokernel
`A_F ⧸ (A_F(D) + F)` with no further work, which is how Lemma 1.5.7 will read `dim_k Ω_F(D)` off
the index of specialty.

The `F`-vector space structure `TauCeti.weilDifferentialSpaceModule` is a `def`, not an instance:
it exists only when `F / k` is a function field, and `IsFunctionField k F` is a hypothesis passed
explicitly rather than a class.  Consumers introduce it with `letI`, as
`TauCeti.coe_weilDifferentialSpaceModule_smul` and
`TauCeti.isScalarTower_weilDifferentialSpace` do.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5.
-/

public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### Weil differentials bounded by a divisor -/

/-- The space `Ω_F(D)` of **Weil differentials bounded by `D`** (Stichtenoth, Definition 1.5.6):
the `k`-linear forms on the repartition space that vanish on `A_F(D) + F`. -/
noncomputable def weilDifferentialFiltration (D : Divisor k F) :
    Submodule k (Module.Dual k ↥(repartitionSpace k F)) :=
  (submoduleOfAdeleFiltrationSupDiagonalRepartitions D).dualAnnihilator

/-- `Ω_F(D)` is the annihilator of `(A_F(D) + F) ∩ A_F`, which is how
`Submodule.dualQuotEquivDualAnnihilator` identifies it with the dual of the cokernel
`A_F ⧸ (A_F(D) + F)`. -/
theorem weilDifferentialFiltration_eq_dualAnnihilator (D : Divisor k F) :
    weilDifferentialFiltration D =
      (submoduleOfAdeleFiltrationSupDiagonalRepartitions D).dualAnnihilator := by
  rfl

/-- Membership in `Ω_F(D)`, unfolded: the form kills every repartition in `A_F(D) + F`. -/
theorem mem_weilDifferentialFiltration_iff {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} :
    ω ∈ weilDifferentialFiltration D ↔
      ∀ a ∈ submoduleOfAdeleFiltrationSupDiagonalRepartitions D, ω a = 0 :=
  Submodule.mem_dualAnnihilator ω

/-- A Weil differential bounded by `D` kills every repartition whose poles are bounded by `D`. -/
theorem weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialFiltration D)
    (a : ↥(repartitionSpace k F)) (ha : (a : Place k F → F) ∈ adeleFiltration D) : ω a = 0 :=
  mem_weilDifferentialFiltration_iff.mp hω a
    (mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff.mpr (Submodule.mem_sup_left ha))

/-- A Weil differential bounded by `D` kills every constant repartition. -/
theorem weilDifferentialFiltration_apply_eq_zero_of_mem_diagonalRepartitions {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialFiltration D)
    (a : ↥(repartitionSpace k F)) (ha : (a : Place k F → F) ∈ diagonalRepartitions k F) :
    ω a = 0 :=
  mem_weilDifferentialFiltration_iff.mp hω a
    (mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff.mpr (Submodule.mem_sup_right ha))

/-- **The two vanishing conditions defining `Ω_F(D)`**: a `k`-linear form on `A_F` that kills the
repartitions bounded by `D` and kills the constants is a Weil differential bounded by `D`. -/
theorem mem_weilDifferentialFiltration_of_apply_eq_zero {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)}
    (h₁ : ∀ a : ↥(repartitionSpace k F), (a : Place k F → F) ∈ adeleFiltration D → ω a = 0)
    (h₂ : ∀ a : ↥(repartitionSpace k F), (a : Place k F → F) ∈ diagonalRepartitions k F →
      ω a = 0) :
    ω ∈ weilDifferentialFiltration D := by
  refine mem_weilDifferentialFiltration_iff.mpr fun a ha ↦ ?_
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp
    (mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff.mp ha)
  have hxA : x ∈ repartitionSpace k F := adeleFiltration_le_repartitionSpace D hx
  have hyA : y ∈ repartitionSpace k F := by
    have : (a : Place k F → F) - x ∈ repartitionSpace k F :=
      (repartitionSpace k F).sub_mem a.2 hxA
    rwa [← hxy, add_sub_cancel_left] at this
  have hsplit : a = ⟨x, hxA⟩ + ⟨y, hyA⟩ := Subtype.ext hxy.symm
  rw [hsplit, map_add, h₁ ⟨x, hxA⟩ hx, h₂ ⟨y, hyA⟩ hy, add_zero]

/-- Enlarging the divisor shrinks the space of Weil differentials it bounds. -/
theorem weilDifferentialFiltration_antitone :
    Antitone (weilDifferentialFiltration : Divisor k F →
      Submodule k (Module.Dual k ↥(repartitionSpace k F))) := fun _ _ h ↦
  Submodule.dualAnnihilator_anti (submoduleOfAdeleFiltrationSupDiagonalRepartitions_mono h)

/-- **`Ω_F(D)` vanishes exactly when `A_F(D) + F` is everything**: the only `k`-linear form on
`A_F` vanishing on `A_F(D) + F` is `0` precisely when every repartition already differs from a
constant by one whose poles are bounded by `D`. -/
theorem weilDifferentialFiltration_eq_bot_iff (hF : IsFunctionField k F) (D : Divisor k F) :
    weilDifferentialFiltration D = ⊥ ↔
      adeleFiltration D ⊔ diagonalRepartitions k F = repartitionSpace k F := by
  rw [weilDifferentialFiltration_eq_dualAnnihilator, Submodule.dualAnnihilator_eq_bot_iff,
    submoduleOfAdeleFiltrationSupDiagonalRepartitions_eq_submoduleOf,
    Submodule.submoduleOf_eq_top]
  exact ⟨fun h ↦ le_antisymm (adeleFiltration_sup_diagonalRepartitions_le hF D) h, fun h ↦ h.ge⟩

/-! ### The space of all Weil differentials -/

variable (k F) in
/-- The space `Ω_F` of **Weil differentials** of `F / k` (Stichtenoth, Definition 1.5.6): the
`k`-linear forms on the repartition space that some divisor bounds. -/
noncomputable def weilDifferentialSpace : Submodule k (Module.Dual k ↥(repartitionSpace k F)) :=
  ⨆ D : Divisor k F, weilDifferentialFiltration D

/-- Every Weil differential bounded by a divisor is a Weil differential. -/
theorem weilDifferentialFiltration_le_weilDifferentialSpace (D : Divisor k F) :
    weilDifferentialFiltration D ≤ weilDifferentialSpace k F :=
  le_iSup (fun D : Divisor k F ↦ weilDifferentialFiltration D) D

/-- The filtration is directed: it is antitone, and any two divisors have a lower bound, namely
their pointwise minimum, whose member then contains both. -/
theorem directed_weilDifferentialFiltration :
    Directed (· ≤ ·) (weilDifferentialFiltration : Divisor k F →
      Submodule k (Module.Dual k ↥(repartitionSpace k F))) :=
  weilDifferentialFiltration_antitone.directed_le

/-- **A `k`-linear form on `A_F` is a Weil differential exactly when a single divisor bounds
it**: the supremum defining `Ω_F` is the union of the `Ω_F(D)`, because they are directed. -/
theorem mem_weilDifferentialSpace_iff {ω : Module.Dual k ↥(repartitionSpace k F)} :
    ω ∈ weilDifferentialSpace k F ↔ ∃ D : Divisor k F, ω ∈ weilDifferentialFiltration D :=
  Submodule.mem_iSup_of_directed _ directed_weilDifferentialFiltration

/-! ### Multiplication by a function -/

/-- The multiplication action of `F` on the `k`-linear forms on the repartition space
(Stichtenoth, Definition 1.5.8): `(f · ω) a = ω (f · a)`.  It is a `k`-algebra map because `F` is
commutative, so the transposes of the multiplication maps compose in either order. -/
noncomputable def repartitionDualMul (hF : IsFunctionField k F) :
    F →ₐ[k] Module.End k (Module.Dual k ↥(repartitionSpace k F)) where
  toFun f := (repartitionMul hF f).dualMap
  map_one' := LinearMap.ext fun ω ↦ LinearMap.ext fun a ↦ by simp
  map_mul' f g := LinearMap.ext fun ω ↦ LinearMap.ext fun a ↦ by
    simp [mul_comm f g]
  map_zero' := LinearMap.ext fun ω ↦ LinearMap.ext fun a ↦ by simp
  map_add' f g := LinearMap.ext fun ω ↦ LinearMap.ext fun a ↦ by simp
  commutes' c := LinearMap.ext fun ω ↦ LinearMap.ext fun a ↦ by simp [map_smul]

/-- The defining formula `(f · ω) a = ω (f · a)` of the action of `F` on the linear forms. -/
@[simp]
theorem repartitionDualMul_apply_apply (hF : IsFunctionField k F) (f : F)
    (ω : Module.Dual k ↥(repartitionSpace k F)) (a : ↥(repartitionSpace k F)) :
    repartitionDualMul hF f ω a = ω (repartitionMul hF f a) :=
  (rfl)

/-- Multiplying twice is multiplying once by the product.  It is not a `simp` lemma: `map_mul`
rewrites in the opposite direction. -/
theorem repartitionDualMul_repartitionDualMul (hF : IsFunctionField k F) (f g : F)
    (ω : Module.Dual k ↥(repartitionSpace k F)) :
    repartitionDualMul hF f (repartitionDualMul hF g ω) = repartitionDualMul hF (f * g) ω := by
  rw [← Module.End.mul_apply, ← map_mul]

/-- **Multiplication translates the filtration by a principal divisor**: for a nonzero function
`z`, a linear form is bounded by `D` exactly when `z · ω` is bounded by `D + div z`, exactly as
multiplication by `z` carries `A_F(D + div z)` into `A_F(D)`. -/
theorem repartitionDualMul_mem_weilDifferentialFiltration_iff (hF : IsFunctionField k F) (z : Fˣ)
    {D : Divisor k F} {ω : Module.Dual k ↥(repartitionSpace k F)} :
    repartitionDualMul hF (z : F) ω ∈ weilDifferentialFiltration (D + Divisor.principal hF z) ↔
      ω ∈ weilDifferentialFiltration D := by
  have key : ∀ (y : Fˣ) (E : Divisor k F) (η : Module.Dual k ↥(repartitionSpace k F)),
      η ∈ weilDifferentialFiltration E →
      repartitionDualMul hF (y : F) η ∈
        weilDifferentialFiltration (E + Divisor.principal hF y) := by
    refine fun y E η hη ↦ mem_weilDifferentialFiltration_of_apply_eq_zero
      (fun a ha ↦ ?_) (fun a ha ↦ ?_)
    · rw [repartitionDualMul_apply_apply]
      refine weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hη _ ?_
      rw [coe_repartitionMul_apply]
      exact (smul_mem_adeleFiltration_iff hF y E _).mpr ha
    · rw [repartitionDualMul_apply_apply]
      refine weilDifferentialFiltration_apply_eq_zero_of_mem_diagonalRepartitions hη _ ?_
      rw [coe_repartitionMul_apply]
      exact smul_mem_diagonalRepartitions (y : F) ha
  refine ⟨fun h ↦ ?_, key z D ω⟩
  have hzz : repartitionDualMul hF ((z⁻¹ : Fˣ) : F) (repartitionDualMul hF (z : F) ω) = ω := by
    rw [← Module.End.mul_apply, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      map_one, Module.End.one_apply]
  have hD : D + Divisor.principal hF z + Divisor.principal hF z⁻¹ = D := by
    rw [Divisor.principal_inv, add_neg_cancel_right]
  have h' := key z⁻¹ _ _ h
  rwa [hzz, hD] at h'

/-- **`Ω_F` is stable under multiplication by a function**, which is what makes it a vector space
over `F` and not merely over `k`. -/
theorem repartitionDualMul_mem_weilDifferentialSpace (hF : IsFunctionField k F) (f : F)
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialSpace k F) :
    repartitionDualMul hF f ω ∈ weilDifferentialSpace k F := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · obtain ⟨D, hD⟩ := mem_weilDifferentialSpace_iff.mp hω
    exact weilDifferentialFiltration_le_weilDifferentialSpace _
      ((repartitionDualMul_mem_weilDifferentialFiltration_iff hF (Units.mk0 f hf)).mpr hD)

/-- The multiplication action of `F` on `Ω_F` itself, the restriction of
`TauCeti.repartitionDualMul` to the stable subspace of Weil differentials. -/
noncomputable def weilDifferentialSpaceMul (hF : IsFunctionField k F) :
    F →ₐ[k] Module.End k ↥(weilDifferentialSpace k F) where
  toFun f := LinearMap.restrict (repartitionDualMul hF f)
    fun _ hω ↦ repartitionDualMul_mem_weilDifferentialSpace hF f hω
  map_one' := LinearMap.ext fun ω ↦ Subtype.ext (by simp)
  map_mul' f g := LinearMap.ext fun ω ↦ Subtype.ext (by simp)
  map_zero' := LinearMap.ext fun ω ↦ Subtype.ext (by simp)
  map_add' f g := LinearMap.ext fun ω ↦ Subtype.ext (by simp)
  commutes' c := LinearMap.ext fun ω ↦ Subtype.ext (by simp)

/-- The action of `F` on `Ω_F` is the restriction of its action on all the linear forms. -/
@[simp]
theorem coe_weilDifferentialSpaceMul_apply (hF : IsFunctionField k F) (f : F)
    (ω : ↥(weilDifferentialSpace k F)) :
    ((weilDifferentialSpaceMul hF f ω : ↥(weilDifferentialSpace k F)) :
      Module.Dual k ↥(repartitionSpace k F)) = repartitionDualMul hF f ω :=
  (rfl)

/-- **The `F`-vector space structure on `Ω_F`** (Stichtenoth, Definition 1.5.8): `(f · ω) a` is
`ω (f · a)`.  It is a `def` and not an instance because it exists only for an algebraic function
field, and `TauCeti.IsFunctionField` is an explicit hypothesis, not a class; introduce it with
`letI`. -/
@[instance_reducible]
noncomputable def weilDifferentialSpaceModule (hF : IsFunctionField k F) :
    Module F ↥(weilDifferentialSpace k F) :=
  Module.compHom _ (weilDifferentialSpaceMul hF).toRingHom

/-- The scalar multiplication of `TauCeti.weilDifferentialSpaceModule` is the multiplication
action `TauCeti.repartitionDualMul`. -/
theorem coe_weilDifferentialSpaceModule_smul (hF : IsFunctionField k F) (f : F)
    (ω : ↥(weilDifferentialSpace k F)) :
    letI := weilDifferentialSpaceModule hF
    ((f • ω : ↥(weilDifferentialSpace k F)) :
      Module.Dual k ↥(repartitionSpace k F)) = repartitionDualMul hF f ω :=
  (rfl)

/-- The `F`-vector space structure on `Ω_F` extends its `k`-vector space structure. -/
theorem isScalarTower_weilDifferentialSpace (hF : IsFunctionField k F) :
    letI := weilDifferentialSpaceModule hF
    IsScalarTower k F ↥(weilDifferentialSpace k F) := by
  let := weilDifferentialSpaceModule hF
  refine ⟨fun c f ω ↦ Subtype.ext ?_⟩
  rw [coe_weilDifferentialSpaceModule_smul, Submodule.coe_smul,
    coe_weilDifferentialSpaceModule_smul, map_smul, LinearMap.smul_apply]

end TauCeti
