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
specialty, and are not proved here.

## Main definitions

* `TauCeti.adeleFiltrationSupDiagonal`: the subspace `(A_F(D) + F) ∩ A_F` of the repartition
  space, on which the Weil differentials bounded by `D` vanish.
* `TauCeti.weilDifferentialFiltration`: the space `Ω_F(D)` of Weil differentials bounded by a
  divisor (Definition 1.5.6), as a `k`-subspace of the dual of `A_F`.
* `TauCeti.weilDifferentialSpace`: the space `Ω_F` of all Weil differentials.
* `TauCeti.repartitionMul` and `TauCeti.weilDifferentialMul`: multiplication of a repartition by
  a function, and the induced action of `F` on the `k`-linear forms on `A_F` (Definition 1.5.8).
* `TauCeti.weilDifferentialSpaceModule`: the `F`-vector space structure on `Ω_F`.

## Main results

* `TauCeti.mem_weilDifferentialFiltration_of_apply_eq_zero` with
  `TauCeti.weilDifferential_apply_eq_zero_of_mem_adeleFiltration` and
  `TauCeti.weilDifferential_apply_eq_zero_of_mem_diagonalRepartitions`: membership in `Ω_F(D)`
  is vanishing on the repartitions bounded by `D` together with vanishing on the constants.
* `TauCeti.weilDifferentialFiltration_antitone` and `TauCeti.mem_weilDifferentialSpace_iff`: the
  filtration is antitone and directed, so a `k`-linear form is a Weil differential exactly when
  some single divisor bounds it.
* `TauCeti.weilDifferentialFiltration_eq_bot_iff`: `Ω_F(D) = 0` exactly when every repartition
  differs from a constant by one bounded by `D`.
* `TauCeti.weilDifferentialMul_mem_weilDifferentialFiltration`: multiplying by `z ∈ Fˣ` carries
  `Ω_F(D)` into `Ω_F(D + div z)`, so `Ω_F` is stable under the action
  (`TauCeti.weilDifferentialMul_mem_weilDifferentialSpace`).

## Implementation notes

`Ω_F(D)` is the annihilator, in the sense of `Submodule.dualAnnihilator`, of the subspace
`(A_F(D) + F) ∩ A_F` of `A_F`.  The intersection with `A_F` is not a restriction: the constants
are repartitions as soon as `F / k` is a function field
(`TauCeti.diagonalRepartitions_le_repartitionSpace`), and taking it means the definition of
`Ω_F(D)` itself needs no such hypothesis.  Because the definition is an annihilator,
`Submodule.dualQuotEquivDualAnnihilator` identifies `Ω_F(D)` with the dual of the cokernel
`A_F ⧸ (A_F(D) + F)` with no further work, which is how Lemma 1.5.7 will read `dim_k Ω_F(D)` off
the index of specialty.

The `F`-vector space structure `TauCeti.weilDifferentialSpaceModule` is a `def`, not an instance:
it exists only when `F / k` is a function field, and `IsFunctionField k F` is a hypothesis passed
explicitly rather than a class.  Consumers introduce it with `letI`, as
`TauCeti.weilDifferentialSpaceModule_smul` and
`TauCeti.isScalarTower_weilDifferentialSpace` do.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5.
-/

public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### The subspace `A_F(D) + F` -/

/-- The subspace `(A_F(D) + F) ∩ A_F` of the repartition space: the repartitions that differ
from a constant by one whose poles are bounded by `D`.  A Weil differential bounded by `D` is by
definition a `k`-linear form on `A_F` killing it. -/
noncomputable def adeleFiltrationSupDiagonal (D : Divisor k F) :
    Submodule k ↥(repartitionSpace k F) :=
  (adeleFiltration D ⊔ diagonalRepartitions k F).comap (repartitionSpace k F).subtype

/-- Membership in `(A_F(D) + F) ∩ A_F` is membership in `A_F(D) + F` of the underlying family. -/
@[simp]
theorem mem_adeleFiltrationSupDiagonal_iff {D : Divisor k F} {a : ↥(repartitionSpace k F)} :
    a ∈ adeleFiltrationSupDiagonal D ↔
      (a : Place k F → F) ∈ adeleFiltration D ⊔ diagonalRepartitions k F :=
  (Iff.rfl)

/-- Enlarging the divisor enlarges `(A_F(D) + F) ∩ A_F`. -/
theorem adeleFiltrationSupDiagonal_mono {D E : Divisor k F} (h : D ≤ E) :
    adeleFiltrationSupDiagonal D ≤ adeleFiltrationSupDiagonal E :=
  Submodule.comap_mono (sup_le_sup_right (adeleFiltration_mono h) _)

/-! ### Weil differentials bounded by a divisor -/

/-- The space `Ω_F(D)` of **Weil differentials bounded by `D`** (Stichtenoth, Definition 1.5.6):
the `k`-linear forms on the repartition space that vanish on `A_F(D) + F`. -/
noncomputable def weilDifferentialFiltration (D : Divisor k F) :
    Submodule k (Module.Dual k ↥(repartitionSpace k F)) :=
  (adeleFiltrationSupDiagonal D).dualAnnihilator

/-- Membership in `Ω_F(D)`, unfolded: the form kills every repartition in `A_F(D) + F`. -/
theorem mem_weilDifferentialFiltration_iff {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} :
    ω ∈ weilDifferentialFiltration D ↔ ∀ a ∈ adeleFiltrationSupDiagonal D, ω a = 0 :=
  Submodule.mem_dualAnnihilator ω

/-- A Weil differential bounded by `D` kills every repartition whose poles are bounded by `D`. -/
theorem weilDifferential_apply_eq_zero_of_mem_adeleFiltration {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialFiltration D)
    (a : ↥(repartitionSpace k F)) (ha : (a : Place k F → F) ∈ adeleFiltration D) : ω a = 0 :=
  mem_weilDifferentialFiltration_iff.mp hω a
    (mem_adeleFiltrationSupDiagonal_iff.mpr (Submodule.mem_sup_left ha))

/-- A Weil differential bounded by `D` kills every constant repartition. -/
theorem weilDifferential_apply_eq_zero_of_mem_diagonalRepartitions {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialFiltration D)
    (a : ↥(repartitionSpace k F)) (ha : (a : Place k F → F) ∈ diagonalRepartitions k F) :
    ω a = 0 :=
  mem_weilDifferentialFiltration_iff.mp hω a
    (mem_adeleFiltrationSupDiagonal_iff.mpr (Submodule.mem_sup_right ha))

/-- **The two vanishing conditions defining `Ω_F(D)`**: a `k`-linear form on `A_F` that kills the
repartitions bounded by `D` and kills the constants is a Weil differential bounded by `D`. -/
theorem mem_weilDifferentialFiltration_of_apply_eq_zero {D : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)}
    (h₁ : ∀ a : ↥(repartitionSpace k F), (a : Place k F → F) ∈ adeleFiltration D → ω a = 0)
    (h₂ : ∀ a : ↥(repartitionSpace k F), (a : Place k F → F) ∈ diagonalRepartitions k F →
      ω a = 0) :
    ω ∈ weilDifferentialFiltration D := by
  refine mem_weilDifferentialFiltration_iff.mpr fun a ha ↦ ?_
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (mem_adeleFiltrationSupDiagonal_iff.mp ha)
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
  Submodule.dualAnnihilator_anti (adeleFiltrationSupDiagonal_mono h)

/-- **`Ω_F(D)` vanishes exactly when `A_F(D) + F` is everything**: the only `k`-linear form on
`A_F` vanishing on `A_F(D) + F` is `0` precisely when every repartition already differs from a
constant by one whose poles are bounded by `D`. -/
theorem weilDifferentialFiltration_eq_bot_iff (hF : IsFunctionField k F) (D : Divisor k F) :
    weilDifferentialFiltration D = ⊥ ↔
      adeleFiltration D ⊔ diagonalRepartitions k F = repartitionSpace k F := by
  rw [weilDifferentialFiltration, Submodule.dualAnnihilator_eq_bot_iff]
  constructor
  · intro h
    refine le_antisymm (adeleFiltration_sup_diagonalRepartitions_le hF D) fun a ha ↦ ?_
    exact mem_adeleFiltrationSupDiagonal_iff.mp (Submodule.eq_top_iff'.mp h ⟨a, ha⟩)
  · intro h
    refine Submodule.eq_top_iff'.mpr fun a ↦ ?_
    rw [mem_adeleFiltrationSupDiagonal_iff, h]
    exact a.2

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

/-- The filtration is directed: any two of its members are both contained in the one attached to
the pointwise minimum of the two divisors. -/
theorem directed_weilDifferentialFiltration :
    Directed (· ≤ ·) (weilDifferentialFiltration : Divisor k F →
      Submodule k (Module.Dual k ↥(repartitionSpace k F))) := fun D E ↦
  ⟨D ⊓ E, weilDifferentialFiltration_antitone inf_le_left,
    weilDifferentialFiltration_antitone inf_le_right⟩

/-- **A `k`-linear form on `A_F` is a Weil differential exactly when a single divisor bounds
it**: the supremum defining `Ω_F` is the union of the `Ω_F(D)`, because they are directed. -/
theorem mem_weilDifferentialSpace_iff {ω : Module.Dual k ↥(repartitionSpace k F)} :
    ω ∈ weilDifferentialSpace k F ↔ ∃ D : Divisor k F, ω ∈ weilDifferentialFiltration D :=
  Submodule.mem_iSup_of_directed _ directed_weilDifferentialFiltration

/-! ### Multiplication by a function -/

/-- Multiplication of repartitions by a function, as a `k`-algebra map to the `k`-linear
endomorphisms of the repartition space.  It lands in the repartition space because a function of
an algebraic function field has only finitely many poles. -/
noncomputable def repartitionMul (hF : IsFunctionField k F) :
    F →ₐ[k] Module.End k ↥(repartitionSpace k F) where
  toFun f :=
    { toFun a := ⟨f • (a : Place k F → F), smul_mem_repartitionSpace hF f a.2⟩
      map_add' a b := Subtype.ext (by simp [smul_add])
      map_smul' c a := Subtype.ext (by simp [smul_comm f c]) }
  map_one' := LinearMap.ext fun a ↦ Subtype.ext (by simp)
  map_mul' f g := LinearMap.ext fun a ↦ Subtype.ext (by simp [mul_smul])
  map_zero' := LinearMap.ext fun a ↦ Subtype.ext (by simp)
  map_add' f g := LinearMap.ext fun a ↦ Subtype.ext (by simp [add_smul])
  commutes' c := LinearMap.ext fun a ↦ Subtype.ext (by simp [algebraMap_smul])

/-- Multiplying a repartition by `f` multiplies each of its entries by `f`. -/
@[simp]
theorem coe_repartitionMul_apply (hF : IsFunctionField k F) (f : F)
    (a : ↥(repartitionSpace k F)) :
    ((repartitionMul hF f a : ↥(repartitionSpace k F)) : Place k F → F) =
      f • (a : Place k F → F) :=
  (rfl)

/-- The multiplication action of `F` on the `k`-linear forms on the repartition space
(Stichtenoth, Definition 1.5.8): `(f · ω) a = ω (f · a)`.  It is a `k`-algebra map because `F` is
commutative, so the transposes of the multiplication maps compose in either order. -/
noncomputable def weilDifferentialMul (hF : IsFunctionField k F) :
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
theorem weilDifferentialMul_apply_apply (hF : IsFunctionField k F) (f : F)
    (ω : Module.Dual k ↥(repartitionSpace k F)) (a : ↥(repartitionSpace k F)) :
    weilDifferentialMul hF f ω a = ω (repartitionMul hF f a) :=
  (rfl)

/-- **Multiplication translates the filtration by a principal divisor**: multiplying by a nonzero
function `z` carries `Ω_F(D)` into `Ω_F(D + div z)`, exactly as it carries `A_F(D + div z)` into
`A_F(D)`. -/
theorem weilDifferentialMul_mem_weilDifferentialFiltration (hF : IsFunctionField k F) (z : Fˣ)
    {D : Divisor k F} {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialFiltration D) :
    weilDifferentialMul hF (z : F) ω ∈
      weilDifferentialFiltration (D + Divisor.principal hF z) := by
  refine mem_weilDifferentialFiltration_of_apply_eq_zero (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · rw [weilDifferentialMul_apply_apply]
    refine weilDifferential_apply_eq_zero_of_mem_adeleFiltration hω _ ?_
    rw [coe_repartitionMul_apply]
    exact (smul_mem_adeleFiltration_iff hF z D _).mpr ha
  · rw [weilDifferentialMul_apply_apply]
    obtain ⟨g, hg⟩ := mem_diagonalRepartitions_iff.mp ha
    refine weilDifferential_apply_eq_zero_of_mem_diagonalRepartitions hω _ ?_
    rw [coe_repartitionMul_apply, ← hg]
    exact const_mem_diagonalRepartitions ((z : F) * g)

/-- **`Ω_F` is stable under multiplication by a function**, which is what makes it a vector space
over `F` and not merely over `k`. -/
theorem weilDifferentialMul_mem_weilDifferentialSpace (hF : IsFunctionField k F) (f : F)
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ∈ weilDifferentialSpace k F) :
    weilDifferentialMul hF f ω ∈ weilDifferentialSpace k F := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · obtain ⟨D, hD⟩ := mem_weilDifferentialSpace_iff.mp hω
    exact weilDifferentialFiltration_le_weilDifferentialSpace _
      (weilDifferentialMul_mem_weilDifferentialFiltration hF (Units.mk0 f hf) hD)

/-- The multiplication action of `F` on `Ω_F` itself, the restriction of
`TauCeti.weilDifferentialMul` to the stable subspace of Weil differentials. -/
noncomputable def weilDifferentialSpaceMul (hF : IsFunctionField k F) :
    F →ₐ[k] Module.End k ↥(weilDifferentialSpace k F) where
  toFun f := LinearMap.restrict (weilDifferentialMul hF f)
    fun _ hω ↦ weilDifferentialMul_mem_weilDifferentialSpace hF f hω
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
      Module.Dual k ↥(repartitionSpace k F)) = weilDifferentialMul hF f ω :=
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
action `TauCeti.weilDifferentialMul`. -/
theorem weilDifferentialSpaceModule_smul (hF : IsFunctionField k F) (f : F)
    (ω : ↥(weilDifferentialSpace k F)) :
    letI := weilDifferentialSpaceModule hF
    ((f • ω : ↥(weilDifferentialSpace k F)) :
      Module.Dual k ↥(repartitionSpace k F)) = weilDifferentialMul hF f ω :=
  (rfl)

/-- The `F`-vector space structure on `Ω_F` extends its `k`-vector space structure. -/
theorem isScalarTower_weilDifferentialSpace (hF : IsFunctionField k F) :
    letI := weilDifferentialSpaceModule hF
    IsScalarTower k F ↥(weilDifferentialSpace k F) := by
  let := weilDifferentialSpaceModule hF
  refine ⟨fun c f ω ↦ Subtype.ext ?_⟩
  rw [weilDifferentialSpaceModule_smul, Submodule.coe_smul, weilDifferentialSpaceModule_smul,
    map_smul, LinearMap.smul_apply]

end TauCeti
