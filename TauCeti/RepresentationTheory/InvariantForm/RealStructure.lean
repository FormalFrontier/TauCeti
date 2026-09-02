/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.RepresentationTheory.InvariantForm.Hermitian
public import TauCeti.RepresentationTheory.RealForm

/-!
# Real structures and invariant symmetric forms, against a fixed invariant Hermitian form

An invariant *symmetric bilinear* form `B` on an irreducible complex representation is strictly
weaker than a real form.  Together with a positive definite invariant *Hermitian* form `H`,
however, it produces one: this file builds a `Representation.IsRealStructure` -- a conjugate-linear
involution of `V` commuting with the action -- out of the two forms, and goes back again, so that
against a fixed `H` the two data are interchangeable.

Comparing the two forms produces a conjugate-linear map `J` of `V` determined by
`H (J x) y = B x y`.  It exists because `H`, read as a map `V → V*`, is injective by definiteness
and hence bijective -- as an `ℝ`-linear map between two spaces of the same finite real dimension --
so it can be inverted on the `ℂ`-linear map `x ↦ B x`.  Invariance of both forms makes `J` commute
with the action, so `J ∘ J` is a `ℂ`-linear self-intertwiner, and Schur's lemma over the
algebraically closed `ℂ` forces `J ∘ J = c • id`.  Symmetry of `B` and the Hermitian symmetry of
`H` then evaluate `c`:

`H (J x) (J x) = B x (J x) = B (J x) x = H (J (J x)) x = conj c * H x x`,

so `c` is the ratio of two positive reals.  Rescaling `J` by the inverse square root of `c` -- a
*real* scalar, so conjugate-linearity survives -- turns it into an involution, that is, into a real
structure, whose real points are a real form.

Only the two forms are needed, so nothing here asks for a finite group; producing the invariant
Hermitian form is where finiteness enters, in
`TauCeti/RepresentationTheory/InvariantForm/Hermitian.lean`, and the Frobenius-Schur criterion this
feeds is in `TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Realizability.lean`.

The **converse** passage, from a real structure `K` back to an invariant symmetric form, is the
second half of the file, and it needs neither irreducibility nor finite dimensionality.  The naive
guess `B x y = H (K x) y` is bilinear, invariant and nondegenerate for free, but it is symmetric
only if `H` is compatible with `K` in the sense `H (K x) (K y) = conj (H x y)`, which an arbitrary
invariant `H` need not be.  Replacing `H` by the **balanced** form
`H x y + conj (H (K x) (K y))` -- still invariant, Hermitian and positive definite, since `K` is
bijective -- makes it compatible, and then `B x y = H (K x) y` is symmetric.  Against a fixed `H`
the two directions assemble into `Representation.exists_isRealStructure_iff`, which is what turns
the Frobenius-Schur value `1` into realizability over `ℝ` whenever a positive definite invariant
Hermitian form is available -- by Haar averaging for a compact group as much as by summation for a
finite one.

## Main results

* `Representation.exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm`: **an
  irreducible representation carrying a nondegenerate invariant symmetric form and a nonnegative
  invariant Hermitian form that is definite off the origin has a real structure.**
* `Representation.exists_isInvariantForm_isSymm_nondegenerate_of_isRealStructure`: **a real
  structure, together with a positive definite invariant Hermitian form, produces a nondegenerate
  invariant symmetric form.**
* `Representation.exists_isRealStructure_iff`: against a positive definite invariant Hermitian
  form, an irreducible finite-dimensional representation has a real structure exactly when it
  carries a nondegenerate invariant symmetric form.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7: the passage from a "compatible Hermitian form" to the real structure that the
  realizability target `frobeniusSchurIndicatorRep_eq_one_realizable` is read off from.
* [Compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  Layer 6b: the structure-map reading of the Frobenius-Schur value `1`, which consumes the
  equivalence below.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §6.
-/

public section

open Module (Dual)

open scoped ComplexOrder

open LinearMap (BilinForm)

open TauCeti

namespace Representation

open TauCeti.Representation

/-! ### Inverting a definite Hermitian form -/

section Inverting

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A sesquilinear form read as an `ℝ`-linear map to the complex dual.  The conjugation on the
scalars is the identity on the reals, so only the real structure survives the bundling; that is
enough for the dimension count, which is all this map is used for. -/
private noncomputable def sesqToDualReal (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : V →ₗ[ℝ] Dual ℂ V where
  toFun := H
  map_add' := H.map_add
  map_smul' r x := by
    simp only [RingHom.id_apply, ← IsScalarTower.algebraMap_smul (R := ℝ) ℂ r, map_smulₛₗ,
      Complex.coe_algebraMap, Complex.conj_ofReal]

private theorem sesqToDualReal_apply (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (x : V) :
    sesqToDualReal H x = H x := (rfl)

variable [FiniteDimensional ℂ V]

/-- A positive definite sesquilinear form on a finite-dimensional complex space is a bijection onto
the complex dual: definiteness makes it injective, and `V` and `V*` have the same finite dimension
over `ℝ`, having the same finite dimension over `ℂ`. -/
private theorem sesqToDualReal_bijective (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) : Function.Bijective (sesqToDualReal H) := by
  have hfinV : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  have hfinD : FiniteDimensional ℝ (Dual ℂ V) := Module.Finite.trans ℂ (Dual ℂ V)
  have hinj : Function.Injective (sesqToDualReal H) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    refine hdef x hne ?_
    have hzero : H x = 0 := by simpa only [sesqToDualReal_apply] using hx
    simp [hzero]
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [← Module.finrank_mul_finrank ℝ ℂ V, ← Module.finrank_mul_finrank ℝ ℂ (Dual ℂ V),
    Subspace.dual_finrank_eq]

/-- A positive definite sesquilinear form on a finite-dimensional complex space, as an `ℝ`-linear
equivalence onto the complex dual. -/
private noncomputable def sesqEquivDual (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) : V ≃ₗ[ℝ] Dual ℂ V :=
  LinearEquiv.ofBijective (sesqToDualReal H) (sesqToDualReal_bijective H hdef)

private theorem sesqEquivDual_apply (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (x : V) : sesqEquivDual H hdef x = H x := (rfl)

/-- A positive definite form separates vectors. -/
private theorem eq_of_forall_sesq_eq (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) {u v : V} (h : ∀ y : V, H u y = H v y) : u = v := by
  refine (sesqEquivDual H hdef).injective ?_
  rw [sesqEquivDual_apply, sesqEquivDual_apply]
  exact LinearMap.ext h

private theorem sesq_apply_symm_apply (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (f : Dual ℂ V) (y : V) :
    H ((sesqEquivDual H hdef).symm f) y = f y := by
  have h := (sesqEquivDual H hdef).apply_symm_apply f
  rw [sesqEquivDual_apply] at h
  exact DFunLike.congr_fun h y

/-! ### The conjugate-linear map comparing the two forms -/

/-- The conjugate-linear map `J` comparing a bilinear form `B` with a positive definite
sesquilinear form `H`, characterized by `H (J x) y = B x y`.  It is conjugate-linear because `H`
carries a conjugation in its first argument while `B` carries none. -/
private noncomputable def compareForms (B : BilinForm ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) : V →ₛₗ[starRingEnd ℂ] V where
  toFun x := (sesqEquivDual H hdef).symm (B x)
  map_add' x y := by simp
  map_smul' c x := by
    refine eq_of_forall_sesq_eq H hdef fun y => ?_
    have hl : H ((sesqEquivDual H hdef).symm (B (c • x))) y = c * B x y := by
      rw [sesq_apply_symm_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hr : H ((starRingEnd ℂ) c • (sesqEquivDual H hdef).symm (B x)) y = c * B x y := by
      rw [map_smulₛₗ, LinearMap.smul_apply, sesq_apply_symm_apply, Complex.conj_conj, smul_eq_mul]
    exact hl.trans hr.symm

private theorem compareForms_apply (B : BilinForm ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (x : V) :
    compareForms B H hdef x = (sesqEquivDual H hdef).symm (B x) := (rfl)

/-- The defining property of the comparison map. -/
private theorem sesq_compareForms (B : BilinForm ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (x y : V) :
    H (compareForms B H hdef x) y = B x y := by
  rw [compareForms_apply, sesq_apply_symm_apply]

/-- The comparison map is injective when `B` is nondegenerate: a vector it kills is
`B`-orthogonal to everything. -/
private theorem compareForms_ne_zero {B : BilinForm ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}
    (hBnd : B.Nondegenerate) (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) {x : V} (hx : x ≠ 0) :
    compareForms B H hdef x ≠ 0 := by
  intro hzero
  refine hx (hBnd.1 x fun y => ?_)
  rw [← sesq_compareForms B H hdef x y, hzero, map_zero, LinearMap.zero_apply]

/-- The square of the comparison map is `ℂ`-linear: the two conjugations cancel, which is what
composing two `starRingEnd ℂ`-semilinear maps records. -/
private noncomputable def compareFormsSq (B : BilinForm ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) : V →ₗ[ℂ] V :=
  (compareForms B H hdef).comp (compareForms B H hdef)

private theorem compareFormsSq_apply (B : BilinForm ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (x : V) :
    compareFormsSq B H hdef x = compareForms B H hdef (compareForms B H hdef x) := (rfl)

end Inverting

/-! ### Equivariance and the Schur scalar -/

section Equivariance

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {B : BilinForm ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} [FiniteDimensional ℂ V]

/-- The comparison map of two invariant forms commutes with the action: both sides pair identically
against every vector, and a positive definite form separates vectors. -/
private theorem compareForms_apply_rep (hBinv : IsInvariantForm ρ B)
    (hHinv : IsInvariantSesqForm ρ H) (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (g : G) (x : V) :
    compareForms B H hdef (ρ g x) = ρ g (compareForms B H hdef x) := by
  refine eq_of_forall_sesq_eq H hdef fun y => ?_
  calc H (compareForms B H hdef (ρ g x)) y
      = B (ρ g x) y := sesq_compareForms B H hdef (ρ g x) y
    _ = B (ρ g x) (ρ g (ρ g⁻¹ y)) := by rw [ρ.self_inv_apply]
    _ = B x (ρ g⁻¹ y) := hBinv.apply g x (ρ g⁻¹ y)
    _ = H (compareForms B H hdef x) (ρ g⁻¹ y) := (sesq_compareForms B H hdef x (ρ g⁻¹ y)).symm
    _ = H (ρ g (compareForms B H hdef x)) (ρ g (ρ g⁻¹ y)) :=
        (hHinv.apply g (compareForms B H hdef x) (ρ g⁻¹ y)).symm
    _ = H (ρ g (compareForms B H hdef x)) y := by rw [ρ.self_inv_apply]

variable [ρ.IsIrreducible]

/-- **Schur's lemma applied to the square of the comparison map.**  It is a `ℂ`-linear
self-intertwiner of an irreducible representation over the algebraically closed `ℂ`, hence a
scalar. -/
private theorem exists_compareFormsSq_eq_smul (hBinv : IsInvariantForm ρ B)
    (hHinv : IsInvariantSesqForm ρ H) (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ c : ℂ, ∀ x : V, compareFormsSq B H hdef x = c • x := by
  have hφ : ∀ (g : G) (v : V), compareFormsSq B H hdef (ρ g v) = ρ g (compareFormsSq B H hdef v) :=
    fun g v => by
      rw [compareFormsSq_apply, compareFormsSq_apply, compareForms_apply_rep hBinv hHinv hdef,
        compareForms_apply_rep hBinv hHinv hdef]
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 ((compareFormsSq B H hdef).intertwiningMap_of_isIntertwiningMap ρ ρ hφ)
  refine ⟨c, fun x => ?_⟩
  simpa using (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc).symm

/-- **The Schur scalar of the squared comparison map is a positive real.**  Symmetry of `B` and
Hermitian symmetry of `H` turn `H (J x) (J x)` into `conj c` times `H x x`, and both self-pairings
are positive because `H` is nonnegative and definite off the origin and `J` is injective. -/
private theorem exists_compareFormsSq_eq_real_smul (hBinv : IsInvariantForm ρ B) (hBsymm : B.IsSymm)
    (hBnd : B.Nondegenerate) (hHinv : IsInvariantSesqForm ρ H) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ x : V, compareFormsSq B H hdef x = (t : ℂ) • x := by
  have : Nontrivial V := IsIrreducible.nontrivial ‹ρ.IsIrreducible›
  obtain ⟨c, hc⟩ := exists_compareFormsSq_eq_smul hBinv hHinv hdef
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hpos : ∀ y : V, y ≠ 0 → 0 < H y y := fun y hy =>
    lt_of_le_of_ne (hHnonneg.nonneg y) (Ne.symm (hdef y hy))
  have hJx : compareForms B H hdef x ≠ 0 := compareForms_ne_zero hBnd hdef hx
  -- `H (J x) (J x) = conj c * H x x`, by symmetry of `B` and Hermitian symmetry of `H`.
  have hkey : H (compareForms B H hdef x) (compareForms B H hdef x)
      = (starRingEnd ℂ) c * H x x := by
    calc H (compareForms B H hdef x) (compareForms B H hdef x)
        = B x (compareForms B H hdef x) :=
          sesq_compareForms B H hdef x (compareForms B H hdef x)
      _ = B (compareForms B H hdef x) x := hBsymm.eq x (compareForms B H hdef x)
      _ = H (compareForms B H hdef (compareForms B H hdef x)) x :=
          (sesq_compareForms B H hdef (compareForms B H hdef x) x).symm
      _ = H (c • x) x := by rw [← compareFormsSq_apply, hc]
      _ = (starRingEnd ℂ) c * H x x := by simp
  -- Both self-pairings are positive reals, so `conj c`, hence `c`, is a positive real.
  have hrC : H x x = ((H x x).re : ℂ) := by
    refine Complex.ext rfl ?_
    simpa using ((Complex.lt_def.mp (hpos x hx)).2).symm
  have hsC : H (compareForms B H hdef x) (compareForms B H hdef x)
      = ((H (compareForms B H hdef x) (compareForms B H hdef x)).re : ℂ) := by
    refine Complex.ext rfl ?_
    simpa using ((Complex.lt_def.mp (hpos _ hJx)).2).symm
  have hrpos : 0 < (H x x).re := (Complex.lt_def.mp (hpos x hx)).1
  have hspos : 0 < (H (compareForms B H hdef x) (compareForms B H hdef x)).re :=
    (Complex.lt_def.mp (hpos _ hJx)).1
  have hrne : ((H x x).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hconj : (starRingEnd ℂ) c
      = (((H (compareForms B H hdef x) (compareForms B H hdef x)).re / (H x x).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff hrne, ← hrC, ← hsC, hkey]
  refine ⟨_, div_pos hspos hrpos, fun y => ?_⟩
  rw [hc y, ← Complex.conj_conj c, hconj, Complex.conj_ofReal]

end Equivariance

/-! ### The real structure -/

section RealStructure

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  [FiniteDimensional ℂ V] [ρ.IsIrreducible]

/-- **An invariant symmetric form and an invariant Hermitian form produce a real structure.**  The
conjugate-linear comparison map `J` of the two forms commutes with the action, and its square is a
positive real scalar by Schur's lemma; rescaling `J` by the inverse square root of that scalar --
a real scalar, so conjugate-linearity is untouched -- makes it an involution. -/
theorem exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm {B : BilinForm ℂ V}
    {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hBinv : IsInvariantForm ρ B) (hBsymm : B.IsSymm)
    (hBnd : B.Nondegenerate) (hHinv : IsInvariantSesqForm ρ H) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ K : V →ₛₗ[starRingEnd ℂ] V, IsRealStructure ρ K := by
  obtain ⟨t, htpos, ht⟩ :=
    exists_compareFormsSq_eq_real_smul hBinv hBsymm hBnd hHinv hHnonneg hdef
  -- The scaling factor, stated once over `ℂ`: this is the only place the proof crosses the
  -- `ℝ`-to-`ℂ` coercion, so the map equality below stays a plain scalar computation.
  have hsq : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (t : ℂ) = 1 := by
    have hreal : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt htpos.le, inv_mul_cancel₀ htpos.ne']
    exact_mod_cast hreal
  refine ⟨(((Real.sqrt t)⁻¹ : ℝ) : ℂ) • compareForms B H hdef, fun x => ?_, fun g v => ?_⟩
  · simp only [LinearMap.smul_apply, map_smulₛₗ, Complex.conj_ofReal, smul_smul,
      ← compareFormsSq_apply]
    rw [ht x, smul_smul, hsq, one_smul]
  · simp only [LinearMap.smul_apply, compareForms_apply_rep hBinv hHinv hdef, map_smul]

end RealStructure

/-! ### The balanced Hermitian form of a conjugate-linear map -/

section Balanced

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The **balanced** form of a sesquilinear form `H` against a conjugate-linear map `K`:
`x, y ↦ H x y + conj (H (K x) (K y))`.  Each argument of the second summand picks up a conjugation
from `K`, and the outer conjugation restores the shape of a sesquilinear form, conjugate-linear in
the first argument and linear in the second.  Adding it to `H` is what forces the compatibility
`balance H K (K x) (K y) = conj (balance H K x y)` when `K` is an involution. -/
private noncomputable def balance (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (K : V →ₛₗ[starRingEnd ℂ] V) :
    V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => H x y + (starRingEnd ℂ) (H (K x) (K y))
      map_add' := fun y z => by simp only [map_add]; ring
      map_smul' := fun c y => by
        simp only [map_smulₛₗ, RingHom.id_apply, smul_eq_mul, map_mul, Complex.conj_conj]
        ring }
  map_add' x y := by
    ext z
    simp only [map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' c x := by
    ext z
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring

private theorem balance_apply (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (K : V →ₛₗ[starRingEnd ℂ] V) (x y : V) :
    balance H K x y = H x y + (starRingEnd ℂ) (H (K x) (K y)) := (rfl)

/-- **The balanced form is compatible with the involution it was balanced against**: replacing both
arguments by their `K`-images conjugates the value.  This is the only property of `balance` that
`H` alone does not already have, and the whole point of the construction. -/
private theorem balance_map_map {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {K : V →ₛₗ[starRingEnd ℂ] V}
    (hK : Function.Involutive ⇑K) (x y : V) :
    balance H K (K x) (K y) = (starRingEnd ℂ) (balance H K x y) := by
  rw [balance_apply, balance_apply, hK x, hK y, map_add, Complex.conj_conj, add_comm]

/-- The balanced form is Hermitian if `H` is. -/
private theorem isSymm_balance {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsSymm)
    (K : V →ₛₗ[starRingEnd ℂ] V) : (balance H K).IsSymm where
  eq x y := by
    rw [balance_apply, balance_apply, map_add, Complex.conj_conj, hH.eq x y,
      hH.eq (K y) (K x)]

/-- A nonnegative complex number has vanishing imaginary part, so conjugation fixes it. -/
private theorem conj_eq_self_of_nonneg {z : ℂ} (hz : 0 ≤ z) : (starRingEnd ℂ) z = z :=
  Complex.conj_eq_iff_im.mpr (Complex.nonneg_iff.mp hz).2.symm

/-- The balanced form is nonnegative if `H` is: both summands are, the second because conjugation
fixes a nonnegative complex number. -/
private theorem isNonneg_balance {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsNonneg)
    (K : V →ₛₗ[starRingEnd ℂ] V) : (balance H K).IsNonneg where
  nonneg x := by
    rw [balance_apply, conj_eq_self_of_nonneg (hH.nonneg (K x))]
    exact add_nonneg (hH.nonneg x) (hH.nonneg (K x))

/-- The balanced form is definite off the origin if `H` is: the first summand is already nonzero
and the second is nonnegative. -/
private theorem balance_apply_self_ne_zero {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (K : V →ₛₗ[starRingEnd ℂ] V) {x : V} (hx : x ≠ 0) :
    balance H K x x ≠ 0 := by
  rw [balance_apply, conj_eq_self_of_nonneg (hH.nonneg (K x))]
  exact (add_pos_of_pos_of_nonneg
    (lt_of_le_of_ne (hH.nonneg x) (Ne.symm (hdef x hx))) (hH.nonneg (K x))).ne'

end Balanced

/-! ### An invariant symmetric form out of a real structure -/

section OfRealStructure

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- The balanced form of an invariant form against an equivariant map is invariant. -/
private theorem isInvariantSesqForm_balance {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}
    {K : V →ₛₗ[starRingEnd ℂ] V} (hHinv : IsInvariantSesqForm ρ H)
    (hK : ∀ (g : G) (v : V), K (ρ g v) = ρ g (K v)) : IsInvariantSesqForm ρ (balance H K) :=
  isInvariantSesqForm_iff.mpr fun g x y => by
    rw [balance_apply, balance_apply, hHinv.apply g x y, hK g x, hK g y, hHinv.apply g (K x) (K y)]

/-- **A real structure produces a nondegenerate invariant symmetric form.**  Balancing the given
invariant Hermitian form `H` against the real structure `K` makes it satisfy
`H (K x) (K y) = conj (H x y)`, and then `B x y = H (K x) y` is a bilinear form -- the two
conjugations, one from `K` and one from the first argument of `H`, cancel -- which is invariant
because both `H` and `K` are, symmetric by the compatibility, and nondegenerate because `H` is
definite and `K` is bijective.

Neither irreducibility nor finite dimensionality is used: this is the elementary direction of the
correspondence, the other being
`Representation.exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm`. -/
theorem exists_isInvariantForm_isSymm_nondegenerate_of_isRealStructure
    {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {K : V →ₛₗ[starRingEnd ℂ] V} (hK : IsRealStructure ρ K)
    (hHinv : IsInvariantSesqForm ρ H) (hHsymm : H.IsSymm) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ B : BilinForm ℂ V, IsInvariantForm ρ B ∧ B.IsSymm ∧ B.Nondegenerate := by
  -- The candidate form, `B x y = balance H K (K x) y`; the composite is honestly `ℂ`-bilinear,
  -- the conjugation `K` carries cancelling the one the first argument of a sesquilinear form does.
  refine ⟨(balance H K).comp K, ?_, ?_, ?_, ?_⟩
  · exact isInvariantForm_iff.mpr fun g x y => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hK.isIntertwining g x,
        (isInvariantSesqForm_balance hHinv hK.isIntertwining).apply g (K x) y]
  · -- Symmetry: move `K` from one argument to the other with `hK.involutive` and the
    -- compatibility, then read off the Hermitian symmetry of the balanced form.
    refine ⟨fun x y => ?_⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hK.involutive y,
      balance_map_map hK.involutive x (K y), ← (isSymm_balance hHsymm K).eq (K y) x,
      Complex.conj_conj, hK.involutive y]
  · -- Left separation: a vector killed by `B` has `balance H K (K x) (K x) = 0`.
    intro x hx
    by_contra hx0
    have hKx : K x ≠ 0 := fun h =>
      hx0 (hK.involutive.injective (h.trans (map_zero K).symm))
    exact balance_apply_self_ne_zero hHnonneg hdef K hKx (by simpa using hx (K x))
  · -- Right separation: pairing against `K y` gives `balance H K y y = 0`.
    intro y hy
    by_contra hy0
    refine balance_apply_self_ne_zero hHnonneg hdef K hy0 ?_
    have h := hy (K y)
    rwa [LinearMap.comp_apply, hK.involutive y] at h

variable [FiniteDimensional ℂ V] [ρ.IsIrreducible]

/-- **Against a positive definite invariant Hermitian form, a real structure is the same datum as a
nondegenerate invariant symmetric form.**  Both directions are proved above; the Hermitian form is
the fixed background datum, supplied by summation over a finite group or by Haar averaging over a
compact one. -/
theorem exists_isRealStructure_iff {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hHinv : IsInvariantSesqForm ρ H)
    (hHsymm : H.IsSymm) (hHnonneg : H.IsNonneg) (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    (∃ K : V →ₛₗ[starRingEnd ℂ] V, IsRealStructure ρ K) ↔
      ∃ B : BilinForm ℂ V, IsInvariantForm ρ B ∧ B.IsSymm ∧ B.Nondegenerate :=
  ⟨fun ⟨_, hK⟩ =>
      exists_isInvariantForm_isSymm_nondegenerate_of_isRealStructure hK hHinv hHsymm hHnonneg hdef,
    fun ⟨_, hBinv, hBsymm, hBnd⟩ =>
      exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm hBinv hBsymm hBnd hHinv
        hHnonneg hdef⟩

end OfRealStructure

end Representation
