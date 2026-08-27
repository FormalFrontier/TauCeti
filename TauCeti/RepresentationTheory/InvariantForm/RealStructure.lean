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
# A real structure out of an invariant symmetric form and an invariant Hermitian form

An invariant *symmetric bilinear* form `B` on an irreducible complex representation is strictly
weaker than a real form.  Together with a positive definite invariant *Hermitian* form `H`,
however, it produces one: this file builds a `Representation.IsRealStructure` -- a conjugate-linear
involution of `V` commuting with the action -- out of the two forms.

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

## Main results

* `Representation.exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm`: **an
  irreducible representation carrying a nondegenerate invariant symmetric form and a nonnegative
  invariant Hermitian form that is definite off the origin has a real structure.**

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7: the passage from a "compatible Hermitian form" to the real structure that the
  realizability target `frobeniusSchurIndicatorRep_eq_one_realizable` is read off from.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
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

end Representation
