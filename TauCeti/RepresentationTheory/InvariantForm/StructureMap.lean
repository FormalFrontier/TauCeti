/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.LinearAlgebra.Complex.SesquilinearForm
public import TauCeti.RepresentationTheory.InvariantForm.Hermitian
public import TauCeti.RepresentationTheory.QuaternionicStructure
public import TauCeti.RepresentationTheory.RealForm

/-!
# Structure maps and invariant bilinear forms, against a fixed invariant Hermitian form

An invariant *bilinear* form on an irreducible complex representation is strictly weaker than a
structure map.  Together with a positive definite invariant *Hermitian* form `H`, however, it
produces one: this file builds a conjugate-linear equivariant map of `V` out of the two forms, and
goes back again, so that against a fixed `H` one exists exactly when the other does.

Which structure map comes out is decided by the **flip rule** of the bilinear form.  Writing
`B x y = ε * B y x` -- with `ε = 1` for a symmetric form and `ε = -1` for an alternating one -- the
map `J` produced squares to `ε`:

* a symmetric `B` gives a conjugate-linear involution, a `Representation.IsRealStructure`,
  whose real points are a real form;
* an alternating `B` gives a conjugate-linear `J` with `J (J x) = -x`, a
  `Representation.IsQuaternionicStructure`, whose fixed points are only `0`.

Both cases are proved once here, for a real sign `ε` with `ε * ε = 1`, and specialized twice.

Comparing the two forms produces a conjugate-linear map `J` of `V` determined by
`H (J x) y = B x y`.  It exists because `H`, read as a map `V → V*`, is injective by definiteness
and hence bijective -- as an `ℝ`-linear map between two spaces of the same finite real dimension --
so it can be inverted on the `ℂ`-linear map `x ↦ B x`.  Invariance of both forms makes `J` commute
with the action, so `J ∘ J` is a `ℂ`-linear self-intertwiner, and Schur's lemma over the
algebraically closed `ℂ` forces `J ∘ J = c • id`.  The flip rule of `B` and the Hermitian symmetry
of `H` then evaluate `c`:

`H (J x) (J x) = B x (J x) = ε * B (J x) x = ε * H (J (J x)) x = ε * conj c * H x x`,

so `ε * c` is the ratio of two positive reals.  Rescaling `J` by the inverse square root of that
ratio -- a *real* scalar, so conjugate-linearity survives -- makes `J ∘ J` equal to `ε`: a real
structure when `ε = 1`, a quaternionic one when `ε = -1`.

Only the two forms are needed, so nothing here asks for a finite group -- nor even for a group,
since a definite invariant Hermitian form on a finite-dimensional space already makes each action
map bijective, which is all the equivariance argument would use an inverse for.  Producing the
invariant Hermitian form is where finiteness enters, in
`TauCeti/RepresentationTheory/InvariantForm/Hermitian.lean`, and the Frobenius-Schur criteria this
feeds are in `TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Realizability.lean` and
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/StructureMap.lean`.

The **converse** passage, from a structure map `K` back to an invariant bilinear form, is the
second half of the file, and it needs neither irreducibility nor finite dimensionality.  The naive
guess `B x y = H (K x) y` is bilinear, invariant and nondegenerate for free, but it obeys a flip
rule only if `H` is compatible with `K` in the sense `H (K x) (K y) = conj (H x y)`, which an
arbitrary invariant `H` need not be.  Replacing `H` by the **balanced** form
`LinearMap.balance H K x y = H x y + conj (H (K x) (K y))` of
`TauCeti/LinearAlgebra/Complex/SesquilinearForm.lean` -- still invariant, Hermitian and positive
definite, since `K` is bijective -- makes it compatible, and then `B x y = H (K x) y` flips by the
sign that `K ∘ K` carries: symmetric for a real structure, alternating for a quaternionic one.
Against a fixed `H` the two directions assemble into the existence criteria
`Representation.exists_isRealStructure_iff` and
`Representation.exists_isQuaternionicStructure_iff`, which are what turn the Frobenius-Schur values
`1` and `-1` into structure maps whenever a positive definite invariant Hermitian form is
available -- by Haar averaging for a compact group as much as by summation for a finite one.

## Main results

* `Representation.exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm`: **an
  irreducible representation carrying a nondegenerate invariant symmetric form and a nonnegative
  invariant Hermitian form that is definite off the origin has a real structure.**
* `Representation.exists_isQuaternionicStructure_of_isInvariantForm_of_isInvariantSesqForm`: **the
  same with an alternating form in place of a symmetric one produces a quaternionic structure.**
* `Representation.exists_isInvariantForm_isSymm_nondegenerate_of_isRealStructure`: **a real
  structure, together with a positive definite invariant Hermitian form, produces a nondegenerate
  invariant symmetric form.**
* `Representation.exists_isInvariantForm_isAlt_nondegenerate_of_isQuaternionicStructure`: **a
  quaternionic structure produces a nondegenerate invariant alternating form the same way.**
* `Representation.isInvariantSesqForm_balance`: **balancing an invariant sesquilinear form
  against an equivariant map leaves it invariant**, which is what makes the balanced form of
  `TauCeti/LinearAlgebra/Complex/SesquilinearForm.lean` usable on a representation.
* `Representation.exists_isRealStructure_iff` and
  `Representation.exists_isQuaternionicStructure_iff`: against a positive definite invariant
  Hermitian form, an irreducible finite-dimensional representation has a real, respectively a
  quaternionic, structure exactly when it carries a nondegenerate invariant symmetric,
  respectively alternating, form.

## Implementation notes

The two structure-map predicates are defined away from this file, so that stating one costs none of
the machinery used to produce it: `Representation.IsRealStructure` in
`TauCeti/RepresentationTheory/RealForm.lean`, beside the real-form theory that consumes it, and
`Representation.IsQuaternionicStructure` in
`TauCeti/RepresentationTheory/QuaternionicStructure.lean`, on its own -- nothing of that real-form
theory attaches to it, since the fixed points of a `J` with `J (J v) = -v` are `0`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §6.
-/

public section

open Module (Dual)

open scoped ComplexOrder

open LinearMap (BilinForm balance balance_apply balance_map_map isSymm_balance
  balance_apply_self_ne_zero)

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

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {B : BilinForm ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} [FiniteDimensional ℂ V]

/-- The comparison map of two invariant forms commutes with the action: both sides pair identically
against every vector, and a positive definite form separates vectors.  The second argument is
written as `ρ g z`, which is no loss because the action is surjective. -/
private theorem compareForms_apply_rep (hBinv : IsInvariantForm ρ B)
    (hHinv : IsInvariantSesqForm ρ H) (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (g : G) (x : V) :
    compareForms B H hdef (ρ g x) = ρ g (compareForms B H hdef x) := by
  refine eq_of_forall_sesq_eq H hdef fun y => ?_
  obtain ⟨z, rfl⟩ := hHinv.surjective_of_apply_self_ne_zero hdef g y
  calc H (compareForms B H hdef (ρ g x)) (ρ g z)
      = B (ρ g x) (ρ g z) := sesq_compareForms B H hdef (ρ g x) (ρ g z)
    _ = B x z := hBinv.apply g x z
    _ = H (compareForms B H hdef x) z := (sesq_compareForms B H hdef x z).symm
    _ = H (ρ g (compareForms B H hdef x)) (ρ g z) :=
        (hHinv.apply g (compareForms B H hdef x) z).symm

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

/-- **The Schur scalar of the squared comparison map is the flip sign times a positive real.**
The flip rule `B x y = ε * B y x` and Hermitian symmetry of `H` turn `H (J x) (J x)` into
`ε * conj c` times `H x x`, and both self-pairings are positive because `H` is nonnegative and
definite off the origin and `J` is injective; `ε * ε = 1` then reads `c` off as `ε` times their
ratio.

The two cases used below are a symmetric `B`, where `ε = 1`, and an alternating one, where
`ε = -1`. -/
private theorem exists_compareFormsSq_eq_sign_smul {ε : ℝ} (hε : ε * ε = 1)
    (hBinv : IsInvariantForm ρ B) (hflip : ∀ x y : V, B x y = (ε : ℂ) * B y x)
    (hBnd : B.Nondegenerate) (hHinv : IsInvariantSesqForm ρ H) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ x : V, compareFormsSq B H hdef x = ((ε * t : ℝ) : ℂ) • x := by
  have : Nontrivial V := IsIrreducible.nontrivial ‹ρ.IsIrreducible›
  have hεC : (ε : ℂ) * (ε : ℂ) = 1 := by exact_mod_cast hε
  obtain ⟨c, hc⟩ := exists_compareFormsSq_eq_smul hBinv hHinv hdef
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hpos : ∀ y : V, y ≠ 0 → 0 < H y y := fun y hy =>
    lt_of_le_of_ne (hHnonneg.nonneg y) (Ne.symm (hdef y hy))
  have hJx : compareForms B H hdef x ≠ 0 := compareForms_ne_zero hBnd hdef hx
  -- `H (J x) (J x) = ε * (conj c * H x x)`, by the flip rule of `B` and Hermitian symmetry of `H`.
  have hkey : H (compareForms B H hdef x) (compareForms B H hdef x)
      = (ε : ℂ) * ((starRingEnd ℂ) c * H x x) := by
    calc H (compareForms B H hdef x) (compareForms B H hdef x)
        = B x (compareForms B H hdef x) :=
          sesq_compareForms B H hdef x (compareForms B H hdef x)
      _ = (ε : ℂ) * B (compareForms B H hdef x) x := hflip x (compareForms B H hdef x)
      _ = (ε : ℂ) * H (compareForms B H hdef (compareForms B H hdef x)) x := by
          rw [sesq_compareForms B H hdef (compareForms B H hdef x) x]
      _ = (ε : ℂ) * H (c • x) x := by rw [← compareFormsSq_apply, hc]
      _ = (ε : ℂ) * ((starRingEnd ℂ) c * H x x) := by simp
  -- Both self-pairings are positive reals, so `ε * conj c`, hence `c`, is `ε` times a positive one.
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
      = ((ε * ((H (compareForms B H hdef x) (compareForms B H hdef x)).re / (H x x).re) : ℝ)
          : ℂ) := by
    -- Recast `hkey` once against the two real parts; from here on nothing about the forms is
    -- used, only the scalar identity `s = ε * (conj c * r)` together with `ε * ε = 1` and `r ≠ 0`.
    have hkeyC : ((H (compareForms B H hdef x) (compareForms B H hdef x)).re : ℂ)
        = (ε : ℂ) * ((starRingEnd ℂ) c * ((H x x).re : ℂ)) := by
      rw [← hsC, ← hrC]; exact hkey
    push_cast
    field_simp
    linear_combination (-(ε : ℂ)) * hkeyC - ((starRingEnd ℂ) c * ((H x x).re : ℂ)) * hεC
  refine ⟨_, div_pos hspos hrpos, fun y => ?_⟩
  rw [hc y, ← Complex.conj_conj c, hconj, Complex.conj_ofReal]

end Equivariance

/-! ### The structure maps -/

section StructureMap

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  [FiniteDimensional ℂ V] [ρ.IsIrreducible]

/-- **An invariant bilinear form obeying a flip rule, together with an invariant Hermitian form,
produces a conjugate-linear equivariant map squaring to the flip sign.**  The comparison map `J` of
the two forms commutes with the action, and its square is `ε` times a positive real scalar by
Schur's lemma; rescaling `J` by the inverse square root of that scalar -- a real scalar, so
conjugate-linearity is untouched -- leaves the square equal to `ε`. -/
private theorem exists_conjLinear_sq_eq_sign_smul {B : BilinForm ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}
    {ε : ℝ} (hε : ε * ε = 1) (hBinv : IsInvariantForm ρ B)
    (hflip : ∀ x y : V, B x y = (ε : ℂ) * B y x) (hBnd : B.Nondegenerate)
    (hHinv : IsInvariantSesqForm ρ H) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ J : V →ₛₗ[starRingEnd ℂ] V, (∀ x : V, J (J x) = (ε : ℂ) • x) ∧
      ∀ (g : G) (x : V), J (ρ g x) = ρ g (J x) := by
  obtain ⟨t, htpos, ht⟩ :=
    exists_compareFormsSq_eq_sign_smul hε hBinv hflip hBnd hHinv hHnonneg hdef
  -- The scaling factor, stated once over `ℂ`: this is the only place the proof crosses the
  -- `ℝ`-to-`ℂ` coercion, so the map equality below stays a plain scalar computation.
  have hsq : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * ((ε * t : ℝ) : ℂ)
      = (ε : ℂ) := by
    -- Over `ℝ` the scaling factor is `t⁻¹ * (ε * t)`, which is `ε` because `t` is positive.
    have hreal : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * (ε * t) = ε := by
      rw [← mul_inv, Real.mul_self_sqrt htpos.le]
      field_simp
    exact_mod_cast hreal
  refine ⟨(((Real.sqrt t)⁻¹ : ℝ) : ℂ) • compareForms B H hdef, fun x => ?_, fun g v => ?_⟩
  · simp only [LinearMap.smul_apply, map_smulₛₗ, Complex.conj_ofReal, smul_smul,
      ← compareFormsSq_apply]
    rw [ht x, smul_smul, hsq]
  · simp only [LinearMap.smul_apply, compareForms_apply_rep hBinv hHinv hdef, map_smul]

/-- **An invariant symmetric form and an invariant Hermitian form produce a real structure.**  This
is the flip sign `ε = 1` of the construction: the rescaled comparison map of the two forms is a
conjugate-linear involution commuting with the action. -/
theorem exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm {B : BilinForm ℂ V}
    {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hBinv : IsInvariantForm ρ B) (hBsymm : B.IsSymm)
    (hBnd : B.Nondegenerate) (hHinv : IsInvariantSesqForm ρ H) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ K : V →ₛₗ[starRingEnd ℂ] V, IsRealStructure ρ K := by
  obtain ⟨K, hKsq, hKint⟩ := exists_conjLinear_sq_eq_sign_smul (ε := 1) (one_mul 1) hBinv
    (fun x y => by rw [Complex.ofReal_one, one_mul]; exact hBsymm.eq x y) hBnd hHinv hHnonneg hdef
  exact ⟨K, fun x => by simpa using hKsq x, hKint⟩

/-- **An invariant alternating form and an invariant Hermitian form produce a quaternionic
structure.**  This is the flip sign `ε = -1` of the same construction, the only change being that
the Schur scalar of the squared comparison map comes out negative, so that rescaling leaves a
conjugate-linear `J` with `J (J x) = -x` rather than an involution. -/
theorem exists_isQuaternionicStructure_of_isInvariantForm_of_isInvariantSesqForm
    {B : BilinForm ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hBinv : IsInvariantForm ρ B) (hBalt : B.IsAlt)
    (hBnd : B.Nondegenerate) (hHinv : IsInvariantSesqForm ρ H) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ J : V →ₛₗ[starRingEnd ℂ] V, IsQuaternionicStructure ρ J := by
  obtain ⟨J, hJsq, hJint⟩ := exists_conjLinear_sq_eq_sign_smul (ε := -1) (by norm_num) hBinv
    (fun x y => by
      rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul]
      exact (hBalt.neg_eq y x).symm)
    hBnd hHinv hHnonneg hdef
  exact ⟨J, fun x => by simpa using hJsq x, hJint⟩

end StructureMap

/-! ### An invariant bilinear form out of a structure map -/

section OfStructureMap

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- **The balanced form of an invariant sesquilinear form against an equivariant map is
invariant.**  Both summands of `LinearMap.balance H K` are, the second because `K` commutes with
the action.  This is the only interaction between balancing and invariance that the passage from a
structure map to an invariant bilinear form uses. -/
theorem isInvariantSesqForm_balance {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}
    {K : V →ₛₗ[starRingEnd ℂ] V} (hHinv : IsInvariantSesqForm ρ H)
    (hK : ∀ (g : G) (v : V), K (ρ g v) = ρ g (K v)) : IsInvariantSesqForm ρ (balance H K) :=
  isInvariantSesqForm_iff.mpr fun g x y => by
    rw [balance_apply, balance_apply, hHinv.apply g x y, hK g x, hK g y, hHinv.apply g (K x) (K y)]

/-- **A structure map produces a nondegenerate invariant bilinear form flipping by the sign of its
square.**  Balancing the given invariant Hermitian form `H` against the structure map `K` makes it
satisfy `H (K x) (K y) = conj (H x y)`, and then `B x y = H (K x) y` is a bilinear form -- the two
conjugations, one from `K` and one from the first argument of `H`, cancel -- which is invariant
because both `H` and `K` are, obeys the flip rule `B x y = ε * B y x` by that compatibility, and is
nondegenerate because `H` is definite and `K` is injective.

Neither irreducibility nor finite dimensionality is used: this is the elementary direction of the
correspondence. -/
private theorem exists_isInvariantForm_flip_of_sq_eq_smul {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}
    {K : V →ₛₗ[starRingEnd ℂ] V} {ε : ℝ} (hε : ε * ε = 1)
    (hKsq : ∀ x : V, K (K x) = (ε : ℂ) • x)
    (hKint : ∀ (g : G) (v : V), K (ρ g v) = ρ g (K v)) (hHinv : IsInvariantSesqForm ρ H)
    (hHsymm : H.IsSymm) (hHnonneg : H.IsNonneg) (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ B : BilinForm ℂ V, IsInvariantForm ρ B ∧ (∀ x y : V, B x y = (ε : ℂ) * B y x) ∧
      B.Nondegenerate := by
  have hεC : (ε : ℂ) * (ε : ℂ) = 1 := by exact_mod_cast hε
  have hεstar : star ((ε : ℂ)) * (ε : ℂ) = 1 := by
    rw [← starRingEnd_apply, Complex.conj_ofReal]
    exact hεC
  have hεne : (ε : ℂ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hεC
    exact zero_ne_one hεC
  have hKne : ∀ {x : V}, x ≠ 0 → K x ≠ 0 := by
    intro x hx h0
    refine hx ?_
    have hsq := hKsq x
    rw [h0, map_zero] at hsq
    exact (smul_eq_zero.mp hsq.symm).resolve_left hεne
  -- The candidate form, `B x y = balance H K (K x) y`; the composite is honestly `ℂ`-bilinear,
  -- the conjugation `K` carries cancelling the one the first argument of a sesquilinear form does.
  refine ⟨(balance H K).comp K, ?_, ?_, ?_, ?_⟩
  · exact isInvariantForm_iff.mpr fun g x y => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hKint g x,
        (isInvariantSesqForm_balance hHinv hKint).apply g (K x) y]
  · -- The flip rule: move `K` from one argument to the other with `hKsq` and the compatibility,
    -- reading the Hermitian symmetry of the balanced form off in between.
    intro x y
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    calc balance H K (K x) y
        = (starRingEnd ℂ) (balance H K y (K x)) := ((isSymm_balance hHsymm K).eq y (K x)).symm
      _ = (starRingEnd ℂ) (balance H K ((ε : ℂ) • K (K y)) (K x)) := by
            rw [hKsq y, smul_smul, hεC, one_smul]
      _ = (starRingEnd ℂ) ((ε : ℂ) * (starRingEnd ℂ) (balance H K (K y) x)) := by
            rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal,
              balance_map_map hεstar hKsq (K y) x]
      _ = (ε : ℂ) * balance H K (K y) x := by
            rw [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  · -- Left separation: a vector killed by `B` has `balance H K (K x) (K x) = 0`.
    intro x hx
    by_contra hx0
    exact balance_apply_self_ne_zero hHnonneg hdef K (hKne hx0) (by simpa using hx (K x))
  · -- Right separation: pairing against `K y` gives `balance H K y y = 0`.
    intro y hy
    by_contra hy0
    refine balance_apply_self_ne_zero hHnonneg hdef K hy0 ?_
    have h := hy (K y)
    rw [LinearMap.comp_apply, hKsq y, map_smulₛₗ, LinearMap.smul_apply, Complex.conj_ofReal,
      smul_eq_mul, mul_eq_zero] at h
    exact h.resolve_left hεne

/-- **A real structure produces a nondegenerate invariant symmetric form.**  This is the flip sign
`ε = 1` of the construction: the balanced form of `H` against the involution `K` is compatible with
it, and `B x y = H (K x) y` is then symmetric. -/
theorem exists_isInvariantForm_isSymm_nondegenerate_of_isRealStructure
    {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {K : V →ₛₗ[starRingEnd ℂ] V} (hK : IsRealStructure ρ K)
    (hHinv : IsInvariantSesqForm ρ H) (hHsymm : H.IsSymm) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ B : BilinForm ℂ V, IsInvariantForm ρ B ∧ B.IsSymm ∧ B.Nondegenerate := by
  obtain ⟨B, hBinv, hflip, hBnd⟩ := exists_isInvariantForm_flip_of_sq_eq_smul (ε := 1) (one_mul 1)
    (fun x => by simpa using hK.involutive x) hK.isIntertwining hHinv hHsymm hHnonneg hdef
  exact ⟨B, hBinv, ⟨fun x y => by simpa using hflip x y⟩, hBnd⟩

/-- **A quaternionic structure produces a nondegenerate invariant alternating form.**  This is the
flip sign `ε = -1` of the same construction: the form built from `J` obeys `B x y = -B y x`, which
over `ℂ` is alternation. -/
theorem exists_isInvariantForm_isAlt_nondegenerate_of_isQuaternionicStructure
    {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {J : V →ₛₗ[starRingEnd ℂ] V} (hJ : IsQuaternionicStructure ρ J)
    (hHinv : IsInvariantSesqForm ρ H) (hHsymm : H.IsSymm) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    ∃ B : BilinForm ℂ V, IsInvariantForm ρ B ∧ B.IsAlt ∧ B.Nondegenerate := by
  obtain ⟨B, hBinv, hflip, hBnd⟩ :=
    exists_isInvariantForm_flip_of_sq_eq_smul (ε := -1) (by norm_num)
      (fun x => by simpa using hJ.sq_eq_neg x) hJ.isIntertwining hHinv hHsymm hHnonneg hdef
  refine ⟨B, hBinv, ?_, hBnd⟩
  intro x
  have h : B x x = -B x x := by simpa using hflip x x
  linear_combination h / 2

end OfStructureMap

/-! ### Each datum exists exactly when the other does -/

section Equivalence

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  [FiniteDimensional ℂ V] [ρ.IsIrreducible]

/-- **Against a positive definite invariant Hermitian form, a real structure exists exactly when a
nondegenerate invariant symmetric form does.**  Both directions are proved above; the Hermitian
form is the fixed background datum, supplied by summation over a finite group or by Haar averaging
over a compact one.  This is an equivalence of the two existence statements, not of the two data:
each direction produces *some* witness from a given one, and no inverse pair of constructions is
claimed. -/
theorem exists_isRealStructure_iff {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hHinv : IsInvariantSesqForm ρ H)
    (hHsymm : H.IsSymm) (hHnonneg : H.IsNonneg) (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    (∃ K : V →ₛₗ[starRingEnd ℂ] V, IsRealStructure ρ K) ↔
      ∃ B : BilinForm ℂ V, IsInvariantForm ρ B ∧ B.IsSymm ∧ B.Nondegenerate :=
  ⟨fun ⟨_, hK⟩ =>
      exists_isInvariantForm_isSymm_nondegenerate_of_isRealStructure hK hHinv hHsymm hHnonneg hdef,
    fun ⟨_, hBinv, hBsymm, hBnd⟩ =>
      exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm hBinv hBsymm hBnd hHinv
        hHnonneg hdef⟩

/-- **Against a positive definite invariant Hermitian form, a quaternionic structure exists exactly
when a nondegenerate invariant alternating form does.**  This is the value `-1` of the
Frobenius-Schur trichotomy, `Representation.exists_isRealStructure_iff` being the value `1`; the
remaining value `0` is the case where no invariant bilinear form of either kind exists. -/
theorem exists_isQuaternionicStructure_iff {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}
    (hHinv : IsInvariantSesqForm ρ H) (hHsymm : H.IsSymm) (hHnonneg : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) :
    (∃ J : V →ₛₗ[starRingEnd ℂ] V, IsQuaternionicStructure ρ J) ↔
      ∃ B : BilinForm ℂ V, IsInvariantForm ρ B ∧ B.IsAlt ∧ B.Nondegenerate :=
  ⟨fun ⟨_, hJ⟩ =>
      exists_isInvariantForm_isAlt_nondegenerate_of_isQuaternionicStructure hJ hHinv hHsymm
        hHnonneg hdef,
    fun ⟨_, hBinv, hBalt, hBnd⟩ =>
      exists_isQuaternionicStructure_of_isInvariantForm_of_isInvariantSesqForm hBinv hBalt hBnd
        hHinv hHnonneg hdef⟩

end Equivalence

end Representation
