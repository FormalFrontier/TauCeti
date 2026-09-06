/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.DualNumber
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution

/-!
# The dual numbers: `Ext`-finite but not `Ext`-bounded

Let `k` be a commutative ring, let `A = k[ε]` be the dual numbers `k[ε]/(ε²)`, and let `S = A/(ε)`
be the residue module of `A` -- its residue field when `k` is a field -- viewed as an `A`-module
through `TrivSqZeroExt.fstHom`. The multiplications

```text
⋯ ⟶ A --ε--> A --ε--> A ⟶ S ⟶ 0
```

form a projective resolution of `S`, and every differential of `Hom_A(-, S)` applied to it is
zero, because `ε` annihilates `S`. Hence `Extⁿ_A(S, S) ≅ k` as a `k`-module, for **every** `n`.

Over a field, every `Ext` group of the pair `(S, S)` is therefore a one-dimensional `k`-vector
space, but none of them vanishes, so the alternating sum `∑ n, (-1)ⁿ dim_k Extⁿ(S, S)` has no
meaning. This is the example that separates the two halves of `TauCeti.IsEulerAdmissible`:
`TauCeti.IsExtFinite` holds and `TauCeti.IsExtBounded` fails. Since `TauCeti.extEuler` takes a
proof of `TauCeti.IsEulerAdmissible` as an argument,
`TauCeti.not_isEulerAdmissible_dualNumberResidue` is exactly the statement that this pair has no
Ext-Euler characteristic; no totalised value is available for it.

## Main definitions

* `TauCeti.dualNumberFree` and `TauCeti.dualNumberResidue`: the rank-one free module `A` and the
  residue module `S = A/(ε)`, as objects of `ModuleCat A`.
* `TauCeti.dualNumberProjectiveResolution`: the `ε`-periodic projective resolution of `S`.
* `TauCeti.extDualNumberResidueEquiv`: the `k`-linear equivalence `Extⁿ(S, S) ≃ₗ[k] k`, for
  every `n`.

## Main results

* `TauCeti.finrank_ext_dualNumberResidue`: over a field, every `Extⁿ(S, S)` is one-dimensional.
* `TauCeti.isExtFinite_dualNumberResidue`: every `Extⁿ(S, S)` is a finite-dimensional
  `k`-vector space.
* `TauCeti.not_isExtBounded_dualNumberResidue`: no degree bounds the `Ext`-support of `(S, S)`.
* `TauCeti.not_isEulerAdmissible_dualNumberResidue`: the pair `(S, S)` is not Euler-admissible.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5 and Chapter 4.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TrivSqZeroExt DualNumber

open scoped ModuleCat.Algebra

-- The terms and differentials of the periodic complex have to reduce definitionally to the free
-- module and to multiplication by `ε`, so that the resolution and the `Hom`-space computations
-- typecheck against `CategoryTheory.ProjectiveResolution.complex`; hence `@[expose]`.
@[expose] public section

namespace TauCeti

universe u

section CommRing

variable (k : Type u) [CommRing k]

/-! ### The two modules -/

/-- The rank-one free module over the dual numbers `k[ε]`. -/
noncomputable abbrev dualNumberFree : ModuleCat.{u} (DualNumber k) :=
  ModuleCat.of _ (DualNumber k)

/-- The quotient `k[ε]/(ε)` of the dual numbers, as a `k[ε]`-module: the underlying `k`-module
is `k`, and `ε` acts by zero. When `k` is a field this is the residue field of `k[ε]`. -/
noncomputable abbrev dualNumberResidue : ModuleCat.{u} (DualNumber k) :=
  (ModuleCat.restrictScalars (TrivSqZeroExt.fstHom k k k).toRingHom).obj (ModuleCat.of k k)

/-- The quotient `k[ε]/(ε)` is `k` as a `k`-module. -/
noncomputable def dualNumberResidueEquiv : dualNumberResidue k ≃ₗ[k] k where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `k[ε]`-action on `k[ε]/(ε)` is multiplication by the constant term. -/
theorem dualNumberResidueEquiv_smul (a : DualNumber k) (x : dualNumberResidue k) :
    dualNumberResidueEquiv k (a • x) = fst a * dualNumberResidueEquiv k x :=
  (rfl)

/-- `ε` annihilates `k[ε]/(ε)`. -/
theorem eps_smul_dualNumberResidue (x : dualNumberResidue k) : (ε : DualNumber k) • x = 0 :=
  (dualNumberResidueEquiv k).injective (by
    rw [dualNumberResidueEquiv_smul, fst_eps, zero_mul, map_zero])

/-! ### The periodic resolution -/

/-- Multiplication by `ε` on the rank-one free module. -/
noncomputable def dualNumberEpsSmul : dualNumberFree k ⟶ dualNumberFree k :=
  ModuleCat.ofHom (LinearMap.mulLeft (DualNumber k) (ε : DualNumber k))

/-- Multiplication by `ε` acts on elements as multiplication by `ε`. -/
@[simp]
theorem dualNumberEpsSmul_apply (x : DualNumber k) :
    (dualNumberEpsSmul k).hom x = ε * x :=
  (rfl)

/-- The quotient map `k[ε] ↠ k[ε]/(ε)`. -/
noncomputable def dualNumberProj : dualNumberFree k ⟶ dualNumberResidue k :=
  ModuleCat.ofHom (X := dualNumberFree k) (Y := dualNumberResidue k)
    { toFun := TrivSqZeroExt.fst
      map_add' := fun _ _ => rfl
      map_smul' := TrivSqZeroExt.fst_mul }

/-- The quotient map is the constant-term map, read through `TauCeti.dualNumberResidueEquiv`. -/
@[simp]
theorem dualNumberProj_apply (x : DualNumber k) :
    dualNumberResidueEquiv k ((dualNumberProj k).hom x) = fst x :=
  (rfl)

/-- `ε² = 0`, so multiplication by `ε` squares to zero. -/
theorem dualNumberEpsSmul_comp_dualNumberEpsSmul :
    dualNumberEpsSmul k ≫ dualNumberEpsSmul k = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun x => by
    change ε * (ε * x) = 0
    rw [← mul_assoc, eps_mul_eps, zero_mul])

/-- Every map from the free module to `k[ε]/(ε)` kills multiplication by `ε`: this is
the statement that `Hom_A(-, S)` turns the periodic resolution into a complex with zero
differentials. -/
theorem dualNumberEpsSmul_comp (f : dualNumberFree k ⟶ dualNumberResidue k) :
    dualNumberEpsSmul k ≫ f = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun x => by
    change f.hom ((ε : DualNumber k) • x) = 0
    rw [map_smul, eps_smul_dualNumberResidue])

/-- The image of multiplication by `ε` is the set of dual numbers with vanishing constant term.
This is `DualNumber.fst_eq_zero_iff_eps_dvd` read as a statement about a linear map. -/
theorem mem_range_dualNumberEpsSmul_iff {x : DualNumber k} :
    x ∈ LinearMap.range (dualNumberEpsSmul k).hom ↔ fst x = 0 := by
  rw [fst_eq_zero_iff_eps_dvd]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩

/-- Multiplication by `ε` is annihilated exactly by the dual numbers with vanishing constant
term. -/
theorem mem_ker_dualNumberEpsSmul_iff {x : DualNumber k} :
    x ∈ LinearMap.ker (dualNumberEpsSmul k).hom ↔ fst x = 0 := by
  constructor
  · intro hx
    have h : (ε : DualNumber k) * x = 0 := hx
    simpa [TrivSqZeroExt.snd_mul] using congrArg TrivSqZeroExt.snd h
  · intro hx
    obtain ⟨y, rfl⟩ := fst_eq_zero_iff_eps_dvd.1 hx
    change (ε : DualNumber k) * ((ε : DualNumber k) * y) = 0
    rw [← mul_assoc, eps_mul_eps, zero_mul]

/-- The quotient map kills exactly the dual numbers with vanishing constant term. -/
theorem mem_ker_dualNumberProj_iff {x : DualNumber k} :
    x ∈ LinearMap.ker (dualNumberProj k).hom ↔ fst x = 0 := by
  rw [LinearMap.mem_ker, ← (dualNumberResidueEquiv k).map_eq_zero_iff, dualNumberProj_apply]

/-- Exactness of the periodic complex away from degree zero. -/
theorem range_dualNumberEpsSmul :
    LinearMap.range (dualNumberEpsSmul k).hom = LinearMap.ker (dualNumberEpsSmul k).hom :=
  SetLike.ext fun _ ↦
    (mem_range_dualNumberEpsSmul_iff k).trans (mem_ker_dualNumberEpsSmul_iff k).symm

/-- Exactness of the augmented periodic complex in degree zero. -/
theorem range_dualNumberEpsSmul_eq_ker_proj :
    LinearMap.range (dualNumberEpsSmul k).hom = LinearMap.ker (dualNumberProj k).hom :=
  SetLike.ext fun _ ↦
    (mem_range_dualNumberEpsSmul_iff k).trans (mem_ker_dualNumberProj_iff k).symm

/-- The quotient map `k[ε] ↠ k[ε]/(ε)` is surjective. -/
theorem dualNumberProj_surjective : Function.Surjective (dualNumberProj k).hom := fun x => by
  refine ⟨inl (dualNumberResidueEquiv k x), (dualNumberResidueEquiv k).injective ?_⟩
  rw [dualNumberProj_apply, fst_inl]

/-- The quotient map `k[ε] ↠ k[ε]/(ε)` is an epimorphism; this is what makes precomposition
with it injective on `End(k[ε]/(ε))`. -/
instance epi_dualNumberProj : Epi (dualNumberProj k) :=
  (ModuleCat.epi_iff_surjective _).2 (dualNumberProj_surjective k)

/-- The `ε`-periodic complex `⋯ ⟶ A --ε--> A --ε--> A` of free modules over the dual numbers. -/
noncomputable def dualNumberComplex : ChainComplex (ModuleCat.{u} (DualNumber k)) ℕ :=
  HomologicalComplex.alternatingConst (dualNumberFree k)
    (φ := dualNumberEpsSmul k) (ψ := dualNumberEpsSmul k)
    (dualNumberEpsSmul_comp_dualNumberEpsSmul k) (dualNumberEpsSmul_comp_dualNumberEpsSmul k)
    fun _ _ => ComplexShape.down_nat_odd_add

/-- Every differential of the periodic complex is multiplication by `ε`. -/
@[simp]
theorem dualNumberComplex_d (n : ℕ) :
    (dualNumberComplex k).d (n + 1) n = dualNumberEpsSmul k := by
  simp only [dualNumberComplex, HomologicalComplex.alternatingConst_d]
  split_ifs with h1 h2 <;> first | rfl | exact absurd rfl h1

/-- The augmentation of the periodic complex by the residue field. -/
noncomputable def dualNumberComplexπ :
    dualNumberComplex k ⟶ (ChainComplex.single₀ (ModuleCat.{u} (DualNumber k))).obj
      (dualNumberResidue k) :=
  ((dualNumberComplex k).toSingle₀Equiv (dualNumberResidue k)).symm
    ⟨dualNumberProj k, by
      rw [dualNumberComplex_d]; exact dualNumberEpsSmul_comp k (dualNumberProj k)⟩

/-- The augmentation is the quotient map in degree zero. -/
@[simp]
theorem dualNumberComplexπ_f_zero : (dualNumberComplexπ k).f 0 = dualNumberProj k :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The `ε`-periodic projective resolution `⋯ ⟶ A --ε--> A --ε--> A ⟶ S ⟶ 0` of `k[ε]/(ε)`. -/
noncomputable def dualNumberProjectiveResolution :
    ProjectiveResolution (dualNumberResidue k) where
  complex := dualNumberComplex k
  projective _ := inferInstanceAs (Projective (dualNumberFree k))
  π := dualNumberComplexπ k
  quasiIso := by
    constructor
    intro m
    induction m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        simpa using! range_dualNumberEpsSmul_eq_ker_proj k
      · rw [ModuleCat.epi_iff_surjective]
        intro x
        exact ⟨inl x, rfl⟩
    | succ m _ =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simpa using! range_dualNumberEpsSmul k

/-- Every term of the periodic resolution is the rank-one free module. -/
@[simp]
theorem dualNumberProjectiveResolution_complex_X (n : ℕ) :
    (dualNumberProjectiveResolution k).complex.X n = dualNumberFree k :=
  rfl

/-- Every differential of the periodic resolution dies against the residue field. -/
theorem dualNumberProjectiveResolution_comp_eq_zero (p q : ℕ)
    (f : (dualNumberProjectiveResolution k).complex.X q ⟶ dualNumberResidue k) :
    (dualNumberProjectiveResolution k).complex.d p q ≫ f = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel p q
  · obtain rfl : p = q + 1 := (by simpa using h : q + 1 = p).symm
    change (dualNumberComplex k).d (q + 1) q ≫ f = 0
    rw [dualNumberComplex_d]
    exact dualNumberEpsSmul_comp k f
  · rw [(dualNumberProjectiveResolution k).complex.shape p q h, zero_comp]

/-! ### The `Hom` spaces -/

/-- `Hom_A(A, S)` is one-dimensional over `k`, by evaluation at `1`. -/
noncomputable def homDualNumberFreeEquiv :
    (dualNumberFree k ⟶ dualNumberResidue k) ≃ₗ[k] k where
  toFun f := dualNumberResidueEquiv k (f.hom 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := c • dualNumberProj k
  left_inv f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    apply (dualNumberResidueEquiv k).injective
    have h : dualNumberResidueEquiv k (f.hom (x * 1)) =
        fst x * dualNumberResidueEquiv k (f.hom 1) :=
      congrArg (dualNumberResidueEquiv k) (f.hom.map_smul x 1)
    rw [mul_one] at h
    change dualNumberResidueEquiv k
      ((dualNumberResidueEquiv k (f.hom 1)) • (dualNumberProj k).hom x) = _
    rw [map_smul, dualNumberProj_apply, smul_eq_mul, h, mul_comm]
  right_inv c := by
    change dualNumberResidueEquiv k (c • (dualNumberProj k).hom 1) = c
    rw [map_smul, dualNumberProj_apply, fst_one, smul_eq_mul, mul_one]

/-- The quotient map is the element `1` of `Hom_A(A, S) ≅ k`. -/
@[simp]
theorem homDualNumberFreeEquiv_proj : homDualNumberFreeEquiv k (dualNumberProj k) = 1 := by
  change dualNumberResidueEquiv k ((dualNumberProj k).hom 1) = 1
  rw [dualNumberProj_apply, fst_one]

/-- Precomposition with the quotient map `A ↠ S`. -/
noncomputable def precompDualNumberProj :
    (dualNumberResidue k ⟶ dualNumberResidue k) →ₗ[k]
      (dualNumberFree k ⟶ dualNumberResidue k) where
  toFun g := dualNumberProj k ≫ g
  map_add' g g' := by simp [Preadditive.comp_add]
  map_smul' c g := by simp [Linear.comp_smul]

/-- `End_A(S)` is one-dimensional over `k`. -/
noncomputable def homDualNumberResidueEquiv :
    (dualNumberResidue k ⟶ dualNumberResidue k) ≃ₗ[k] k :=
  LinearEquiv.ofBijective ((homDualNumberFreeEquiv k).toLinearMap ∘ₗ precompDualNumberProj k)
    ⟨fun g g' h => (cancel_epi (dualNumberProj k)).1
        ((homDualNumberFreeEquiv k).injective h),
      fun c => ⟨c • 𝟙 (dualNumberResidue k), by
        change homDualNumberFreeEquiv k (dualNumberProj k ≫ (c • 𝟙 (dualNumberResidue k))) = c
        rw [Linear.comp_smul, Category.comp_id, map_smul, homDualNumberFreeEquiv_proj,
          smul_eq_mul, mul_one]⟩⟩

/-! ### The `Ext` groups -/

/-- **`Extⁿ_A(S, S) ≅ k` for every `n`**, where `A = k[ε]` is the ring of dual numbers and
`S = A/(ε)`: the periodic resolution of `S` has zero `Hom(-, S)`-differentials. -/
noncomputable def extDualNumberResidueEquiv :
    ∀ n : ℕ, Ext.{u} (dualNumberResidue k) (dualNumberResidue k) n ≃ₗ[k] k
  | 0 => Ext.linearEquiv₀.trans (homDualNumberResidueEquiv k)
  | (n + 1) =>
    (extLinearEquivOfProjectiveResolution (k := k) (dualNumberProjectiveResolution k)
      (dualNumberProjectiveResolution_comp_eq_zero k) n).symm.trans
        (homDualNumberFreeEquiv k)

end CommRing

/-! ### The failure of Euler-admissibility -/

section Field

variable (k : Type u) [Field k]

/-- Over a field, every `Extⁿ(S, S)` of the residue field `S` of `k[ε]` is one-dimensional. -/
theorem finrank_ext_dualNumberResidue (n : ℕ) :
    Module.finrank k (Ext.{u} (dualNumberResidue k) (dualNumberResidue k) n) = 1 := by
  rw [(extDualNumberResidueEquiv k n).finrank_eq, Module.finrank_self]

/-- Every `Ext` group of `k[ε]/(ε)` against itself is a finite-dimensional `k`-vector space. -/
theorem isExtFinite_dualNumberResidue :
    IsExtFinite.{u} k (dualNumberResidue k) (dualNumberResidue k) :=
  ⟨fun n => (extDualNumberResidueEquiv k n).symm.finiteDimensional⟩

/-- No degree is a vanishing bound for the `Ext` groups of `k[ε]/(ε)` against itself, because
none of them vanishes. -/
theorem not_isExtBoundedBy_dualNumberResidue (N : ℕ) :
    ¬ IsExtBoundedBy.{u} (dualNumberResidue k) (dualNumberResidue k) N := by
  intro h
  have hsub : Subsingleton (Ext.{u} (dualNumberResidue k) (dualNumberResidue k) N) :=
    h.subsingleton (le_refl N)
  have : Subsingleton k := (extDualNumberResidueEquiv k N).symm.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton k

/-- **The dual-numbers rejection.** `Extⁿ(S, S)` never vanishes, so the pair `(S, S)` is not
`Ext`-bounded. -/
theorem not_isExtBounded_dualNumberResidue :
    ¬ IsExtBounded.{u} (dualNumberResidue k) (dualNumberResidue k) := by
  rintro ⟨N, hN⟩
  exact not_isExtBoundedBy_dualNumberResidue k N hN

/-- **The dual-numbers rejection.** The residue field `S` of `k[ε]` is not Euler-admissible
against itself: its `Ext` groups are all one-dimensional, so `Ext`-finiteness holds
(`TauCeti.isExtFinite_dualNumberResidue`), but none of them vanishes, so the alternating sum
`∑ n, (-1)ⁿ dim_k Extⁿ(S, S)` is not a finite sum. Because `TauCeti.extEuler` consumes a proof of
`TauCeti.IsEulerAdmissible`, this pair has no Ext-Euler characteristic at all; no totalised value
is exposed for it. -/
theorem not_isEulerAdmissible_dualNumberResidue :
    ¬ IsEulerAdmissible.{u} k (dualNumberResidue k) (dualNumberResidue k) :=
  fun h => not_isExtBounded_dualNumberResidue k h.isExtBounded

end Field

end TauCeti
