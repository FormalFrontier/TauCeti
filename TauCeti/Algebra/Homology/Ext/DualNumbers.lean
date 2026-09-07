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
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution

/-!
# `Extⁿ` over the dual numbers is free of rank one in every degree

Let `k` be a commutative ring, let `A = k[ε]` be the dual numbers `k[ε]/(ε²)`, and let `S = A/(ε)`
be the residue module of `A` -- its residue field when `k` is a field -- viewed as an `A`-module
through `TrivSqZeroExt.fstHom`. The multiplications

```text
⋯ ⟶ A --ε--> A --ε--> A ⟶ S ⟶ 0
```

form a projective resolution of `S`, and every differential of `Hom_A(-, S)` applied to it is
zero, because `ε` annihilates `S`. Hence `Extⁿ_A(S, S) ≅ k` as a `k`-module, for **every** `n`.

## Main definitions

* `TauCeti.dualNumberFree` and `TauCeti.dualNumberResidue`: the rank-one free module `A` and the
  residue module `S = A/(ε)`, as objects of `ModuleCat A`.
* `TauCeti.dualNumberProjectiveResolution`: the `ε`-periodic projective resolution of `S`.
* `TauCeti.extDualNumberResidueSuccEquiv`: the `k`-linear equivalence
  `Hom_A(A, S) ≃ₗ[k] Extⁿ⁺¹(S, S)` read off that resolution.
* `TauCeti.extDualNumberResidueEquiv`: the `k`-linear equivalence `Extⁿ(S, S) ≃ₗ[k] k`, for
  every `n`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5 and Chapter 4.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TrivSqZeroExt DualNumber

open scoped ModuleCat.Algebra

public section

namespace TauCeti

universe u

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

/-- Multiplication by `ε` is left multiplication by `ε` as a linear map. -/
theorem dualNumberEpsSmul_hom :
    (dualNumberEpsSmul k).hom = LinearMap.mulLeft (DualNumber k) (ε : DualNumber k) :=
  (rfl)

/-- `ε² = 0`, so multiplication by `ε` squares to zero. -/
theorem dualNumberEpsSmul_comp_dualNumberEpsSmul_eq_zero :
    dualNumberEpsSmul k ≫ dualNumberEpsSmul k = 0 :=
  ModuleCat.hom_ext (by
    rw [ModuleCat.hom_comp, dualNumberEpsSmul_hom, ← LinearMap.mulLeft_mul, eps_mul_eps,
      LinearMap.mulLeft_zero_eq_zero, ModuleCat.hom_zero])

/-- Every map from the free module to `k[ε]/(ε)` kills multiplication by `ε`: this is
the statement that `Hom_A(-, S)` turns the periodic resolution into a complex with zero
differentials. -/
theorem dualNumberEpsSmul_comp_eq_zero (f : dualNumberFree k ⟶ dualNumberResidue k) :
    dualNumberEpsSmul k ≫ f = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun x => by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, dualNumberEpsSmul_apply, ← smul_eq_mul,
      map_smul, eps_smul_dualNumberResidue, ModuleCat.hom_zero, LinearMap.zero_apply])

/-- The image of multiplication by `ε` is the set of dual numbers with vanishing constant term.
This is `DualNumber.fst_eq_zero_iff_eps_dvd` read as a statement about a linear map. -/
private theorem mem_range_dualNumberEpsSmul_iff {x : DualNumber k} :
    x ∈ LinearMap.range (dualNumberEpsSmul k).hom ↔ fst x = 0 := by
  rw [fst_eq_zero_iff_eps_dvd]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩

/-- Multiplication by `ε` is annihilated exactly by the dual numbers with vanishing constant
term. -/
private theorem mem_ker_dualNumberEpsSmul_iff {x : DualNumber k} :
    x ∈ LinearMap.ker (dualNumberEpsSmul k).hom ↔ fst x = 0 := by
  rw [LinearMap.mem_ker, dualNumberEpsSmul_apply]
  constructor
  · intro hx
    simpa [TrivSqZeroExt.snd_mul] using congrArg TrivSqZeroExt.snd hx
  · intro hx
    obtain ⟨y, rfl⟩ := fst_eq_zero_iff_eps_dvd.1 hx
    rw [← mul_assoc, eps_mul_eps, zero_mul]

/-- The quotient map kills exactly the dual numbers with vanishing constant term. -/
private theorem mem_ker_dualNumberProj_iff {x : DualNumber k} :
    x ∈ LinearMap.ker (dualNumberProj k).hom ↔ fst x = 0 := by
  rw [LinearMap.mem_ker, ← (dualNumberResidueEquiv k).map_eq_zero_iff, dualNumberProj_apply]

/-- Exactness of the periodic complex away from degree zero. -/
private theorem range_dualNumberEpsSmul_eq_ker :
    LinearMap.range (dualNumberEpsSmul k).hom = LinearMap.ker (dualNumberEpsSmul k).hom :=
  SetLike.ext fun _ ↦
    (mem_range_dualNumberEpsSmul_iff k).trans (mem_ker_dualNumberEpsSmul_iff k).symm

/-- Exactness of the augmented periodic complex in degree zero. -/
private theorem range_dualNumberEpsSmul_eq_ker_proj :
    LinearMap.range (dualNumberEpsSmul k).hom = LinearMap.ker (dualNumberProj k).hom :=
  SetLike.ext fun _ ↦
    (mem_range_dualNumberEpsSmul_iff k).trans (mem_ker_dualNumberProj_iff k).symm

/-- The quotient map `k[ε] ↠ k[ε]/(ε)` is surjective. -/
theorem dualNumberProj_surjective : Function.Surjective (dualNumberProj k).hom := fun x => by
  obtain ⟨y, hy⟩ := TrivSqZeroExt.fst_surjective (R := k) (M := k) (dualNumberResidueEquiv k x)
  exact ⟨y, (dualNumberResidueEquiv k).injective (by rw [dualNumberProj_apply]; exact hy)⟩

/-- The quotient map `k[ε] ↠ k[ε]/(ε)` is an epimorphism; this is what makes precomposition
with it injective on `End(k[ε]/(ε))`. -/
instance epi_dualNumberProj : Epi (dualNumberProj k) :=
  (ModuleCat.epi_iff_surjective _).2 (dualNumberProj_surjective k)

/-- The `ε`-periodic complex `⋯ ⟶ A --ε--> A --ε--> A` of free modules over the dual numbers. -/
-- `@[expose]`: the terms and the differentials of this complex have to reduce to the free module
-- and to multiplication by `ε`, both for the two characteristic lemmas below and for the
-- statements built on the resolution; a `HomologicalComplex` term is type-valued, so this is
-- needed already to elaborate those statements.
@[expose] noncomputable def dualNumberComplex : ChainComplex (ModuleCat.{u} (DualNumber k)) ℕ :=
  HomologicalComplex.alternatingConst (dualNumberFree k)
    (φ := dualNumberEpsSmul k) (ψ := dualNumberEpsSmul k)
    (dualNumberEpsSmul_comp_dualNumberEpsSmul_eq_zero k)
    (dualNumberEpsSmul_comp_dualNumberEpsSmul_eq_zero k)
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
      rw [dualNumberComplex_d]; exact dualNumberEpsSmul_comp_eq_zero k (dualNumberProj k)⟩

/-- The augmentation is the quotient map in degree zero. -/
@[simp]
theorem dualNumberComplexπ_f_zero : (dualNumberComplexπ k).f 0 = dualNumberProj k :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The `ε`-periodic projective resolution `⋯ ⟶ A --ε--> A --ε--> A ⟶ S ⟶ 0` of `k[ε]/(ε)`. -/
-- `@[expose]`: consumers must compute with the terms of this resolution. Already the *statements*
-- of `TauCeti.dualNumberProjectiveResolution_complex_d` and of
-- `TauCeti.extDualNumberResidueSuccEquiv` need `R.complex.X n` to reduce to the free module, so
-- they do not elaborate while the body is hidden.
@[expose] noncomputable def dualNumberProjectiveResolution :
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
        exact dualNumberProj_surjective k
    | succ m _ =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simpa using! range_dualNumberEpsSmul_eq_ker k

/-- Every term of the periodic resolution is the rank-one free module. -/
@[simp]
theorem dualNumberProjectiveResolution_complex_X (n : ℕ) :
    (dualNumberProjectiveResolution k).complex.X n = dualNumberFree k :=
  (rfl)

/-- Every differential of the periodic resolution is multiplication by `ε`. -/
@[simp]
theorem dualNumberProjectiveResolution_complex_d (n : ℕ) :
    (dualNumberProjectiveResolution k).complex.d (n + 1) n = dualNumberEpsSmul k :=
  dualNumberComplex_d k n

/-- Every differential of the periodic resolution dies against the residue field. -/
theorem dualNumberProjectiveResolution_comp_eq_zero (p q : ℕ)
    (f : (dualNumberProjectiveResolution k).complex.X q ⟶ dualNumberResidue k) :
    (dualNumberProjectiveResolution k).complex.d p q ≫ f = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel p q
  · obtain rfl : p = q + 1 := (by simpa using h : q + 1 = p).symm
    rw [dualNumberProjectiveResolution_complex_d]
    exact dualNumberEpsSmul_comp_eq_zero k f
  · rw [(dualNumberProjectiveResolution k).complex.shape p q h, zero_comp]

/-! ### The `Hom` spaces -/

/-- `Hom_A(A, S)` is isomorphic to `k` as a `k`-module, by evaluation at `1`. -/
noncomputable def homDualNumberFreeEquiv :
    (dualNumberFree k ⟶ dualNumberResidue k) ≃ₗ[k] k :=
  ModuleCat.homLinearEquiv ≪≫ₗ LinearMap.ringLmapEquivSelf (DualNumber k) k _ ≪≫ₗ
    dualNumberResidueEquiv k

/-- Evaluation at `1`, read through `TauCeti.dualNumberResidueEquiv`, is what the composite
does. This is the one place where the three equivalences above have to be unfolded: `ε`-linear
maps out of `A` and their values are definitionally the same data, but no lemma of Mathlib's
states the composite in this form. -/
theorem homDualNumberFreeEquiv_apply (f : dualNumberFree k ⟶ dualNumberResidue k) :
    homDualNumberFreeEquiv k f = dualNumberResidueEquiv k (f.hom 1) :=
  (rfl)

/-- The quotient map is the element `1` of `Hom_A(A, S) ≅ k`. -/
@[simp]
theorem homDualNumberFreeEquiv_proj : homDualNumberFreeEquiv k (dualNumberProj k) = 1 := by
  rw [homDualNumberFreeEquiv_apply, dualNumberProj_apply, fst_one]

/-- `End_A(S)` is isomorphic to `k` as a `k`-module. -/
noncomputable def homDualNumberResidueEquiv :
    (dualNumberResidue k ⟶ dualNumberResidue k) ≃ₗ[k] k :=
  LinearEquiv.ofBijective ((homDualNumberFreeEquiv k).toLinearMap ∘ₗ
      Linear.leftComp k (dualNumberResidue k) (dualNumberProj k))
    ⟨fun g g' h => (cancel_epi (dualNumberProj k)).1
        ((homDualNumberFreeEquiv k).injective h),
      fun c => ⟨c • 𝟙 (dualNumberResidue k), by
        rw [LinearMap.comp_apply, Linear.leftComp_apply, Linear.comp_smul, Category.comp_id,
          LinearEquiv.coe_coe, map_smul, homDualNumberFreeEquiv_proj, smul_eq_mul, mul_one]⟩⟩

/-! ### The `Ext` groups -/

/-- In every positive degree the periodic resolution identifies `Extⁿ⁺¹_A(S, S)` with the
`Hom`-space `Hom_A(A, S)`: no cocycle condition and no coboundary survives. -/
noncomputable def extDualNumberResidueSuccEquiv (n : ℕ) :
    (dualNumberFree k ⟶ dualNumberResidue k) ≃ₗ[k]
      Ext.{u} (dualNumberResidue k) (dualNumberResidue k) (n + 1) :=
  (dualNumberProjectiveResolution k).extLinearEquiv n
    (dualNumberProjectiveResolution_comp_eq_zero k _ _)
    (dualNumberProjectiveResolution_comp_eq_zero k _ _)

/-- The class attached to `f : A ⟶ S` is the one `CategoryTheory.ProjectiveResolution.extMk`
builds out of `f`. -/
@[simp]
theorem extDualNumberResidueSuccEquiv_apply (n : ℕ)
    (f : dualNumberFree k ⟶ dualNumberResidue k) :
    extDualNumberResidueSuccEquiv k n f =
      (dualNumberProjectiveResolution k).extMk f (n + 2) rfl
        (dualNumberProjectiveResolution_comp_eq_zero k _ _ f) :=
  ProjectiveResolution.extLinearEquiv_apply (k := k) (dualNumberProjectiveResolution k) n
    (dualNumberProjectiveResolution_comp_eq_zero k _ _)
    (dualNumberProjectiveResolution_comp_eq_zero k _ _) f

/-- **`Extⁿ_A(S, S) ≅ k` for every `n`**, where `A = k[ε]` is the ring of dual numbers and
`S = A/(ε)`: the periodic resolution of `S` has zero `Hom(-, S)`-differentials. -/
noncomputable def extDualNumberResidueEquiv :
    ∀ n : ℕ, Ext.{u} (dualNumberResidue k) (dualNumberResidue k) n ≃ₗ[k] k
  | 0 => Ext.linearEquiv₀.trans (homDualNumberResidueEquiv k)
  | (n + 1) => (extDualNumberResidueSuccEquiv k n).symm.trans (homDualNumberFreeEquiv k)

/-- In degree `0` the equivalence is the identification `Ext⁰(S, S) ≅ End_A(S) ≅ k`. -/
@[simp]
theorem extDualNumberResidueEquiv_zero
    (α : Ext.{u} (dualNumberResidue k) (dualNumberResidue k) 0) :
    extDualNumberResidueEquiv k 0 α =
      homDualNumberResidueEquiv k (Ext.linearEquiv₀ (R := k) α) := by
  rw [extDualNumberResidueEquiv, LinearEquiv.trans_apply]

/-- In positive degree the equivalence reads a class off the cocycle representing it, through
`TauCeti.homDualNumberFreeEquiv`. -/
@[simp]
theorem extDualNumberResidueEquiv_succ (n : ℕ)
    (α : Ext.{u} (dualNumberResidue k) (dualNumberResidue k) (n + 1)) :
    extDualNumberResidueEquiv k (n + 1) α =
      homDualNumberFreeEquiv k ((extDualNumberResidueSuccEquiv k n).symm α) := by
  rw [extDualNumberResidueEquiv, LinearEquiv.trans_apply]

end TauCeti
