/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.Lattice
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.LinearAlgebra.Dimension.BaseChange

/-!
# Full submodule and integral lattices

This file provides generic results about full submodules over fraction fields and full integral
lattices in real vector spaces. It relates bases and ranks of full submodules to their ambient
spaces, extends integral linear equivalences between full submodules to rational linear equivalences
of their ambient spaces, and proves that rational linear equivalences preserve fullness. It also
records the injectivity, spanning, rank, discreteness, and `IsZLattice` consequences of the
scalar-extension characterization of an integral lattice. Finally, a free full lattice over an
integral domain rationalizes to its ambient vector space over the fraction field.

## Main declarations

* `TauCeti.Basis.span_range_extendOfIsLattice`: the span of an extended lattice basis is the
  lattice.
* `TauCeti.Submodule.IsLattice.toAddSubgroup_eq_closure_range_extendOfIsLattice`: the additive
  closure of an extended lattice basis is the lattice's underlying additive subgroup.
* `Submodule.toAddSubgroup_submoduleOf`: taking the underlying additive subgroup commutes
  with restricting a submodule to another submodule.
* `TauCeti.Submodule.IsLattice.finrank_eq_finrank`: a full lattice and its ambient space have the
  same finrank.
* `TauCeti.LinearEquiv.extendOfIsLattice`: extension of an integral linear equivalence between
  full submodules to their rational ambient spaces.
* `TauCeti.Submodule.IsLattice.isBaseChange_subtype`: the inclusion of a free full lattice
  submodule into its ambient vector space over the fraction field is a base change.
* `TauCeti.Submodule.rationalizationEquiv`: the canonical equivalence from the scalar extension
  of a free full lattice submodule to its ambient vector space.
* `TauCeti.TensorProduct.unitTmulEquiv`: a finite free module is the full lattice of unit pure
  tensors in its scalar extension.
* `TauCeti.TensorProduct.rationalizationEquiv_baseChange_unitTmulEquiv`: rationalizing that
  unit-tensor lattice returns the scalar extension one started from.
* `AddMonoidHom.IsIntegralLattice`: an additive map from a finite free `ℤ`-module whose scalar
  extension to `ℝ` is a base change.
* `AddMonoidHom.IsIntegralLattice.injective`, `span_range_eq_top`, `finrank_eq_finrank`,
  `isDiscrete_range`, and `isZLattice_range`: the main integral-lattice consequences.
* `AddMonoidHom.IsIntegralLattice.comp_equiv_eq_equiv_comp_baseChange`: naturality of the
  scalar-extension equivalence under compatible integral and real-linear maps.

## References

* See N. Bourbaki, *Commutative Algebra*, Chapter VII, §4 for lattice theory over Dedekind domains.
* The integral-lattice interface and its Layer 0 target are specified in
  `TauCetiRoadmap/AnalyticToricGeometry/README.md`, item 1, with the pinned declarations in
  `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u v w

section

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The `R`-span of the ambient `K`-basis obtained from an `R`-basis of a lattice is the lattice
itself. -/
theorem Basis.span_range_extendOfIsLattice {κ : Type*} {N : Submodule R V} [N.IsLattice K]
    (b : Basis κ R N) :
    Submodule.span R (Set.range (b.extendOfIsLattice K)) = N := by
  have hrange : Set.range (b.extendOfIsLattice K) = Set.range (N.subtype ∘ b) :=
    congrArg Set.range (funext fun i ↦ Basis.extendOfIsLattice_apply K b i)
  rw [hrange, Set.range_comp, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- The `R`-finrank of a free full lattice in `V` equals the `K`-finrank of the ambient space. -/
theorem Submodule.IsLattice.finrank_eq_finrank [IsDomain R]
    (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    Module.finrank R N = Module.finrank K V := by
  let b := Module.Free.chooseBasis R N
  exact congr_arg Cardinal.toNat
    (b.mk_eq_rank''.symm.trans (b.extendOfIsLattice K).mk_eq_rank'')

end

section

/-- Taking the underlying additive subgroup commutes with restricting a submodule to another
submodule. -/
theorem _root_.Submodule.toAddSubgroup_submoduleOf {R V : Type*} [Ring R] [AddCommGroup V]
    [Module R V] (p q : Submodule R V) :
    (p.submoduleOf q).toAddSubgroup = p.toAddSubgroup.addSubgroupOf q.toAddSubgroup := rfl

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The additive subgroup generated by an extended basis of a full `ℤ`-submodule is the submodule's
underlying additive subgroup. -/
theorem Submodule.IsLattice.toAddSubgroup_eq_closure_range_extendOfIsLattice
    {N : Submodule ℤ V} [N.IsLattice ℚ] {κ : Type*} (b : Basis κ ℤ N) :
    N.toAddSubgroup = AddSubgroup.closure (Set.range (b.extendOfIsLattice ℚ)) := by
  apply AddSubgroup.toIntSubmodule.injective
  rw [AddSubgroup.toIntSubmodule_closure, TauCeti.Basis.span_range_extendOfIsLattice,
    Submodule.toIntSubmodule_toAddSubgroup, Submodule.restrictScalars_self]

end

namespace LinearEquiv

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]

/-- Extend an integral linear equivalence between full submodules uniquely to their rational
ambient spaces. -/
noncomputable def extendOfIsLattice {S : Submodule ℤ V} {T : Submodule ℤ W}
    [S.IsLattice ℚ] [T.IsLattice ℚ] (e : S ≃ₗ[ℤ] T) : V ≃ₗ[ℚ] W :=
  let b := Module.Free.chooseBasis ℤ S
  (b.extendOfIsLattice ℚ).equiv ((b.map e).extendOfIsLattice ℚ) (Equiv.refl _)

/-- The rational extension of a full-submodule equivalence agrees with it on the submodule. -/
@[simp]
theorem extendOfIsLattice_apply {S : Submodule ℤ V} {T : Submodule ℤ W}
    [S.IsLattice ℚ] [T.IsLattice ℚ] (e : S ≃ₗ[ℤ] T) (x : S) :
    extendOfIsLattice e (x : V) = (e x : W) := by
  let b := Module.Free.chooseBasis ℤ S
  have h : (extendOfIsLattice e).toLinearMap.restrictScalars ℤ ∘ₗ S.subtype =
      T.subtype ∘ₗ e.toLinearMap := by
    apply b.ext
    intro i
    dsimp only [b]
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply,
      LinearEquiv.coe_toLinearMap]
    rw [← Basis.extendOfIsLattice_apply ℚ (Module.Free.chooseBasis ℤ S) i]
    -- Expose the constructed basis equivalence so `Basis.equiv_apply` can identify its values.
    unfold extendOfIsLattice
    rw [Basis.equiv_apply, Basis.extendOfIsLattice_apply, Basis.map_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun h x

/-- A rational linear equivalence extending a given equivalence of full submodules is the
canonical extension. -/
theorem eq_extendOfIsLattice {S : Submodule ℤ V} {T : Submodule ℤ W}
    [S.IsLattice ℚ] [T.IsLattice ℚ] (e : S ≃ₗ[ℤ] T) (f : V ≃ₗ[ℚ] W)
    (h : ∀ x : S, f (x : V) = (e x : W)) : f = extendOfIsLattice e := by
  apply LinearEquiv.toLinearMap_injective
  apply (Module.Free.chooseBasis ℤ S).extendOfIsLattice ℚ |>.ext
  intro i
  rw [Basis.extendOfIsLattice_apply]
  exact (h (Module.Free.chooseBasis ℤ S i)).trans
    (extendOfIsLattice_apply e (Module.Free.chooseBasis ℤ S i)).symm

/-- The rational extension maps the source full submodule onto the target full submodule. -/
theorem extendOfIsLattice_map {S : Submodule ℤ V} {T : Submodule ℤ W}
    [S.IsLattice ℚ] [T.IsLattice ℚ] (e : S ≃ₗ[ℤ] T) :
    S.map ((extendOfIsLattice e).restrictScalars ℤ).toLinearMap = T := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hmem : (e (⟨x, hx⟩ : S) : W) ∈ T := (e ⟨x, hx⟩).2
    rw [← extendOfIsLattice_apply] at hmem
    simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_toLinearMap] using hmem
  · intro y hy
    let yT : T := ⟨y, hy⟩
    let xS : S := e.symm yT
    refine ⟨(xS : V), xS.2, ?_⟩
    simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_toLinearMap,
      extendOfIsLattice_apply] using congr_arg Subtype.val (e.apply_symm_apply yT)

end LinearEquiv

namespace Submodule

namespace IsLattice

variable {R : Type u} {K : Type v} {V' : Type w}
variable [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V'] [Module R V'] [Module K V'] [IsScalarTower R K V']

/-- The inclusion of a free full lattice submodule over an integral domain into its ambient vector
space over the fraction field exhibits that space as base change from `R` to `K`. -/
theorem isBaseChange_subtype (S : Submodule R V') [Module.Free R S] [S.IsLattice K] :
    IsBaseChange K S.subtype := by
  have : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (IsFractionRing.injective R K)
  let b := Module.Free.chooseBasis R S
  let e : K ⊗[R] S ≃ₗ[K] V' :=
    (b.baseChange K).equiv (b.extendOfIsLattice K) (Equiv.refl _)
  have hmap : (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R K S 1) =
      S.subtype := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
      LinearEquiv.coe_coe, Submodule.subtype_apply]
    rw [← Module.Basis.baseChange_apply K b i, Basis.equiv_apply,
      Basis.extendOfIsLattice_apply, Equiv.refl_apply]
  exact IsBaseChange.of_equiv e fun x ↦ DFunLike.congr_fun hmap x

end IsLattice

variable {R : Type u} {K : Type v} {V' : Type w}
variable [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V'] [Module R V'] [Module K V'] [IsScalarTower R K V']

/-- The canonical equivalence from the scalar extension of a free full lattice submodule to its
ambient vector space. -/
noncomputable def rationalizationEquiv (S : Submodule R V') [Module.Free R S] [S.IsLattice K] :
    K ⊗[R] S ≃ₗ[K] V' :=
  (IsLattice.isBaseChange_subtype S).equiv

/-- The rationalization equivalence sends a pure tensor to scalar multiplication of the embedded
lattice vector. This equation characterizes the equivalence. -/
@[simp]
theorem rationalizationEquiv_tmul (S : Submodule R V') [Module.Free R S] [S.IsLattice K]
    (k : K) (x : S) : rationalizationEquiv S (k ⊗ₜ[R] x) = k • (x : V') :=
  (IsLattice.isBaseChange_subtype S).equiv_tmul k x

/-- The inverse rationalization equivalence sends an embedded lattice vector to the corresponding
unit pure tensor. -/
@[simp]
theorem rationalizationEquiv_symm_coe (S : Submodule R V') [Module.Free R S] [S.IsLattice K]
    (x : S) : (rationalizationEquiv S).symm (x : V') = 1 ⊗ₜ[R] x :=
  (IsLattice.isBaseChange_subtype S).equiv_symm_apply x

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]

/-- A rational linear equivalence maps a full integral submodule to a full integral submodule. -/
theorem IsLattice.map (S : Submodule ℤ V) [S.IsLattice ℚ] (e : V ≃ₗ[ℚ] W) :
    (S.map (e.restrictScalars ℤ).toLinearMap).IsLattice ℚ where
  fg := Submodule.FG.map (e.restrictScalars ℤ).toLinearMap
    _root_.Submodule.IsLattice.fg
  span_eq_top := by
    simp [Submodule.map_coe, Submodule.span_image_linearEquiv,
      _root_.Submodule.IsLattice.span_eq_top]

end Submodule

namespace TensorProduct

variable {R : Type u} {K : Type v} {M : Type w}
variable [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

omit [IsDomain R] [IsFractionRing R K] [Module.Free R M] [Module.Finite R M] in
/-- The unit pure tensors are the `R`-span of the base change of any basis. -/
theorem range_mk_one_eq_span {ι : Type*} (b : Basis ι R M) :
    LinearMap.range (TensorProduct.mk R K M 1) =
      Submodule.span R (Set.range (b.baseChange K)) := by
  rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span R)
    (congrArg Set.range (funext fun i ↦ (Basis.baseChange_apply K b i).symm))

/-- The unit pure tensors form a full lattice in the scalar extension of a finite free module. -/
instance isLattice_range_mk_one :
    (LinearMap.range (TensorProduct.mk R K M 1)).IsLattice K where
  fg := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  span_eq_top := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul k m =>
      rw [tmul_eq_smul_one_tmul]
      exact Submodule.smul_mem _ k (Submodule.subset_span ⟨m, rfl⟩)

variable (R K M) in
/-- A finite free module is canonically isomorphic to the lattice of unit pure tensors in its
scalar extension. -/
noncomputable def unitTmulEquiv : M ≃ₗ[R] LinearMap.range (TensorProduct.mk R K M 1) :=
  LinearEquiv.ofInjective _ (Module.Flat.tensorProduct_mk_injective R M K)

/-- The lattice of unit pure tensors is free, being a copy of the module it comes from. -/
instance free_range_mk_one :
    Module.Free R (LinearMap.range (TensorProduct.mk R K M 1)) :=
  Module.Free.of_equiv (unitTmulEquiv R K M)

omit [IsDomain R] [Module.Finite R M] in
/-- The unit-tensor equivalence sends a vector to its unit pure tensor. This equation
characterizes the equivalence. -/
@[simp]
theorem coe_unitTmulEquiv_apply (m : M) :
    (unitTmulEquiv R K M m : K ⊗[R] M) = 1 ⊗ₜ[R] m := by
  rw [unitTmulEquiv, LinearEquiv.ofInjective_apply, TensorProduct.mk_apply]

omit [IsDomain R] [Module.Finite R M] in
/-- The inverse unit-tensor equivalence recovers a vector from its unit pure tensor. -/
@[simp]
theorem unitTmulEquiv_symm_tmul (m : M)
    (h : (1 : K) ⊗ₜ[R] m ∈ LinearMap.range (TensorProduct.mk R K M 1)) :
    (unitTmulEquiv R K M).symm ⟨1 ⊗ₜ[R] m, h⟩ = m := by
  apply (unitTmulEquiv R K M).injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext (coe_unitTmulEquiv_apply m).symm

/-- Rationalizing the unit-tensor lattice recovers the scalar extension it sits in: base-changing
the unit-tensor equivalence and then rationalizing is the identity. -/
@[simp]
theorem rationalizationEquiv_baseChange_unitTmulEquiv (x : K ⊗[R] M) :
    Submodule.rationalizationEquiv (LinearMap.range (TensorProduct.mk R K M 1))
        (LinearEquiv.baseChange R K M _ (unitTmulEquiv R K M) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul k m =>
    rw [LinearEquiv.baseChange_tmul, Submodule.rationalizationEquiv_tmul,
      coe_unitTmulEquiv_apply]
    exact (tmul_eq_smul_one_tmul k m).symm

/-- The bundled form of `rationalizationEquiv_baseChange_unitTmulEquiv`. -/
theorem unitTmulEquiv_baseChange_trans_rationalizationEquiv :
    (LinearEquiv.baseChange R K M _ (unitTmulEquiv R K M)).trans
        (Submodule.rationalizationEquiv (LinearMap.range (TensorProduct.mk R K M 1))) =
      LinearEquiv.refl K (K ⊗[R] M) :=
  LinearEquiv.ext rationalizationEquiv_baseChange_unitTmulEquiv

end TensorProduct

/-!
## Integral lattices in real vector spaces

This section defines the full integral-lattice datum used by the toric geometry development. An
additive map from a finite free `ℤ`-module is a lattice map precisely when its scalar extension to
`ℝ` is an equivalence. The resulting API records injectivity, fullness, and equality of the
integral and real ranks, which are the basic facts needed to make rational cones coordinate-free.

The scalar-extension formulation combines injectivity with full real spanning: it rules out, for
example, the injective map `ℤ² → ℝ` given by `(a, b) ↦ a + √2 * b`.

## References

* D. Cox, J. Little, and H. Schenck, *Toric Varieties*, §1.1.
* W. Fulton, *Introduction to Toric Varieties*, §1.2.

-/

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

universe u' v'

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]

private noncomputable instance moduleOfNormedSpace (E : Type w) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Module ℝ E :=
  NormedSpace.toModule

end TauCeti

universe u v w u' v'

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]

namespace AddMonoidHom

/-- An additive map is a full integral lattice when its scalar extension to `ℝ` is a base change.

The base-change condition says that the scalar extension sends each pure tensor `1 ⊗ₜ n` to the
corresponding lattice vector `i n`. It gives fullness, while the datum records the finiteness and
freeness needed for the API to derive discreteness. -/
structure IsIntegralLattice (i : N →+ V) : Prop where
  free : Module.Free ℤ N
  finite : Module.Finite ℤ N
  baseChange : IsBaseChange ℝ i.toIntLinearMap

/-- Construct an integral lattice from its scalar-extension equivalence. -/
theorem IsIntegralLattice.of_equiv [Module.Free ℤ N] [Module.Finite ℤ N]
    (i : N →+ V) (e : TensorProduct ℤ ℝ N ≃ₗ[ℝ] V)
    (he : ∀ n : N, e ((1 : ℝ) ⊗ₜ[ℤ] n) = i n) : IsIntegralLattice i :=
  ⟨inferInstance, inferInstance, IsBaseChange.of_equiv e fun n ↦ by
    simpa only [AddMonoidHom.coe_toIntLinearMap] using he n⟩

/-- An integral lattice has finite-dimensional real span. -/
theorem IsIntegralLattice.finiteDimensional (i : N →+ V) (h : IsIntegralLattice i) :
    FiniteDimensional ℝ V := by
  let _ : Module.Finite ℤ N := h.finite
  let _ : Module.Finite ℝ V := TauCeti.finite_of_isBaseChange h.baseChange
  infer_instance

/-- An integral lattice map is injective. -/
theorem IsIntegralLattice.injective (i : N →+ V) (h : IsIntegralLattice i) :
    Function.Injective i := by
  intro m n hmn
  apply @Module.Flat.tensorProduct_mk_injective ℤ N _ _ _ ℝ _ _ _
    (@Module.Flat.of_free ℤ N _ _ _ h.free)
  apply h.baseChange.equiv.injective
  simp only [TensorProduct.mk_apply, IsBaseChange.equiv_tmul, one_smul,
    AddMonoidHom.coe_toIntLinearMap, hmn]

/-- The real basis obtained by extending a chosen integral basis through the lattice equivalence. -/
noncomputable def IsIntegralLattice.realBasis (i : N →+ V) (h : IsIntegralLattice i) :
    Module.Basis (@Module.Free.ChooseBasisIndex ℤ N _ _ _ h.free) ℝ V := by
  letI := h.free
  exact (Module.Free.chooseBasis ℤ N).baseChange ℝ |>.map h.baseChange.equiv

/-- The induced real basis consists of the images of the chosen integral basis vectors. -/
@[simp]
theorem IsIntegralLattice.realBasis_apply (i : N →+ V) (h : IsIntegralLattice i)
    (j : @Module.Free.ChooseBasisIndex ℤ N _ _ _ h.free) :
    IsIntegralLattice.realBasis i h j =
      i ((@Module.Free.chooseBasis ℤ N _ _ _ h.free) j) := by
  simp only [IsIntegralLattice.realBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  simp only [IsBaseChange.equiv_tmul, one_smul, AddMonoidHom.coe_toIntLinearMap] at ⊢

/-- The image of an integral lattice is the `ℤ`-span of the induced real basis. -/
theorem IsIntegralLattice.range_eq_span_realBasis (i : N →+ V) (h : IsIntegralLattice i) :
    Set.range i =
      (Submodule.span ℤ (Set.range (IsIntegralLattice.realBasis i h)) : Set V) := by
  have hrange : Set.range i = (LinearMap.range i.toIntLinearMap : Set V) := by
    simp only [LinearMap.coe_range, AddMonoidHom.coe_toIntLinearMap]
  rw [hrange]
  have hrange' : LinearMap.range i.toIntLinearMap =
      Submodule.span ℤ (Set.range (IsIntegralLattice.realBasis i h)) := by
    rw [LinearMap.range_eq_map,
      ← (@Module.Free.chooseBasis ℤ N _ _ _ h.free).span_eq,
      Submodule.map_span, ← Set.range_comp]
    congr 1
    exact congrArg Set.range <| funext fun j ↦ by
      simp only [Function.comp_apply, IsIntegralLattice.realBasis_apply,
        AddMonoidHom.coe_toIntLinearMap]
  exact congrArg (fun p : Submodule ℤ V => (p : Set V)) hrange'

/-- The real span of the image of an integral lattice is the whole ambient space. -/
@[simp]
theorem IsIntegralLattice.span_range_eq_top (i : N →+ V) (h : IsIntegralLattice i) :
    Submodule.span ℝ (Set.range i) = ⊤ := by
  rw [IsIntegralLattice.range_eq_span_realBasis i h]
  rw [Submodule.span_span_of_tower]
  exact (IsIntegralLattice.realBasis i h).span_eq

/-- The rank of a full integral lattice equals the real dimension of its ambient space. -/
theorem IsIntegralLattice.finrank_eq_finrank (i : N →+ V) (h : IsIntegralLattice i) :
    Module.finrank ℤ N = Module.finrank ℝ V := by
  let _ : Module.Free ℤ N := h.free
  exact (TauCeti.finrank_of_isBaseChange h.baseChange).symm

variable {V₀ : Type w} [NormedAddCommGroup V₀] [NormedSpace ℝ V₀]

/-- Helper with the instances needed by the Mathlib discreteness theorem. -/
private theorem isDiscrete_range_of_instances [Module.Finite ℤ N]
    (i : N →+ V₀) (h : IsIntegralLattice i) :
    IsDiscrete (Set.range i) := by
  let b := IsIntegralLattice.realBasis i h
  have hd : DiscreteTopology (Submodule.span ℤ (Set.range b)) := by
    infer_instance
  rw [IsIntegralLattice.range_eq_span_realBasis i h]
  exact @DiscreteTopology.isDiscrete _ _ _ hd

/-- With its usual real-vector-space topology, the image of an integral lattice is discrete. -/
theorem IsIntegralLattice.isDiscrete_range (i : N →+ V₀)
    (h : IsIntegralLattice i) :
    IsDiscrete (Set.range i) :=
  @isDiscrete_range_of_instances N _ V₀ _ _ h.finite i h

/-- The image submodule of an integral lattice has the discrete topology. -/
theorem IsIntegralLattice.discreteTopology_range (i : N →+ V₀)
    (h : IsIntegralLattice i) :
    DiscreteTopology (LinearMap.range i.toIntLinearMap) := by
  apply SetLike.isDiscrete_iff_discreteTopology.mp
  simpa only [LinearMap.coe_range, AddMonoidHom.coe_toIntLinearMap] using
    IsIntegralLattice.isDiscrete_range i h

/-- The image submodule of an integral lattice is a Mathlib `IsZLattice`. -/
theorem IsIntegralLattice.isZLattice_range (i : N →+ V₀)
    (h : IsIntegralLattice i) :
    @IsZLattice ℝ _ V₀ _ _ (LinearMap.range i.toIntLinearMap)
      (IsIntegralLattice.discreteTopology_range i h) := by
  let _ : Module.Finite ℤ N := h.finite
  let b := IsIntegralLattice.realBasis i h
  have hrange : (LinearMap.range i.toIntLinearMap : Set V₀) =
      (Submodule.span ℤ (Set.range b) : Set V₀) := by
    simpa only [LinearMap.coe_range, AddMonoidHom.coe_toIntLinearMap] using
      IsIntegralLattice.range_eq_span_realBasis i h
  refine @IsZLattice.mk ℝ _ V₀ _ _ (LinearMap.range i.toIntLinearMap)
    (IsIntegralLattice.discreteTopology_range i h) ?_
  rw [hrange]
  exact (instIsZLatticeRealSpan b).span_top

/-- Compatibility on lattice vectors induces a commuting square between the scalar-extension
equivalences and the base change of the corresponding integral additive map. -/
theorem IsIntegralLattice.comp_equiv_eq_equiv_comp_baseChange
    {N' : Type u'} {V' : Type v'} [AddCommGroup N']
    [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hf : ∀ n, g (i n) = i' (f n)) :
    g.comp h.baseChange.equiv.toLinearMap =
      h'.baseChange.equiv.toLinearMap.comp (f.toIntLinearMap.baseChange ℝ) := by
  refine (TensorProduct.isBaseChange ℤ N ℝ).algHom_ext'
    (g.comp h.baseChange.equiv.toLinearMap)
    (h'.baseChange.equiv.toLinearMap.comp (f.toIntLinearMap.baseChange ℝ)) ?_
  ext n
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
    LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
  -- The preceding simplification unfolds the composition and base-change wrappers, but the
  -- coercions from `LinearEquiv.toLinearMap` and `AddMonoidHom.toIntLinearMap` still hide the
  -- tensor expressions from `equiv_tmul`; `change` exposes those definitional wrappers.
  change g (h.baseChange.equiv (1 ⊗ₜ[ℤ] n)) =
    h'.baseChange.equiv (1 ⊗ₜ[ℤ] f.toIntLinearMap n)
  rw [h.baseChange.equiv_tmul, h'.baseChange.equiv_tmul]
  simpa only [one_smul, AddMonoidHom.coe_toIntLinearMap] using hf n

end AddMonoidHom
