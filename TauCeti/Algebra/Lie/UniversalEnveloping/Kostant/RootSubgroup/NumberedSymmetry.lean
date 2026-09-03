/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Basic
public import TauCeti.RingTheory.Nilpotent.Conjugation

/-!
# Numbered symmetries of a Kostant elementary group

Let `U_ℤ = kostantForm e h` act on a rational representation `V` preserving an additive subgroup
`M ≤ V`, so that the divided-power exponentials of the distinguished root vectors `eᵢ` generate the
elementary group `E(A) ≤ Aut_A(A ⊗[ℤ] M)` of
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Basic`.

A *symmetry of the numbered data* is a surjective self-map `σ` of the index set together with a
`ℚ`-linear automorphism `θ` of `V` that preserves `M` and carries the action of `eᵢ` to the action
of `e_{σ i}`. Conjugating by the scalar extension of `θ` is then an automorphism of `E(A)` which
sends each root subgroup to the one indexed by `σ` without touching its parameters:

```text
γ (xᵢ(t)) = x_{σ i}(t).
```

These include the equations that a graph automorphism of a Chevalley group is pinned by, restricted
to the simple root subgroups, when the numbered symmetry comes from a Dynkin-diagram symmetry.
Here `γ` is *defined* from a symmetry of the underlying data rather than obtained from the
isomorphism theorem for pinned groups, and no uniqueness statement is claimed. Two further
properties are what a Steinberg endomorphism built from `γ` needs. The
automorphism commutes with every base change of the value ring, hence in particular with the
`q`-power Frobenius endomorphism of `E(A)`; and if `θ ^ n = 1` then `γ ^ n = 1`, so an involution
or a triality of the numbered data produces a `γ` with `γ ^ 2 = 1` or `γ ^ 3 = 1`.

Nothing here assumes that `σ` is induced by a symmetry of a Dynkin diagram, nor that `θ` is unique:
both are supplied by the caller as data, and the intertwining hypothesis is the whole input.

## Main declarations

* `baseChangeInvariantRestrictUnit_conj_kostantRootSubgroupParam`:
  the pinning equation `γ (xᵢ(t)) = x_{σ i}(t)`.
* `map_kostantElementarySubgroup_conj`: the conjugation
  preserves the elementary group.
* `kostantElementaryNumberedSymmetryAut`: the resulting
  automorphism, with `kostantElementaryNumberedSymmetryAut_pow_eq_one` for its order.
* `kostantElementaryMap_kostantElementaryNumberedSymmetryAut` and
  `kostantElementaryFrobenius_kostantElementaryNumberedSymmetryAut`:
  commutation with base change of the value ring and with Frobenius.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

open AddEquiv

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type*} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (σ : I → I) (θ : V ≃ₗ[ℚ] V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M)
variable (hθe : ∀ i, ∀ v : V,
  θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) v) =
    ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (σ i))) (θ v))
variable (hσ : Function.Surjective σ)

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-! ## The pinning equation -/

include hθe in
/-- Conjugation by the scalar extension of `θ` carries the root subgroup at `i` to the root
subgroup at `σ i`, leaving the parameter untouched.

This is the multiplicative form of the pinning equation; the conjugated form is
`baseChangeInvariantRestrictUnit_conj_kostantRootSubgroupParam`. -/
theorem baseChangeInvariantRestrictUnit_mul_kostantRootSubgroupParam (A : CommAlgCat.{w} ℤ) (i : I)
    (t : Multiplicative A) :
    baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM *
        kostantRootSubgroupParam e h ρ M hM i (hnil i) A t =
      kostantRootSubgroupParam e h ρ M hM (σ i) (hnil (σ i)) A t *
        baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM := by
  have hk : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ^
      nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) = 0 :=
    pow_nilpotencyClass (hnil i)
  have hint : ∀ v : V,
      θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) • v) =
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (σ i))) • θ v :=
    fun v => by simpa only [Module.End.smul_def] using hθe i v
  have hY : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (σ i))) =
      θ.conjAlgEquiv ℚ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) := by
    ext v
    simpa [LinearEquiv.conjAlgEquiv_apply] using (hθe i (θ.symm v)).symm
  have hky : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (σ i))) ^
      nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) = 0 := by
    rw [hY, ← map_pow, hk, map_zero]
  refine Units.ext (LinearMap.ext fun z => ?_)
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    kostantRootSubgroupParam_val_apply, kostantRootSubgroupParam_val_apply,
    val_baseChangeInvariantRestrictUnit_apply, val_baseChangeInvariantRestrictUnit_apply]
  exact baseChange_invariantRestrict_baseChangeExp θ M hθM hint _ hk hky _ z

include hθe in
/-- The pinning equation for a numbered symmetry: conjugation by the scalar extension of `θ`
sends `xᵢ(t)` to `x_{σ i}(t)`. -/
theorem baseChangeInvariantRestrictUnit_conj_kostantRootSubgroupParam (A : CommAlgCat.{w} ℤ) (i : I)
    (t : Multiplicative A) :
    baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM *
        kostantRootSubgroupParam e h ρ M hM i (hnil i) A t *
        (baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM)⁻¹ =
      kostantRootSubgroupParam e h ρ M hM (σ i) (hnil (σ i)) A t := by
  rw [baseChangeInvariantRestrictUnit_mul_kostantRootSubgroupParam e h ρ M hM hnil σ θ hθM hθe,
    mul_assoc, mul_inv_cancel, mul_one]

/-! ## The automorphism of the elementary group -/

include hθe hσ in
/-- Conjugation by the scalar extension of `θ` preserves the elementary group.

Both inclusions come from the pinning equation: the generators at `i` go to the generators at
`σ i`, and every generator is hit because `σ` is surjective. -/
theorem map_kostantElementarySubgroup_conj (A : CommAlgCat.{w} ℤ) :
    (kostantElementarySubgroup e h ρ M hM hnil A).map
        (MulAut.conj (baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM) : _ →* _) =
      kostantElementarySubgroup e h ρ M hM hnil A := by
  have hconj : ∀ (i : I) (t : Multiplicative A),
      (MulAut.conj (baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM) : _ →* _)
          (kostantRootSubgroupParam e h ρ M hM i (hnil i) A t) =
        kostantRootSubgroupParam e h ρ M hM (σ i) (hnil (σ i)) A t := fun i t =>
    baseChangeInvariantRestrictUnit_conj_kostantRootSubgroupParam
      e h ρ M hM hnil σ θ hθM hθe A i t
  exact map_kostantElementarySubgroup_eq_of_map_param_of_surjective
    e h ρ M hM hnil _ σ id hconj hσ Function.surjective_id

/-- The automorphism of the elementary group attached to a symmetry `(σ, θ)` of the numbered
Kostant data: conjugation by the scalar extension of `θ`. -/
noncomputable def kostantElementaryNumberedSymmetryAut (A : CommAlgCat.{w} ℤ) :
    MulAut (kostantElementarySubgroup e h ρ M hM hnil A) :=
  (MulEquiv.subgroupMap (MulAut.conj
      (baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM))
      (kostantElementarySubgroup e h ρ M hM hnil A)).trans
    (MulEquiv.subgroupCongr
      (map_kostantElementarySubgroup_conj e h ρ M hM hnil σ θ hθM hθe hσ A))

/-- The numbered symmetry acts by conjugation inside the ambient automorphism group. -/
@[simp]
theorem val_kostantElementaryNumberedSymmetryAut (A : CommAlgCat.{w} ℤ)
    (g : kostantElementarySubgroup e h ρ M hM hnil A) :
    (kostantElementaryNumberedSymmetryAut e h ρ M hM hnil σ θ hθM hθe hσ A g :
        LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)) =
      baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM *
          (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)) *
        (baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM)⁻¹ := by
  -- Traverse each equivalence wrapper explicitly; this formula should not depend on their
  -- definitional transparency.
  rw [kostantElementaryNumberedSymmetryAut, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]

/-- The numbered symmetry sends the root subgroup at `i` to the one at `σ i`, leaving parameters
untouched. -/
@[simp]
theorem kostantElementaryNumberedSymmetryAut_kostantRootSubgroupParam
    (A : CommAlgCat.{w} ℤ) (i : I)
    (t : Multiplicative A) :
    kostantElementaryNumberedSymmetryAut e h ρ M hM hnil σ θ hθM hθe hσ A
        ⟨kostantRootSubgroupParam e h ρ M hM i (hnil i) A t,
          kostantRootSubgroupParam_mem_kostantElementarySubgroup e h ρ M hM hnil A i t⟩ =
      ⟨kostantRootSubgroupParam e h ρ M hM (σ i) (hnil (σ i)) A t,
        kostantRootSubgroupParam_mem_kostantElementarySubgroup e h ρ M hM hnil A (σ i) t⟩ := by
  apply Subtype.ext
  rw [val_kostantElementaryNumberedSymmetryAut,
    baseChangeInvariantRestrictUnit_conj_kostantRootSubgroupParam e h ρ M hM hnil σ θ hθM hθe]

/-- A numbered symmetry of order `n` produces an automorphism of order dividing `n`.

This is what makes the order relations `γ ^ 2 = 1` and `γ ^ 3 = 1` available for the graph-twisted
families, where `θ` realizes an involution or a triality of the numbered data. -/
theorem kostantElementaryNumberedSymmetryAut_pow_eq_one (A : CommAlgCat.{w} ℤ) {n : ℕ}
    (hn : ∀ v, (θ ^ n) v = v) :
    kostantElementaryNumberedSymmetryAut e h ρ M hM hnil σ θ hθM hθe hσ A ^ n = 1 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  have hpow : ∀ m : ℕ, ∀ g : kostantElementarySubgroup e h ρ M hM hnil A,
      ((kostantElementaryNumberedSymmetryAut e h ρ M hM hnil σ θ hθM hθe hσ A ^ m) g :
          LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)) =
        baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM ^ m *
          (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)) *
          (baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro g; simp
    | succ m ih =>
        intro g
        rw [pow_succ', MulAut.mul_apply, val_kostantElementaryNumberedSymmetryAut, ih g, pow_succ']
        group
  have hn' : ∀ v, (θ.toAddEquiv.toIntLinearEquiv ^ n) v = v := by
    intro v
    have hpowθ : ∀ m : ℕ, ∀ w : V,
        (θ.toAddEquiv.toIntLinearEquiv ^ m) w = (θ ^ m) w := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          intro w
          rw [pow_succ, LinearEquiv.mul_apply, pow_succ, LinearEquiv.mul_apply, ih]
          rfl
    exact (hpowθ n v).trans (hn v)
  rw [hpow n g, baseChangeInvariantRestrictUnit_pow_eq_one θ.toAddEquiv M hθM hn', one_mul,
    inv_one, mul_one]
  rfl

/-! ## Compatibility with base change and Frobenius -/

/-- The numbered symmetry commutes with base change of the value ring.

The scalar extension of `θ` is defined over `ℤ`, so extending scalars along `φ` leaves it
unchanged, and conjugation by it is therefore natural. -/
theorem kostantElementaryMap_kostantElementaryNumberedSymmetryAut
    {A B : CommAlgCat.{w} ℤ} (φ : A ⟶ B)
    (g : kostantElementarySubgroup e h ρ M hM hnil A) :
    kostantElementaryMap e h ρ M hM hnil φ
        (kostantElementaryNumberedSymmetryAut e h ρ M hM hnil σ θ hθM hθe hσ A g) =
      kostantElementaryNumberedSymmetryAut e h ρ M hM hnil σ θ hθM hθe hσ B
        (kostantElementaryMap e h ρ M hM hnil φ g) := by
  refine Subtype.ext ?_
  rw [val_kostantElementaryMap, val_kostantElementaryNumberedSymmetryAut,
    val_kostantElementaryNumberedSymmetryAut,
    val_kostantElementaryMap, map_mul, map_mul, map_inv,
    AddEquiv.mapScalarExtensionAutomorphisms_baseChangeInvariantRestrictUnit
      θ.toAddEquiv M hθM φ]

/-- The numbered symmetry commutes with the `p ^ n`-power Frobenius endomorphism.

Together with the pinning equation and the order relation, this is the compatibility a Steinberg
endomorphism of the form `γ ∘ Frob_q` is built from. -/
theorem kostantElementaryFrobenius_kostantElementaryNumberedSymmetryAut
    (p n : ℕ) (A : CommAlgCat.{w} ℤ)
    [ExpChar A p] (g : kostantElementarySubgroup e h ρ M hM hnil A) :
    kostantElementaryFrobenius e h ρ M hM hnil p n A
        (kostantElementaryNumberedSymmetryAut e h ρ M hM hnil σ θ hθM hθe hσ A g) =
      kostantElementaryNumberedSymmetryAut e h ρ M hM hnil σ θ hθM hθe hσ A
        (kostantElementaryFrobenius e h ρ M hM hnil p n A g) := by
  rw [kostantElementaryFrobenius_eq_kostantElementaryMap]
  exact kostantElementaryMap_kostantElementaryNumberedSymmetryAut
    e h ρ M hM hnil σ θ hθM hθe hσ (iterateFrobeniusValueHom p n A) g

end TauCeti.UniversalEnvelopingAlgebra
