/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius
public import TauCeti.FieldTheory.Finite.SepClosedSubfield

/-!
# Fixed points of Frobenius on a Kostant toral closure

Let `G` be a closed subgroup of `GLₙ` obtained from the Kostant toral-closure construction. Over a
commutative ring `A` of exponential characteristic `p`, its `p ^ k`-power Frobenius fixes exactly
the matrices whose entries belong to `frobeniusFixedSubring A p k`. The subgroup equality proving
this is already available as
`TauCeti.UniversalEnvelopingAlgebra.map_subtype_fixedSubgroup_kostantToralFrobenius_eq`.

This file upgrades that equality inside `GLₙ(A)` to an isomorphism of the point groups themselves.
The forward map is entrywise inclusion from the fixed subring into `A`; injectivity is inherited
from that inclusion, and surjectivity is exactly the existing subgroup equality. Consequently, the
fixed-point group is finite whenever the fixed subring is finite. When `A` is a field of
characteristic `p` and `k` is nonzero, its fixed subring is the finite Frobenius-fixed subfield.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsFixedSubringMulEquiv`: the points over the
  Frobenius-fixed subring are isomorphic to the Frobenius-fixed points over `A`.
* `TauCeti.UniversalEnvelopingAlgebra.finite_fixedSubgroup_kostantToralFrobenius`: finiteness of the
  fixed subring implies finiteness of the fixed-point group.
* `TauCeti.UniversalEnvelopingAlgebra.finite_fixedSubgroup_kostantToralFrobenius_of_charP`: over a
  field of characteristic `p`, a nonzero Frobenius iterate has a finite fixed subgroup.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, §11.

This advances the Layer 9 target "Points over an algebraically closed field" in the
ReductiveGroups roadmap. It supplies the finiteness step for the fixed subgroups used in milestone
L3, "fixed points and the simple-group candidate", of the CFSGStatement roadmap.
-/

public section

open WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type}
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (p k : ℕ)

section FixedPoints

variable [Finite κ]
variable (A : Type v) [CommRing A] [ExpChar A p]

private theorem generalLinearMap_frobeniusFixedSubring_injective :
    Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin n) (frobeniusFixedSubring A p k).subtype) :=
  Units.map_injective (Matrix.map_injective Subtype.val_injective)

private theorem coe_equivMapOfInjective_symm_apply {G N : Type*} [Group G] [Group N]
    (H : Subgroup G) (f : G →* N) (hf : Function.Injective f) (x : H.map f) :
    f ((H.equivMapOfInjective f hf).symm x) = x := by
  rw [← Subgroup.coe_equivMapOfInjective_apply H f hf]
  exact congrArg Subtype.val ((H.equivMapOfInjective f hf).apply_symm_apply x)

/-- **Points of a Kostant toral closure over the Frobenius-fixed subring are isomorphic to the
Frobenius-fixed points over the ambient ring.**

Under this isomorphism a matrix over `frobeniusFixedSubring A p k` is sent to the same matrix with
its entries included into `A`. -/
noncomputable def kostantToralPointsFixedSubringMulEquiv :
    ↥(kostantToralPointsSubgroup e h ρ M hM hnil b wt ↥(frobeniusFixedSubring A p k)) ≃*
      ↥(fixedSubgroup (kostantToralFrobenius e h ρ M hM hnil b wt p k A)) :=
  let source :=
    kostantToralPointsSubgroup e h ρ M hM hnil b wt ↥(frobeniusFixedSubring A p k)
  let target := fixedSubgroup (kostantToralFrobenius e h ρ M hM hnil b wt p k A)
  let fixedRingMap :=
    Matrix.GeneralLinearGroup.map (n := Fin n) (frobeniusFixedSubring A p k).subtype
  (source.equivMapOfInjective fixedRingMap
      (generalLinearMap_frobeniusFixedSubring_injective (n := n) p k A)).trans
    ((MulEquiv.subgroupCongr
      (map_subtype_fixedSubgroup_kostantToralFrobenius_eq
        e h ρ M hM hnil b wt p k A).symm).trans
      (target.equivMapOfInjective
        (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).subtype
        (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).subtype_injective).symm)

/-- The fixed-point isomorphism is entrywise inclusion of matrices from the Frobenius-fixed
subring into the ambient ring. -/
@[simp]
theorem coe_kostantToralPointsFixedSubringMulEquiv
    (g : kostantToralPointsSubgroup e h ρ M hM hnil b wt ↥(frobeniusFixedSubring A p k)) :
    ((kostantToralPointsFixedSubringMulEquiv e h ρ M hM hnil b wt p k A g :
        kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
      Matrix.GeneralLinearGroup (Fin n) A) =
        Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype g := by
  rw [kostantToralPointsFixedSubringMulEquiv]
  let source :=
    kostantToralPointsSubgroup e h ρ M hM hnil b wt ↥(frobeniusFixedSubring A p k)
  let target := fixedSubgroup (kostantToralFrobenius e h ρ M hM hnil b wt p k A)
  let fixedRingMap :=
    Matrix.GeneralLinearGroup.map (n := Fin n) (frobeniusFixedSubring A p k).subtype
  let sourceEquiv := source.equivMapOfInjective fixedRingMap
    (generalLinearMap_frobeniusFixedSubring_injective (n := n) p k A)
  let targetEquiv := target.equivMapOfInjective
    (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).subtype
    (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).subtype_injective
  let middle := MulEquiv.subgroupCongr
    (map_subtype_fixedSubgroup_kostantToralFrobenius_eq
      e h ρ M hM hnil b wt p k A).symm
  exact calc
    (((targetEquiv.symm (middle (sourceEquiv g)) : target) :
        kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
          Matrix.GeneralLinearGroup (Fin n) A) = middle (sourceEquiv g) :=
      coe_equivMapOfInjective_symm_apply target
        (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).subtype
        (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).subtype_injective _
    _ = sourceEquiv g := MulEquiv.subgroupCongr_apply _ _
    _ = fixedRingMap g := Subgroup.coe_equivMapOfInjective_apply _ _ _ _

/-- Re-including the fixed-subring point recovered by the inverse fixed-point isomorphism gives
the original Frobenius-fixed point. -/
@[simp]
theorem coe_kostantToralPointsFixedSubringMulEquiv_symm
    (g : fixedSubgroup (kostantToralFrobenius e h ρ M hM hnil b wt p k A)) :
    Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype
        ((kostantToralPointsFixedSubringMulEquiv e h ρ M hM hnil b wt p k A).symm g) =
      ((g : kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
        Matrix.GeneralLinearGroup (Fin n) A) := by
  rw [← coe_kostantToralPointsFixedSubringMulEquiv]
  exact congrArg (fun x : fixedSubgroup
      (kostantToralFrobenius e h ρ M hM hnil b wt p k A) ↦
        ((x : kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
          Matrix.GeneralLinearGroup (Fin n) A))
      ((kostantToralPointsFixedSubringMulEquiv e h ρ M hM hnil b wt p k A).apply_symm_apply g)

/-- If the Frobenius-fixed subring is finite, then the Frobenius-fixed subgroup of every Kostant
toral closure is finite. -/
theorem finite_fixedSubgroup_kostantToralFrobenius
    [Finite ↥(frobeniusFixedSubring A p k)] :
    Finite ↥(fixedSubgroup (kostantToralFrobenius e h ρ M hM hnil b wt p k A)) :=
  Finite.of_equiv
    ↥(kostantToralPointsSubgroup e h ρ M hM hnil b wt ↥(frobeniusFixedSubring A p k))
    (kostantToralPointsFixedSubringMulEquiv e h ρ M hM hnil b wt p k A).toEquiv

end FixedPoints

section FiniteFixedPoints

variable [Finite κ]
variable (K : Type v) [Field K] [Fact p.Prime] [CharP K p]

/-- **A nonzero Frobenius iterate has a finite fixed subgroup on the points of every Kostant toral
closure over a field of characteristic `p`.**

The fixed subgroup is isomorphic to the carrier's points over the Frobenius-fixed subfield, which
is finite because it is the root set of `X ^ p ^ k - X`. -/
theorem finite_fixedSubgroup_kostantToralFrobenius_of_charP (hk : k ≠ 0) :
    Finite ↥(fixedSubgroup (kostantToralFrobenius e h ρ M hM hnil b wt p k K)) := by
  have hfixed : (frobeniusFixedSubfield K p k : Set K) =
      frobeniusFixedSubring K p k := by
    rw [← Subfield.coe_toSubring, toSubring_frobeniusFixedSubfield]
  let _ : Finite ↥(frobeniusFixedSubfield K p k) :=
    finite_frobeniusFixedSubfield K p k hk
  let _ : Finite ↥(frobeniusFixedSubring K p k) :=
    Finite.of_equiv ↥(frobeniusFixedSubfield K p k) (Equiv.setCongr hfixed)
  exact finite_fixedSubgroup_kostantToralFrobenius e h ρ M hM hnil b wt p k K

end FiniteFixedPoints

end TauCeti.UniversalEnvelopingAlgebra
