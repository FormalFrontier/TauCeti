/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Torus

/-!
# The pinning equation in a toral-subsystem group scheme

A toral-subsystem group scheme indexed by `S` is the closed subgroup scheme of `GLₙ` generated
jointly by a represented split torus and the represented root subgroups selected by `S`. Both
kinds of generators factor through that carrier, but the equation relating them was previously
available only after mapping back into `GL_n`:

```text
t(s) x_i(u) t(s)⁻¹ = x_i(α(s) u).
```

This file proves the equation intrinsically in the toral carrier, on points over every commutative
ring. The proof uses the closed immersion into `GL_n` only to reflect equality. Its input is the
mathematical weight equation `[h_j, e_i] = α_j e_i`; no compatibility is added as an
assumption on the constructed group scheme.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.
  kostantWeightTorusToToralSubsystem_mul_kostantRootSubgroupToToralSubsystem`: the intertwining form
  `t(s) x_i(u) = x_i(α(s) u) t(s)`.
* `TauCeti.UniversalEnvelopingAlgebra.
  kostantWeightTorusToToralSubsystem_conj_kostantRootSubgroupToToralSubsystem`: the conjugation
  form of the pinning equation.
* `TauCeti.UniversalEnvelopingAlgebra.
  kostantWeightTorusToToralSubsystem_conj_kostantRootSubgroupToToralSubsystemParam`: the same
  equation with its root-subgroup parameter read directly in the value ring.

## References

This is the torus--root-subgroup compatibility equation intended for the future pinning of the
Chevalley--Demazure group scheme; see J. E. Humphreys, *Linear Algebraic Groups*, Section 26, and
R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1. It advances the Pinnings and Root
subgroup maps targets of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by
milestone L0 of the CFSGStatement roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Fintype κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (S : Set I)
variable (hnil : ∀ i ∈ S, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
variable (A : Type) [CommRing A]

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

include hwt

/-- **The pinning equation in a toral-subsystem carrier indexed by `S`, in intertwining form.** If
`e_i` has Cartan weight `α`, then a torus point `s` and root-subgroup parameters `u`, `v`
satisfying `v = α(s) u` obey `t(s) x_i(u) = x_i(v) t(s)` inside that carrier.

The statement is on points over an arbitrary commutative ring. The parameter equation is stated
through the canonical scheme-point coordinates of the split torus and additive group. -/
theorem kostantWeightTorusToToralSubsystem_mul_kostantRootSubgroupToToralSubsystem
    (i : S) {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i.1⁆ = (α j : ℚ) • e i.1)
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ κ).X)
    (u v : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hv : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A v) =
      (torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s) α : A) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A u)) :
    (s ≫ (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil).hom.hom) *
        (u ≫ (kostantRootSubgroupToToralSubsystem e h ρ M hM b wt S hnil i).hom.hom) =
      (v ≫ (kostantRootSubgroupToToralSubsystem e h ρ M hM b wt S hnil i).hom.hom) *
        (s ≫ (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil).hom.hom) := by
  let _ : Mono (kostantToralSubsystemGroupSchemeι e h ρ M hM b wt S hnil).hom.hom :=
    Over.mono_of_mono_left _
  let f := IsMonHom.monoidHom
    (kostantToralSubsystemGroupSchemeι e h ρ M hM b wt S hnil).hom.hom
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)))
  have hf : Function.Injective f := by
    intro p q hpq
    exact (cancel_mono (kostantToralSubsystemGroupSchemeι e h ρ M hM b wt S hnil).hom.hom).1 hpq
  apply hf
  dsimp only [f]
  simp only [map_mul, IsMonHom.monoidHom_apply, Category.assoc, ← Grp.comp_hom_hom,
    kostantWeightTorusToToralSubsystem_comp_ι,
    kostantRootSubgroupToToralSubsystem_comp_ι]
  apply (GeneralLinear.schemePointsMulEquiv n A).injective
  simp only [map_mul]
  rw [schemePointsMulEquiv_weightTorus_eq_kostantTorusMatrix M b wt A,
    schemePointsMulEquiv_kostantRootSubgroup, schemePointsMulEquiv_kostantRootSubgroup]
  let q := (AdditiveGroup.groupSchemePointMulEquiv A).symm u
  let r := (AdditiveGroup.groupSchemePointMulEquiv A).symm v
  have hv' :
      Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
        (torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s) α : A) *
          Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) := by
    simpa only [q, r, AdditiveGroup.schemePointsMulEquiv_apply] using hv
  have hpin := kostantTorusPoints_mul_kostantRootSubgroupPoints
    e h ρ M hM b wt hwt hα (hnil i.1 i.2)
    (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s) q r hv'
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom) hpin
  rw [← basisMatrix_kostantTorusPoints, kostantRootSubgroupMatrix_def,
    MonoidHom.comp_apply, MonoidHom.comp_apply]
  simpa only [map_mul, q, r, MulEquiv.toMonoidHom_eq_coe] using hmatrix

/-- **The pinning equation in a toral-subsystem carrier indexed by `S`.** Conjugation by the torus
point `t(s)` sends the `i`th selected root-subgroup point with parameter `u` to the same root
subgroup with parameter `α(s) u`, where `α` is the Cartan weight of `e_i`.

This is the intrinsic equation later diagram automorphisms and Steinberg maps are normalized
against; it no longer mentions the embedding of the constructed carrier into `GL_n`. -/
@[simp]
theorem kostantWeightTorusToToralSubsystem_conj_kostantRootSubgroupToToralSubsystem
    (i : S) {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i.1⁆ = (α j : ℚ) • e i.1)
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ κ).X)
    (u : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    (s ≫ (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil).hom.hom) *
        (u ≫ (kostantRootSubgroupToToralSubsystem e h ρ M hM b wt S hnil i).hom.hom) *
        (s ≫ (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s) α : A) *
              Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A u))) ≫
        (kostantRootSubgroupToToralSubsystem e h ρ M hM b wt S hnil i).hom.hom := by
  rw [mul_inv_eq_iff_eq_mul]
  apply kostantWeightTorusToToralSubsystem_mul_kostantRootSubgroupToToralSubsystem
    e h ρ M hM b wt S hnil hwt A i hα s u
  exact congrArg Multiplicative.toAdd
    ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _)

/-- **The pinning equation with the root-subgroup parameter read in the value ring.**
Conjugation by `t(s)` sends `x_i(u)` to `x_i(α(s) u)` inside the toral-subsystem carrier indexed
by `S`. -/
@[simp]
theorem kostantWeightTorusToToralSubsystem_conj_kostantRootSubgroupToToralSubsystemParam
    (i : S) {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i.1⁆ = (α j : ℚ) • e i.1)
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ κ).X)
    (u : A) :
    (s ≫ (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd u)) ≫
          (kostantRootSubgroupToToralSubsystem e h ρ M hM b wt S hnil i).hom.hom) *
        (s ≫ (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s) α : A) * u)) ≫
        (kostantRootSubgroupToToralSubsystem e h ρ M hM b wt S hnil i).hom.hom := by
  rw [← AdditiveGroup.schemePointsMulEquiv_symm_apply]
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
    kostantWeightTorusToToralSubsystem_conj_kostantRootSubgroupToToralSubsystem
    e h ρ M hM b wt S hnil hwt A i hα s
      ((AdditiveGroup.schemePointsMulEquiv A).symm (Multiplicative.ofAdd u))

end TauCeti.UniversalEnvelopingAlgebra
