/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Conjugation and maps on complexifications of integral modules

This file packages a conjugation on a complex vector space as a conjugate-linear involution and
constructs the canonical conjugation on any abstract complexification of an integral module.
The construction uses Mathlib's `IsBaseChange` interface: it transports coordinatewise conjugation
on `ℂ ⊗[ℤ] V` to an arbitrary complex base-change model and is uniquely characterized by fixing the
image of `V`. The same interface canonically complexifies integral linear maps between abstract
complexification models.

## Main declarations

* `TauCeti.Hodge.Conjugation`: a conjugate-linear involution of a complex vector space.
* `TauCeti.Hodge.Conjugation.conjFiltration`: the conjugate of a complex filtration.
* `TauCeti.Hodge.concreteLatticeConj`: conjugation on the tensor model `ℂ ⊗[ℤ] V`.
* `TauCeti.Hodge.latticeConj`: conjugation on an abstract complex base-change model.
* `TauCeti.Hodge.latticeConj_unique`: uniqueness among conjugate-linear maps fixing the integral
  module.
* `TauCeti.Hodge.Conjugation.restrict`: the conjugation induced on a stable complex subspace.
* `TauCeti.Hodge.Conjugation.quotient`: the conjugation induced on the quotient by a stable
  complex subspace.
* `TauCeti.Hodge.Conjugation.map_comap_eq_comap_map`: an equivalence intertwining two conjugations
  exchanges conjugation with taking preimages of subspaces.
* `TauCeti.Hodge.Conjugation.dual`: the twisted transpose of a conjugation, again a conjugation,
  on the complex dual space, with its pointwise description
  `TauCeti.Hodge.Conjugation.dual_toEquiv_apply`.
* `TauCeti.Hodge.Conjugation.map_dualAnnihilator`: a conjugation carries dual annihilators to
  dual annihilators of conjugated subspaces.
* `TauCeti.Hodge.latticeConjugation`: the abstract map bundled as a `Conjugation`.
* `TauCeti.Hodge.integralMapToComplex`: complexification of an integral linear map between abstract
  complexification models.

The base-change design follows the Hodge structures roadmap and the discussion by Johan Commelin,
Andrew Yang, Kevin Buzzard, and Joël Riou in the `#mathlib4` Zulip thread *Complexifications with a
view towards Hodge theory*. The opposed-filtration formulation that consumes this conjugation is
Deligne's, *Théorie de Hodge II*, §1.2.1.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v

/-- A conjugation on a complex vector space: a conjugate-linear involution. -/
@[ext]
structure Conjugation (W : Type u) [AddCommGroup W] [Module ℂ W] where
  /-- The conjugate-linear equivalence underlying the conjugation. -/
  toEquiv : W ≃ₛₗ[starRingEnd ℂ] W
  /-- Applying the conjugation twice is the identity. -/
  involutive : Function.Involutive toEquiv

namespace Conjugation

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

/-- The inverse of a conjugation is the conjugation itself. -/
@[simp]
theorem toEquiv_symm (ω : Conjugation W) : ω.toEquiv.symm = ω.toEquiv := by
  ext x
  apply ω.toEquiv.injective
  simp [ω.involutive x]

/-- Applying a conjugation twice returns the original vector. -/
@[simp]
theorem apply_apply (ω : Conjugation W) (x : W) : ω.toEquiv (ω.toEquiv x) = x :=
  ω.involutive x

/-- Mapping a complex subspace twice by a conjugation returns the original subspace. -/
@[simp]
theorem map_map_eq_self (ω : Conjugation W) (U : Submodule ℂ W) :
    (U.map ω.toEquiv.toLinearMap).map ω.toEquiv.toLinearMap = U := by
  have h : (U.map ω.toEquiv.toLinearMap).map ω.toEquiv.symm.toLinearMap = U :=
    (Submodule.map_symm_eq_iff ω.toEquiv).2 rfl
  simpa only [ω.toEquiv_symm] using h

/-- The conjugate filtration obtained by mapping each step through a conjugation. -/
noncomputable def conjFiltration (ω : Conjugation W) (F : ℤ → Submodule ℂ W) (p : ℤ) :
    Submodule ℂ W :=
  (F p).map ω.toEquiv.toLinearMap

/-- A conjugate filtration step is the image of the original step under conjugation. -/
theorem conjFiltration_def (ω : Conjugation W) (F : ℤ → Submodule ℂ W) (p : ℤ) :
    ω.conjFiltration F p = (F p).map ω.toEquiv.toLinearMap :=
  (rfl)

/-- Conjugating an antitone filtration produces an antitone filtration. -/
theorem conjFiltration_antitone (ω : Conjugation W) {F : ℤ → Submodule ℂ W}
    (hF : Antitone F) : Antitone (ω.conjFiltration F) :=
  fun _ _ hpq ↦ Submodule.map_mono (hF hpq)

/-- Membership in a conjugate filtration step is detected by applying the conjugation. -/
@[simp]
theorem mem_conjFiltration_iff (ω : Conjugation W) (F : ℤ → Submodule ℂ W) (p : ℤ) (x : W) :
    x ∈ ω.conjFiltration F p ↔ ω.toEquiv x ∈ F p := by
  simp [conjFiltration, ω.toEquiv_symm]

/-- Applying conjugation to a conjugate filtration step recovers the original step. -/
@[simp]
theorem conjFiltration_conjFiltration (ω : Conjugation W) (F : ℤ → Submodule ℂ W) (p : ℤ) :
    (ω.conjFiltration F p).map ω.toEquiv.toLinearMap = F p :=
  ω.map_map_eq_self (F p)

variable {W' : Type v} [AddCommGroup W'] [Module ℂ W']

/-- A linear map commuting with two conjugations carries the conjugate of a preserved filtration
step into the corresponding conjugate filtration step. -/
theorem map_conjFiltration_le (ω : Conjugation W) (ω' : Conjugation W')
    (F : ℤ → Submodule ℂ W) (F' : ℤ → Submodule ℂ W') (f : W →ₗ[ℂ] W')
    (hcomm : ∀ x, f (ω.toEquiv x) = ω'.toEquiv (f x)) {p : ℤ}
    (hF : (F p).map f ≤ F' p) :
    (ω.conjFiltration F p).map f ≤ ω'.conjFiltration F' p := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨f x, hF ⟨x, hx, rfl⟩, (hcomm x).symm⟩

/-- A conjugation restricted to a stable complex subspace is involutive. -/
private theorem restrict_involutive (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) :
    Function.Involutive (ω.toEquiv.toLinearMap.restrict hU) := fun x ↦ by
  ext
  simp

/-- The conjugation induced on a complex subspace stable under a given conjugation. -/
noncomputable def restrict (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) : Conjugation U where
  toEquiv := LinearEquiv.ofInvolutive _ (ω.restrict_involutive hU)
  involutive := ω.restrict_involutive hU

/-- A restricted conjugation acts as the ambient one. -/
@[simp]
theorem restrict_toEquiv_apply (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) (x : U) :
    ((ω.restrict hU).toEquiv x : W) = ω.toEquiv x :=
  (rfl)

/-- Conjugating inside a stable subspace is conjugating in the ambient space: the image of an
intersection with the subspace under the restricted conjugation is the intersection with the
conjugate subspace. -/
@[simp]
theorem map_restrict_comap_subtype (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) (A : Submodule ℂ W) :
    (A.comap U.subtype).map (ω.restrict hU).toEquiv.toLinearMap =
      (A.map ω.toEquiv.toLinearMap).comap U.subtype := by
  ext x
  simp

/-- A linear equivalence intertwining two conjugations exchanges conjugating a preimage with
taking the preimage of the conjugate. -/
theorem map_comap_eq_comap_map {W' : Type v} [AddCommGroup W'] [Module ℂ W']
    (ω : Conjugation W) (ω' : Conjugation W') (e : W ≃ₗ[ℂ] W')
    (he : ∀ x, e (ω.toEquiv x) = ω'.toEquiv (e x)) (A : Submodule ℂ W') :
    (A.comap e.toLinearMap).map ω.toEquiv.toLinearMap =
      (A.map ω'.toEquiv.toLinearMap).comap e.toLinearMap := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, hx, (he x).symm⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨ω.toEquiv y, ?_, ω.apply_apply y⟩
    rw [he y, ← hzy, ω'.apply_apply]
    exact hz

/-- The conjugation induced on a quotient by a stable complex subspace is involutive. -/
private theorem quotient_involutive (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) :
    Function.Involutive (U.mapQ U ω.toEquiv.toLinearMap fun x hx ↦ hU x hx) := fun x ↦
  Submodule.Quotient.induction_on _ x fun y ↦
    congrArg Submodule.Quotient.mk (ω.apply_apply y)

/-- The conjugation induced on the quotient of a complex vector space by a stable subspace. -/
noncomputable def quotient (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) : Conjugation (W ⧸ U) where
  toEquiv := LinearEquiv.ofInvolutive _ (ω.quotient_involutive hU)
  involutive := ω.quotient_involutive hU

/-- The induced conjugation on a quotient acts on classes through the ambient conjugation. -/
@[simp]
theorem quotient_toEquiv_mk (ω : Conjugation W) {U : Submodule ℂ W}
    (hU : ∀ x ∈ U, ω.toEquiv x ∈ U) (x : W) :
    (ω.quotient hU).toEquiv (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ω.toEquiv x) :=
  (rfl)

/-- The twisted transpose of a conjugation: a functional `φ` is sent to the functional
conjugating the values of `φ` along `ω`. -/
private def dualMap (ω : Conjugation W) :
    Module.Dual ℂ W →ₛₗ[starRingEnd ℂ] Module.Dual ℂ W :=
  { toFun := fun φ =>
      { toFun := fun v => star (φ (ω.toEquiv v))
        map_add' := by
          intro x y
          simp [map_add, star_add]
        map_smul' := by
          intro c v
          have h1 : ω.toEquiv (c • v) = (starRingEnd ℂ) c • ω.toEquiv v :=
            LinearMap.map_smulₛₗ ω.toEquiv.toLinearMap c v
          have h2 : φ ((starRingEnd ℂ) c • ω.toEquiv v) =
              (starRingEnd ℂ) c * φ (ω.toEquiv v) := by simp
          rw [h1, h2]
          simp [star_mul, mul_comm] }
    map_add' := by
      intro φ ψ
      ext v
      simp
    map_smul' := by
      intro c φ
      ext v
      simp }

/-- Pointwise description of the twisted transpose. -/
private theorem dualMap_apply (ω : Conjugation W) (φ : Module.Dual ℂ W) (v : W) :
    dualMap ω φ v = star (φ (ω.toEquiv v)) :=
  (rfl)

/-- The twisted transpose is an involution. -/
private theorem dualMap_involutive (ω : Conjugation W) :
    Function.Involutive (dualMap ω) := by
  intro φ
  ext v
  simp [dualMap_apply, ω.apply_apply]

/-- The twisted transpose of a conjugation `ω`: a functional `φ` acts by conjugating the values
of `φ` along `ω`. It is again an involution, so it packages as a conjugation on the dual space;
see `TauCeti.Hodge.Conjugation.dual_toEquiv_apply` for its pointwise description. -/
def dual (ω : Conjugation W) : Conjugation (Module.Dual ℂ W) where
  toEquiv :=
    { toFun := dualMap ω
      invFun := dualMap ω
      left_inv := dualMap_involutive ω
      right_inv := dualMap_involutive ω
      map_add' := by
        intro φ ψ
        ext v
        simp [map_add]
      map_smul' := by
        intro c φ
        ext v
        simp [dualMap_apply] }
  involutive := dualMap_involutive ω

/-- Pointwise description of the dual conjugation. -/
@[simp]
theorem dual_toEquiv_apply (ω : Conjugation W) (φ : Module.Dual ℂ W) (v : W) :
    ω.dual.toEquiv φ v = star (φ (ω.toEquiv v)) :=
  (rfl)

/-- A conjugation carries dual annihilators to dual annihilators of conjugated subspaces. -/
@[simp]
theorem map_dualAnnihilator (ω : Conjugation W) (U : Submodule ℂ W) :
    U.dualAnnihilator.map ω.dual.toEquiv.toLinearMap =
      (U.map ω.toEquiv.toLinearMap).dualAnnihilator := by
  ext φ
  rw [Submodule.mem_dualAnnihilator, Submodule.mem_map]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩ u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
    have hψ' : ∀ w ∈ U, ψ w = 0 := (Submodule.mem_dualAnnihilator ψ).mp hψ
    -- `LinearEquiv.coe_toLinearMap` exposes the underlying functions (one rewrite per
    -- occurrence), so that the pointwise description `dual_toEquiv_apply` applies to the goal.
    rw [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, dual_toEquiv_apply,
      ω.apply_apply, hψ' v hv]
    exact star_zero _
  · intro h
    refine ⟨ω.dual.toEquiv φ,
      (Submodule.mem_dualAnnihilator (ω.dual.toEquiv φ)).mpr fun u hu => ?_, ?_⟩
    · have h0 : φ (ω.toEquiv u) = 0 :=
        h (ω.toEquiv u) (Submodule.mem_map.2 ⟨u, hu, rfl⟩)
      rw [dual_toEquiv_apply, h0]
      exact star_zero _
    · ext v
      exact congrArg (fun f => f v) (ω.dual.apply_apply φ)

end Conjugation

section Concrete

variable {V : Type u} [AddCommGroup V]

/-- The canonical complexification `ℂ ⊗[ℤ] V` of an integral module. -/
abbrev Complexification (V : Type u) [AddCommGroup V] :=
  TensorProduct ℤ ℂ V

/-- The canonical map from an integral module to its tensor-product complexification. -/
def complexificationMap : V →ₗ[ℤ] Complexification V :=
  (TensorProduct.mk ℤ ℂ V) 1

/-- The tensor-product complexification satisfies the abstract base-change interface. -/
theorem isBaseChange_complexificationMap :
    IsBaseChange ℂ (complexificationMap (V := V)) :=
  TensorProduct.isBaseChange ℤ V ℂ

/-- The integral-linear map underlying conjugation on the tensor-product complexification. -/
private noncomputable def concreteLatticeConjIntLinear :=
  TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
    (LinearMap.id : V →ₗ[ℤ] V)

/-- Lattice-induced conjugation on the tensor model `ℂ ⊗[ℤ] V`, acting by complex conjugation on
the scalar tensor factor and by the identity on the integral module. -/
noncomputable def concreteLatticeConj :
    Complexification V →ₛₗ[starRingEnd ℂ] Complexification V where
  toFun := concreteLatticeConjIntLinear
  map_add' := concreteLatticeConjIntLinear.map_add
  map_smul' c x := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro z v
      simp only [TensorProduct.smul_tmul']
      unfold concreteLatticeConjIntLinear
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp [map_mul, TensorProduct.smul_tmul']
    · intro x y hx hy
      simp [map_add, hx, hy]

/-- Conjugation on the tensor model conjugates the scalar in a pure tensor. -/
@[simp]
theorem concreteLatticeConj_tmul (z : ℂ) (v : V) :
    concreteLatticeConj (V := V) (z ⊗ₜ[ℤ] v) = (starRingEnd ℂ z) ⊗ₜ[ℤ] v :=
  by
    -- The tensor map is `ℤ`-linear while the bundled result is conjugate-linear over `ℂ`, so the
    -- public pure-tensor equation is the stable bridge between the two scalar interfaces.
    change concreteLatticeConjIntLinear (z ⊗ₜ[ℤ] v) = _
    unfold concreteLatticeConjIntLinear
    rw [TensorProduct.map_tmul]
    simp

/-- Conjugation on the tensor model fixes the image of the integral module. -/
@[simp]
theorem concreteLatticeConj_complexificationMap (v : V) :
    concreteLatticeConj (complexificationMap v) = complexificationMap v := by
  -- `Complexification V` has both the tensor-product and canonical integer-module instances;
  -- restating the goal as a pure tensor avoids exposing that harmless instance diamond.
  change concreteLatticeConj (1 ⊗ₜ[ℤ] v) = 1 ⊗ₜ[ℤ] v
  simpa only [map_one] using concreteLatticeConj_tmul (V := V) 1 v

private theorem concreteLatticeConjIntLinear_comp :
    concreteLatticeConjIntLinear (V := V) ∘ₗ concreteLatticeConjIntLinear = LinearMap.id := by
  unfold concreteLatticeConjIntLinear
  rw [← TensorProduct.map_comp]
  have hstar : (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap ∘ₗ
      (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap = LinearMap.id := by
    ext z
    simp
  rw [hstar]
  exact TensorProduct.map_id

/-- Conjugation on the tensor model is involutive. -/
theorem concreteLatticeConj_involutive :
    Function.Involutive (concreteLatticeConj (V := V)) := by
  intro x
  exact LinearMap.congr_fun (concreteLatticeConjIntLinear_comp (V := V)) x

/-- Applying conjugation on the tensor model twice returns the original vector. -/
@[simp]
theorem concreteLatticeConj_apply_apply (x : Complexification V) :
    concreteLatticeConj (concreteLatticeConj x) = x :=
  concreteLatticeConj_involutive x

end Concrete

section Abstract

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- Lattice-induced conjugation on an abstract complex base-change model. -/
noncomputable def latticeConj (hℂ : IsBaseChange ℂ ιℂ) :
    Vℂ →ₛₗ[starRingEnd ℂ] Vℂ :=
  hℂ.equiv.toLinearMap.comp
    ((concreteLatticeConj (V := V)).comp hℂ.equiv.symm.toLinearMap)

/-- Abstract lattice-induced conjugation fixes the image of the integral module. -/
@[simp]
theorem latticeConj_ι (hℂ : IsBaseChange ℂ ιℂ) (v : V) :
    latticeConj hℂ (ιℂ v) = ιℂ v := by
  simp [latticeConj]

/-- Abstract lattice-induced conjugation is involutive. -/
theorem latticeConj_involutive (hℂ : IsBaseChange ℂ ιℂ) :
    Function.Involutive (latticeConj hℂ) := by
  intro x
  simp only [latticeConj, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hℂ.equiv.symm_apply_apply, concreteLatticeConj_involutive,
    hℂ.equiv.apply_symm_apply]

/-- Applying abstract lattice-induced conjugation twice returns the original vector. -/
@[simp]
theorem latticeConj_apply_apply (hℂ : IsBaseChange ℂ ιℂ) (x : Vℂ) :
    latticeConj hℂ (latticeConj hℂ x) = x :=
  latticeConj_involutive hℂ x

/-- Lattice-induced conjugation is the unique conjugate-linear map on an abstract complexification
that fixes every integral vector. -/
theorem latticeConj_unique (hℂ : IsBaseChange ℂ ιℂ)
    (c : Vℂ →ₛₗ[starRingEnd ℂ] Vℂ) (hc : ∀ v, c (ιℂ v) = ιℂ v) :
    c = latticeConj hℂ := by
  ext x
  induction x using hℂ.inductionOn with
  | zero => simp
  | tmul v => simp [hc]
  | smul z x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]

/-- On the canonical tensor-product model, abstract lattice-induced conjugation is the concrete
tensor map. -/
theorem latticeConj_complexificationMap :
    latticeConj (isBaseChange_complexificationMap (V := V)) =
      concreteLatticeConj (V := V) :=
  (latticeConj_unique isBaseChange_complexificationMap concreteLatticeConj
    concreteLatticeConj_complexificationMap).symm

/-- Lattice-induced conjugation on an abstract complexification, bundled as a conjugation. -/
noncomputable def latticeConjugation (hℂ : IsBaseChange ℂ ιℂ) : Conjugation Vℂ where
  toEquiv := LinearEquiv.ofInvolutive (latticeConj hℂ) (latticeConj_involutive hℂ)
  involutive := latticeConj_involutive hℂ

/-- The equivalence underlying bundled lattice conjugation applies as `latticeConj`. -/
@[simp]
theorem latticeConjugation_toEquiv_apply (hℂ : IsBaseChange ℂ ιℂ) (x : Vℂ) :
    (latticeConjugation hℂ).toEquiv x = latticeConj hℂ x :=
  by simp [latticeConjugation]

/-- The linear map underlying bundled lattice conjugation is `latticeConj`, bridging the bundled
spelling used by `HodgeStructureOn` and the bare spelling used by the base-change API. This is not
a `simp` lemma: rewriting with it discards the equivalence, and with it `simp`'s ability to see
that conjugating a subspace preserves `⊤`. -/
theorem latticeConjugation_toLinearMap (hℂ : IsBaseChange ℂ ιℂ) :
    (latticeConjugation hℂ).toEquiv.toLinearMap = latticeConj hℂ :=
  (rfl)

/-- Bundled lattice conjugation fixes the image of the integral module. -/
theorem latticeConjugation_toEquiv_ι (hℂ : IsBaseChange ℂ ιℂ) (v : V) :
    (latticeConjugation hℂ).toEquiv (ιℂ v) = ιℂ v := by
  simp

end Abstract

section IntegralMaps

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
variable {W₁ : Type v₁} {W₂ : Type v₂} {W₃ : Type v₃}
variable [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]
variable [AddCommGroup W₃] [Module ℂ W₃]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂} {ι₃ : V₃ →ₗ[ℤ] W₃}

/-- The complexification of an integral linear map between abstract complexification models. -/
noncomputable def integralMapToComplex (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f : V₁ →ₗ[ℤ] V₂) : W₁ →ₗ[ℂ] W₂ :=
  h₁.lift (ι₂ ∘ₗ f)

/-- Complexification agrees with the target lattice map on integral vectors. -/
@[simp]
theorem integralMapToComplex_apply_ι (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f : V₁ →ₗ[ℤ] V₂) (x : V₁) :
    integralMapToComplex h₁ ι₂ f (ι₁ x) = ι₂ (f x) :=
  h₁.lift_eq (ι₂ ∘ₗ f) x

/-- The additive homomorphism `(V₁ →ₗ[ℤ] V₂) →+ (W₁ →ₗ[ℂ] W₂)` sending an integral linear map to
its complexification. -/
private noncomputable def integralMapToComplexAddMonoidHom (h₁ : IsBaseChange ℂ ι₁)
    (ι₂ : V₂ →ₗ[ℤ] W₂) : (V₁ →ₗ[ℤ] V₂) →+ (W₁ →ₗ[ℂ] W₂) :=
  AddMonoidHom.mk' (integralMapToComplex h₁ ι₂) fun _ _ ↦ h₁.algHom_ext _ _ fun x ↦ by simp

/-- The bundled complexification homomorphism acts as `integralMapToComplex`. -/
@[simp]
private theorem coe_integralMapToComplexAddMonoidHom (h₁ : IsBaseChange ℂ ι₁)
    (ι₂ : V₂ →ₗ[ℤ] W₂) :
    ⇑(integralMapToComplexAddMonoidHom h₁ ι₂) = integralMapToComplex h₁ ι₂ :=
  rfl

/-- Complexification sends the identity integral map to the identity complex map. -/
@[simp]
theorem integralMapToComplex_id (h₁ : IsBaseChange ℂ ι₁) :
    integralMapToComplex h₁ ι₁ (LinearMap.id : V₁ →ₗ[ℤ] V₁) = LinearMap.id :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- Complexification sends the zero integral map to the zero complex map. -/
@[simp]
theorem integralMapToComplex_zero (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) :
    integralMapToComplex h₁ ι₂ (0 : V₁ →ₗ[ℤ] V₂) = 0 := by
  simpa using map_zero (integralMapToComplexAddMonoidHom h₁ ι₂)

/-- Complexification preserves addition of integral linear maps. -/
@[simp]
theorem integralMapToComplex_add (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f g : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (f + g) =
      integralMapToComplex h₁ ι₂ f + integralMapToComplex h₁ ι₂ g := by
  simpa using map_add (integralMapToComplexAddMonoidHom h₁ ι₂) f g

/-- Complexification preserves negation of integral linear maps. -/
@[simp]
theorem integralMapToComplex_neg (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (-f) = -integralMapToComplex h₁ ι₂ f := by
  simpa using map_neg (integralMapToComplexAddMonoidHom h₁ ι₂) f

/-- Complexification preserves subtraction of integral linear maps. -/
@[simp]
theorem integralMapToComplex_sub (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f g : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (f - g) =
      integralMapToComplex h₁ ι₂ f - integralMapToComplex h₁ ι₂ g := by
  simpa using map_sub (integralMapToComplexAddMonoidHom h₁ ι₂) f g

/-- Complexification preserves natural-number multiples of integral linear maps. -/
@[simp]
theorem integralMapToComplex_nsmul (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) (k : ℕ)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (k • f) = k • integralMapToComplex h₁ ι₂ f := by
  simpa using map_nsmul (integralMapToComplexAddMonoidHom h₁ ι₂) k f

/-- Complexification preserves integer multiples of integral linear maps. -/
@[simp]
theorem integralMapToComplex_zsmul (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) (k : ℤ)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (k • f) = k • integralMapToComplex h₁ ι₂ f := by
  simpa using map_zsmul (integralMapToComplexAddMonoidHom h₁ ι₂) k f

/-- Complexification preserves composition of integral linear maps. -/
theorem integralMapToComplex_comp (h₁ : IsBaseChange ℂ ι₁) (h₂ : IsBaseChange ℂ ι₂)
    (ι₃ : V₃ →ₗ[ℤ] W₃) (f : V₁ →ₗ[ℤ] V₂) (g : V₂ →ₗ[ℤ] V₃) :
    integralMapToComplex h₁ ι₃ (g ∘ₗ f) =
      integralMapToComplex h₂ ι₃ g ∘ₗ integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp

/-- The complexification of an integral map commutes with lattice-induced conjugation. -/
@[simp]
theorem integralMapToComplex_commutes_conj (h₁ : IsBaseChange ℂ ι₁)
    (h₂ : IsBaseChange ℂ ι₂) (f : V₁ →ₗ[ℤ] V₂) (x : W₁) :
    integralMapToComplex h₁ ι₂ f (latticeConj h₁ x) =
      latticeConj h₂ (integralMapToComplex h₁ ι₂ f x) := by
  induction x using h₁.inductionOn with
  | zero => simp
  | tmul x => simp
  | smul z x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]

end IntegralMaps

end TauCeti.Hodge
