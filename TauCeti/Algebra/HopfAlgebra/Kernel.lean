/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Equalizer
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic
import TauCeti.Algebra.TensorProduct.Injective

/-!
# Kernels of Hopf algebra morphisms

This file records two conditions under which the kernel of a morphism of Hopf algebras is a
Hopf ideal. Over an arbitrary commutative base, surjectivity provides the exactness needed to
identify the kernel of the tensor-square map with `ker f ⊗ H + H ⊗ ker f`. Over a field, no
surjectivity hypothesis is needed: after factoring through `H / ker f`, the tensor square of
the injective factor remains injective.

This is a Layer 3 prerequisite for the reductive-groups roadmap target "Hopf ideals ↔ closed
subgroup schemes", specifically the "kernels" part of the Hopf-ideal/closed-subgroup
dictionary.

## Main declarations

* `TauCeti.HopfIdeal.kerOfSurjective`: the Hopf ideal given by the kernel of a surjective bialgebra
  morphism.
* `TauCeti.HopfIdeal.ker`: the kernel Hopf ideal of an arbitrary bialgebra morphism over a field.
* `TauCeti.HopfIdeal.ker_le_ker_comp`: a Hopf kernel grows under postcomposition.
* `TauCeti.HopfIdeal.kerOfSurjective_eq_ker`: comparison of the two constructions over a field.
* `TauCeti.HopfIdeal.kerOfSurjective_toIdeal` and
  `TauCeti.HopfIdeal.mem_kerOfSurjective`: its characteristic API.
* `TauCeti.HopfIdeal.kerLiftBialgHom`: the induced bialgebra morphism from the quotient by
  the kernel of a surjective morphism.
* `TauCeti.HopfIdeal.kerLiftBialgEquiv`: the resulting bialgebra equivalence from the quotient
  by the kernel to the codomain.
* `TauCeti.HopfIdeal.kerOfSurjective_mkBialgHom`: the kernel of the quotient morphism by `I`
  is `I`.
* `TauCeti.HopfIdeal.ker_lTensor_eq_rightTensorIdeal`: tensoring on the left by a flat algebra
  carries the kernel of an algebra map to the corresponding right tensor ideal.

## References

The construction is the standard kernel Hopf ideal. The tensor-kernel exactness steps use
Mathlib's `Algebra.TensorProduct.map_ker` and `Module.Flat.ker_lTensor_eq`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace HopfIdeal

variable {R : Type u} {H : Type v} {K : Type w}
variable [CommRing R] [Ring H] [Ring K]

/-- The tensor-kernel exactness theorem in the tensor-ideal notation used by `HopfIdeal`. -/
private theorem tensor_map_ker_eq_left_sup_right [Algebra R H] {A : Type*} [Ring A] [Algebra R A]
    (f : H →ₐ[R] A)
    (hf : Function.Surjective f) :
    RingHom.ker (Algebra.TensorProduct.map f f) =
      leftTensorIdeal (R := R) (H := H) (RingHom.ker f) ⊔
        rightTensorIdeal (R := R) (H := H) (RingHom.ker f) := by
  rw [Algebra.TensorProduct.map_ker (f := f) (g := f) hf hf,
    leftTensorIdeal_def, rightTensorIdeal_def]
  simp only [AlgHom.toRingHom_eq_coe]
  -- `map_ker` states the two maps via algebra-hom coercions, while `leftTensorIdeal_def`
  -- and `rightTensorIdeal_def` use their `toRingHom`; after the named coercion rewrite
  -- these are the same ideal maps definitionally.
  apply congr_arg₂ (· ⊔ ·) <;> rfl

/-- Tensoring on the left by a flat algebra carries the kernel of an algebra map to the
corresponding right tensor ideal. -/
theorem ker_lTensor_eq_rightTensorIdeal {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R A] (f : A →ₐ[R] B) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) f) =
      rightTensorIdeal (R := R) (H := A) (RingHom.ker f) := by
  rw [← Submodule.restrictScalars_inj R]
  have hmap :
      (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) f)).restrictScalars R =
        LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor R A f.toLinearMap) := by
    have hlinear :
        (Algebra.TensorProduct.map (AlgHom.id R A) f).toLinearMap =
          TensorProduct.AlgebraTensorModule.lTensor R A f.toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro x y
      simp only [Algebra.TensorProduct.toLinearMap_map, AlgHom.toLinearMap_id,
        TensorProduct.AlgebraTensorModule.map_tmul,
        TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.id_apply]
    ext x
    simp only [Submodule.restrictScalars_mem, RingHom.mem_ker, LinearMap.mem_ker]
    rw [← LinearMap.congr_fun hlinear x]
    simp only [AlgHom.toLinearMap_apply]
  rw [hmap]
  rw [Module.Flat.ker_lTensor_eq]
  have hker : f.toLinearMap.ker = (RingHom.ker f).restrictScalars R := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, RingHom.mem_ker,
      AlgHom.toLinearMap_apply]
  rw [hker]
  have hsubtype : ((RingHom.ker f).restrictScalars R).subtype =
      (RingHom.ker f).subtype.restrictScalars R := by
    ext x
    exact (LinearMap.restrictScalars_apply R (RingHom.ker f).subtype x).symm
  rw [hsubtype, rightTensorIdeal_def]
  exact TensorProduct.AlgebraTensorModule.range_lTensor_idealMap
    (R := R) A R (RingHom.ker f)

variable [HopfAlgebra R H] [HopfAlgebra R K]

/-- The tensor-square map sends the comultiplication of an element in the kernel of a
bialgebra morphism to zero. -/
private theorem comul_mem_tensor_map_ker (f : H →ₐc[R] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[R] K)) :
    Coalgebra.comul (R := R) x ∈
      RingHom.ker
        (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)).toRingHom := by
  rw [RingHom.mem_ker]
  calc
    Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K) (Coalgebra.comul (R := R) x)
        = Coalgebra.comul (R := R) (f x) := CoalgHomClass.map_comp_comul_apply f x
    _ = 0 := by
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simpa using congrArg (Coalgebra.comul (R := R) (A := K)) hfx

/-- The counit vanishes on the ordinary kernel of a bialgebra morphism. -/
private theorem counit_eq_zero_of_mem_ker (f : H →ₐc[R] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[R] K)) : Coalgebra.counit (R := R) x = 0 := by
  have h := CoalgHomClass.counit_comp_apply f x
  have hfx : f x = 0 := RingHom.mem_ker.mp hx
  simpa [hfx] using h.symm

/-- The antipode preserves the ordinary kernel of a bialgebra morphism. -/
private theorem antipode_mem_ker (f : H →ₐc[R] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[R] K)) :
    HopfAlgebra.antipode R x ∈ RingHom.ker (f : H →ₐ[R] K) := by
  rw [RingHom.mem_ker]
  have hfx : f x = 0 := RingHom.mem_ker.mp hx
  simp [hfx, BialgHom.map_antipode f x]

/-- Build a Hopf ideal from the only kernel condition that is not automatic. -/
private def ofKerComul (f : H →ₐc[R] K)
    (hcomul : ∀ ⦃x : H⦄, x ∈ RingHom.ker (f : H →ₐ[R] K) →
      Coalgebra.comul (R := R) x ∈
        leftTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K)) ⊔
          rightTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K))) :
    HopfIdeal R H :=
  ofIdeal (RingHom.ker (f : H →ₐ[R] K)) hcomul
    (fun x hx ↦ counit_eq_zero_of_mem_ker (R := R) f (x := x) hx)
    (fun x hx ↦ antipode_mem_ker (R := R) f (x := x) hx)

@[simp]
private theorem ofKerComul_toIdeal (f : H →ₐc[R] K) (hcomul) :
    (ofKerComul f hcomul).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  rfl

@[simp]
private theorem mem_ofKerComul (f : H →ₐc[R] K) (hcomul) {x : H} :
    x ∈ ofKerComul f hcomul ↔ f x = 0 := by
  rw [← mem_toIdeal, ofKerComul_toIdeal, RingHom.mem_ker]
  simp only [BialgHom.coe_toAlgHom]

/-- A Hopf ideal whose underlying ideal is a morphism kernel is bottom exactly when the
morphism is injective. -/
private theorem eq_bot_iff_injective {I : HopfIdeal R H} (f : H →ₐc[R] K)
    (hI : I.toIdeal = RingHom.ker (f : H →ₐ[R] K)) :
    I = ⊥ ↔ Function.Injective f := by
  constructor
  · intro h
    apply (RingHom.injective_iff_ker_eq_bot (f : H →ₐ[R] K)).mpr
    calc
      RingHom.ker (f : H →ₐ[R] K) = I.toIdeal := hI.symm
      _ = (⊥ : HopfIdeal R H).toIdeal := congrArg toIdeal h
      _ = ⊥ := bot_toIdeal
  · intro hf
    have h := (RingHom.injective_iff_ker_eq_bot (f : H →ₐ[R] K)).mp hf
    apply le_antisymm ?_ bot_le
    rw [← toIdeal_le_toIdeal, bot_toIdeal, hI, h]

/-- The kernel of a surjective bialgebra morphism, as a Hopf ideal. -/
def kerOfSurjective (f : H →ₐc[R] K) (hf : Function.Surjective f) : HopfIdeal R H :=
  ofKerComul f (by
    intro x hx
    have hker := comul_mem_tensor_map_ker (R := R) f hx
    have hker' : Coalgebra.comul (R := R) x ∈
        RingHom.ker (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)) := by
      simpa using hker
    rwa [tensor_map_ker_eq_left_sup_right (R := R) (f : H →ₐ[R] K) hf] at hker')

/-- The underlying ideal of the kernel Hopf ideal is the ring-hom kernel. -/
@[simp]
theorem kerOfSurjective_toIdeal (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerOfSurjective f hf).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  ofKerComul_toIdeal f _

/-- Membership in the kernel Hopf ideal is vanishing under the bialgebra morphism. -/
@[simp]
theorem mem_kerOfSurjective (f : H →ₐc[R] K) (hf : Function.Surjective f) {x : H} :
    x ∈ kerOfSurjective f hf ↔ f x = 0 :=
  mem_ofKerComul f _

/-- The kernel Hopf ideal is bottom exactly when the morphism is injective. -/
theorem kerOfSurjective_eq_bot_iff (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    kerOfSurjective f hf = ⊥ ↔ Function.Injective f :=
  eq_bot_iff_injective f (kerOfSurjective_toIdeal f hf)

section Field

variable {k : Type u} [Field k]
variable [HopfAlgebra k H] [HopfAlgebra k K]

/-- The tensor square of the injective factor through `H / ker f` is injective. -/
private theorem tensor_kerLiftAlg_injective (f : H →ₐ[k] K) :
    Function.Injective
      (Algebra.TensorProduct.map (Ideal.kerLiftAlg f) (Ideal.kerLiftAlg f)) := by
  let f' : (H ⧸ RingHom.ker f) →ₐ[k] K := Ideal.kerLiftAlg f
  have hf' : Function.Injective f' := Ideal.kerLiftAlg_injective f
  exact Algebra.TensorProduct.map_injective_of_injective f' f' hf' hf'

/-- The comultiplication of an element in the ordinary kernel of a Hopf-algebra morphism over a
field belongs to `ker f ⊗ H + H ⊗ ker f`. -/
private theorem comul_mem_left_sup_right_of_mem_ker (f : H →ₐc[k] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[k] K)) :
    Coalgebra.comul (R := k) x ∈
      leftTensorIdeal (R := k) (H := H) (RingHom.ker (f : H →ₐ[k] K)) ⊔
        rightTensorIdeal (R := k) (H := H) (RingHom.ker (f : H →ₐ[k] K)) := by
  let I := RingHom.ker (f : H →ₐ[k] K)
  let q : H →ₐ[k] H ⧸ I := Ideal.Quotient.mkₐ k I
  let f' : (H ⧸ I) →ₐ[k] K := Ideal.kerLiftAlg f.toAlgHom
  have hcomp : f'.comp q = f.toAlgHom := by
    ext y
    exact Ideal.kerLiftAlg_mk f.toAlgHom y
  have hzero :
      Algebra.TensorProduct.map f.toAlgHom f.toAlgHom (Coalgebra.comul (R := k) x) = 0 := by
    calc
      Algebra.TensorProduct.map f.toAlgHom f.toAlgHom (Coalgebra.comul (R := k) x) =
          Coalgebra.comul (R := k) (f x) := CoalgHomClass.map_comp_comul_apply f x
      _ = 0 := by
        have hfx : f x = 0 := RingHom.mem_ker.mp hx
        simp [hfx]
  have hfactor :
      Algebra.TensorProduct.map f' f'
          (Algebra.TensorProduct.map q q (Coalgebra.comul (R := k) x)) = 0 := by
    calc
      Algebra.TensorProduct.map f' f'
          (Algebra.TensorProduct.map q q (Coalgebra.comul (R := k) x)) =
          Algebra.TensorProduct.map (f'.comp q) (f'.comp q)
            (Coalgebra.comul (R := k) x) := by
              rw [Algebra.TensorProduct.map_comp, AlgHom.comp_apply]
      _ = Algebra.TensorProduct.map f.toAlgHom f.toAlgHom
            (Coalgebra.comul (R := k) x) := by rw [hcomp]
      _ = 0 := hzero
  have hqzero :
      Algebra.TensorProduct.map q q (Coalgebra.comul (R := k) x) = 0 :=
    tensor_kerLiftAlg_injective f.toAlgHom hfactor
  have hker : RingHom.ker (Algebra.TensorProduct.map q q).toRingHom =
      leftTensorIdeal (R := k) (H := H) I ⊔ rightTensorIdeal (R := k) (H := H) I := by
    simpa only [q, AlgHom.ker_coe, AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker] using
      tensor_map_ker_eq_left_sup_right (R := k) q (Ideal.Quotient.mkₐ_surjective k I)
  rw [← hker, RingHom.mem_ker]
  exact hqzero

/-- The ordinary kernel of a morphism of Hopf algebras over a field, as a Hopf ideal. No
surjectivity hypothesis is needed over a field. -/
def ker (f : H →ₐc[k] K) : HopfIdeal k H :=
  ofKerComul (R := k) f
    (fun x hx ↦ comul_mem_left_sup_right_of_mem_ker (k := k) f (x := x) hx)

/-- The underlying ideal of the kernel Hopf ideal is the ordinary ring-hom kernel. -/
@[simp]
theorem ker_toIdeal (f : H →ₐc[k] K) :
    (ker f).toIdeal = RingHom.ker (f : H →ₐ[k] K) :=
  ofKerComul_toIdeal f _

/-- Membership in the kernel Hopf ideal is vanishing under the morphism. -/
@[simp]
theorem mem_ker (f : H →ₐc[k] K) {x : H} : x ∈ ker f ↔ f x = 0 :=
  mem_ofKerComul f _

/-- The kernel Hopf ideal of a morphism is contained in the kernel after postcomposition. -/
theorem ker_le_ker_comp {L : Type x} [Ring L] [HopfAlgebra k L]
    (f : H →ₐc[k] K) (g : K →ₐc[k] L) : ker f ≤ ker (g.comp f) := by
  intro h hh
  rw [mem_ker] at hh ⊢
  rw [BialgHom.comp_apply, hh, map_zero]

/-- Over a field, the kernel constructed for a surjective morphism agrees with the canonical
kernel, which does not require the surjectivity hypothesis. -/
@[simp]
theorem kerOfSurjective_eq_ker (f : H →ₐc[k] K) (hf : Function.Surjective f) :
    kerOfSurjective f hf = ker f := by
  ext x
  rw [mem_kerOfSurjective, mem_ker]

/-- The kernel of the quotient bialgebra morphism by `I` is `I`. -/
@[simp]
theorem ker_mkBialgHom (I : HopfIdeal k H) :
    ker (Bialgebra.Quotient.mkBialgHom I.toIdeal) = I := by
  ext x
  rw [mem_ker, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_toIdeal]

/-- The kernel Hopf ideal is bottom exactly when the morphism is injective. -/
@[simp]
theorem ker_eq_bot_iff (f : H →ₐc[k] K) : ker f = ⊥ ↔ Function.Injective f :=
  eq_bot_iff_injective f (ker_toIdeal f)

end Field

/-- The bialgebra morphism induced from a surjective morphism on the quotient by its
Hopf-ideal kernel. -/
@[expose] noncomputable def kerLiftBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    H ⧸ (kerOfSurjective f hf).toIdeal →ₐc[R] K :=
  Bialgebra.Quotient.liftBialgHom (kerOfSurjective f hf).toIdeal f (by
    intro x hx
    simpa [kerOfSurjective_toIdeal] using hx)

/-- The kernel quotient lift evaluates on quotient classes as the original morphism. -/
@[simp]
theorem kerLiftBialgHom_mk (f : H →ₐc[R] K) (hf : Function.Surjective f) (h : H) :
    kerLiftBialgHom f hf (Ideal.Quotient.mkₐ R (kerOfSurjective f hf).toIdeal h) = f h :=
  Bialgebra.Quotient.liftBialgHom_mk (kerOfSurjective f hf).toIdeal f (by
    intro x hx
    simpa [kerOfSurjective_toIdeal] using hx) h

/-- The kernel quotient lift composed with the quotient map is the original morphism. -/
@[simp]
theorem kerLiftBialgHom_comp_mkBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerLiftBialgHom f hf).comp
        (Bialgebra.Quotient.mkBialgHom (kerOfSurjective f hf).toIdeal) = f :=
  Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom (kerOfSurjective f hf).toIdeal f (by
    intro x hx
    simpa [kerOfSurjective_toIdeal] using hx)

/-- The quotient by the Hopf-ideal kernel of a surjective morphism maps bijectively to the
codomain. -/
theorem kerLiftBialgHom_bijective (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    Function.Bijective (kerLiftBialgHom f hf) := by
  have hfun : (kerLiftBialgHom f hf : H ⧸ (kerOfSurjective f hf).toIdeal → K) =
      (Ideal.quotientKerAlgEquivOfSurjective (f := (f : H →ₐ[R] K)) hf :
        H ⧸ RingHom.ker (f : H →ₐ[R] K) → K) := by
    ext q
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (kerOfSurjective f hf).toIdeal q
    rw [kerLiftBialgHom_mk, Ideal.Quotient.mkₐ_eq_mk]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := (f : H →ₐ[R] K)) hf h).symm
  rw [hfun]
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := (f : H →ₐ[R] K)) hf).bijective

/-- The quotient by the Hopf-ideal kernel of a surjective morphism is bialgebra-equivalent to
the codomain. -/
@[expose] noncomputable def kerLiftBialgEquiv (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (H ⧸ (kerOfSurjective f hf).toIdeal) ≃ₐc[R] K :=
  BialgEquiv.ofBijective (kerLiftBialgHom f hf) (kerLiftBialgHom_bijective f hf)

/-- The kernel quotient equivalence applies as the kernel quotient lift. -/
@[simp]
theorem kerLiftBialgEquiv_apply (f : H →ₐc[R] K) (hf : Function.Surjective f)
    (q : H ⧸ (kerOfSurjective f hf).toIdeal) :
    kerLiftBialgEquiv f hf q = kerLiftBialgHom f hf q :=
  rfl

/-- The bialgebra morphism underlying the kernel quotient equivalence is the kernel quotient
lift. -/
@[simp]
theorem kerLiftBialgEquiv_toBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerLiftBialgEquiv f hf : H ⧸ (kerOfSurjective f hf).toIdeal →ₐc[R] K) =
      kerLiftBialgHom f hf :=
  rfl

/-- The Hopf-ideal kernel of the quotient morphism by `I` is `I`. -/
@[simp]
theorem kerOfSurjective_mkBialgHom (I : HopfIdeal R H) :
    kerOfSurjective (Bialgebra.Quotient.mkBialgHom I.toIdeal)
      Ideal.Quotient.mk_surjective = I := by
  ext x
  -- Membership in `kerOfSurjective` is by definition vanishing under the morphism; `change`
  -- spells that out because the kernel is a bundled structure.
  change Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal x = 0 ↔ x ∈ I
  rw [Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem, mem_toIdeal]

end HopfIdeal

end TauCeti
