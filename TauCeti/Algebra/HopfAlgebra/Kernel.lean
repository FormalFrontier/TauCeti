/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic

/-!
# Kernels of Hopf algebra morphisms

This file records that the kernel of a surjective morphism of Hopf algebras is a Hopf ideal.
The surjectivity hypothesis is the exactness input needed to identify the kernel
of the tensor-square map with `ker f ⊗ H + H ⊗ ker f`.

This is a Layer 3 prerequisite for the reductive-groups roadmap target "Hopf ideals ↔ closed
subgroup schemes", specifically the "kernels" part of the Hopf-ideal/closed-subgroup
dictionary.

## Main declarations

* `TauCeti.HopfIdeal.ker`: the Hopf ideal given by the kernel of a surjective bialgebra
  morphism.
* `TauCeti.HopfIdeal.ker_toIdeal` and `TauCeti.HopfIdeal.mem_ker`: its characteristic API.
* `TauCeti.HopfIdeal.kerLiftBialgHom`: the induced bialgebra morphism from the quotient by
  the kernel of a surjective morphism.
* `TauCeti.HopfIdeal.kerLiftBialgEquiv`: the resulting bialgebra equivalence from the quotient
  by the kernel to the codomain.
* `TauCeti.HopfIdeal.ker_mkBialgHom`: the kernel of the quotient morphism by `I` is `I`.

## References

The construction is the standard kernel Hopf ideal. The tensor-kernel exactness step uses
Mathlib's `Algebra.TensorProduct.map_ker`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace HopfIdeal

variable {R : Type u} {H : Type v} {K : Type w}
variable [CommRing R] [Ring H] [Ring K]
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

/-- The tensor-kernel exactness theorem in the tensor-ideal notation used by `HopfIdeal`. -/
private theorem tensor_map_ker_eq_left_sup_right (f : H →ₐc[R] K)
    (hf : Function.Surjective f) :
    RingHom.ker (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)) =
      leftTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K)) ⊔
        rightTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K)) := by
  rw [Algebra.TensorProduct.map_ker (f := (f : H →ₐ[R] K)) (g := (f : H →ₐ[R] K)) hf hf,
    leftTensorIdeal_def, rightTensorIdeal_def]
  simp only [AlgHom.toRingHom_eq_coe]
  -- `map_ker` states the two maps via algebra-hom coercions, while `leftTensorIdeal_def`
  -- and `rightTensorIdeal_def` use their `toRingHom`; after the named coercion rewrite
  -- these are the same ideal maps definitionally.
  apply congr_arg₂ (· ⊔ ·) <;> rfl

/-- The kernel of a surjective bialgebra morphism, as a Hopf ideal. -/
@[expose] def ker (f : H →ₐc[R] K) (hf : Function.Surjective f) : HopfIdeal R H :=
  ofIdeal (RingHom.ker (f : H →ₐ[R] K))
    (by
      intro x hx
      have hker := comul_mem_tensor_map_ker (R := R) f hx
      have hker' : Coalgebra.comul (R := R) x ∈
          RingHom.ker (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)) := by
        simpa using hker
      rwa [tensor_map_ker_eq_left_sup_right (R := R) f hf] at hker')
    (by
      intro x hx
      have h := CoalgHomClass.counit_comp_apply f x
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simpa [hfx] using h.symm)
    (by
      intro x hx
      rw [RingHom.mem_ker]
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simp [hfx, BialgHom.map_antipode f x])

/-- The underlying ideal of the kernel Hopf ideal is the ring-hom kernel. -/
@[simp]
theorem ker_toIdeal (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (ker f hf).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  rfl

/-- Membership in the kernel Hopf ideal is vanishing under the bialgebra morphism. -/
@[simp]
theorem mem_ker (f : H →ₐc[R] K) (hf : Function.Surjective f) {x : H} :
    x ∈ ker f hf ↔ f x = 0 := by
  rw [← mem_toIdeal, ker_toIdeal, RingHom.mem_ker]
  rfl

/-- The kernel Hopf ideal is bottom exactly when the morphism is injective. -/
theorem ker_eq_bot_iff (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    ker f hf = ⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    have hmem : x - y ∈ ker f hf := by
      rw [mem_ker, map_sub, hxy, sub_self]
    have hzero : x - y = 0 := by
      rw [h] at hmem
      exact (HopfIdeal.mem_bot (R := R) (H := H)).mp hmem
    exact sub_eq_zero.mp hzero
  · intro hinj
    ext x
    rw [mem_ker, mem_bot]
    exact ⟨fun hx => hinj (by simpa using hx), fun hx => by rw [hx, map_zero]⟩

/-- The bialgebra morphism induced from a surjective morphism on the quotient by its
Hopf-ideal kernel. -/
@[expose] noncomputable def kerLiftBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    H ⧸ (ker f hf).toIdeal →ₐc[R] K :=
  Bialgebra.Quotient.liftBialgHom (ker f hf).toIdeal f (by
    intro x hx
    simpa [ker_toIdeal] using hx)

/-- The kernel quotient lift evaluates on quotient classes as the original morphism. -/
@[simp]
theorem kerLiftBialgHom_mk (f : H →ₐc[R] K) (hf : Function.Surjective f) (h : H) :
    kerLiftBialgHom f hf (Ideal.Quotient.mkₐ R (ker f hf).toIdeal h) = f h :=
  Bialgebra.Quotient.liftBialgHom_mk (ker f hf).toIdeal f (by
    intro x hx
    simpa [ker_toIdeal] using hx) h

/-- The kernel quotient lift composed with the quotient map is the original morphism. -/
@[simp]
theorem kerLiftBialgHom_comp_mkBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerLiftBialgHom f hf).comp (Bialgebra.Quotient.mkBialgHom (ker f hf).toIdeal) = f :=
  Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom (ker f hf).toIdeal f (by
    intro x hx
    simpa [ker_toIdeal] using hx)

/-- The quotient by the Hopf-ideal kernel of a surjective morphism maps bijectively to the
codomain. -/
theorem kerLiftBialgHom_bijective (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    Function.Bijective (kerLiftBialgHom f hf) := by
  have hfun : (kerLiftBialgHom f hf : H ⧸ (ker f hf).toIdeal → K) =
      (Ideal.quotientKerAlgEquivOfSurjective (f := (f : H →ₐ[R] K)) hf :
        H ⧸ RingHom.ker (f : H →ₐ[R] K) → K) := by
    ext q
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (ker f hf).toIdeal q
    rw [kerLiftBialgHom_mk, Ideal.Quotient.mkₐ_eq_mk]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := (f : H →ₐ[R] K)) hf h).symm
  rw [hfun]
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := (f : H →ₐ[R] K)) hf).bijective

/-- The quotient by the Hopf-ideal kernel of a surjective morphism is bialgebra-equivalent to
the codomain. -/
@[expose] noncomputable def kerLiftBialgEquiv (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (H ⧸ (ker f hf).toIdeal) ≃ₐc[R] K :=
  BialgEquiv.ofBijective (kerLiftBialgHom f hf) (kerLiftBialgHom_bijective f hf)

/-- The kernel quotient equivalence applies as the kernel quotient lift. -/
@[simp]
theorem kerLiftBialgEquiv_apply (f : H →ₐc[R] K) (hf : Function.Surjective f)
    (q : H ⧸ (ker f hf).toIdeal) :
    kerLiftBialgEquiv f hf q = kerLiftBialgHom f hf q :=
  rfl

/-- The bialgebra morphism underlying the kernel quotient equivalence is the kernel quotient
lift. -/
@[simp]
theorem kerLiftBialgEquiv_toBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerLiftBialgEquiv f hf : H ⧸ (ker f hf).toIdeal →ₐc[R] K) = kerLiftBialgHom f hf :=
  rfl

/-- The Hopf-ideal kernel of the quotient morphism by `I` is `I`. -/
@[simp]
theorem ker_mkBialgHom (I : HopfIdeal R H) :
    ker (Bialgebra.Quotient.mkBialgHom I.toIdeal) Ideal.Quotient.mk_surjective = I := by
  ext x
  -- membership in `ker` is by definition vanishing under the morphism; `change` spells that out,
  -- `ker` being a bundled structure with no membership equation lemma.
  change Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal x = 0 ↔ x ∈ I
  rw [Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem, mem_toIdeal]

end HopfIdeal

end TauCeti
