/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Images of commutative Hopf-algebra morphisms over a field

For a morphism `f : H →ₐc[k] K` of commutative Hopf algebras over a field, its ordinary
ring-theoretic kernel is a Hopf ideal even when `f` is not surjective. The field hypothesis is
the exactness input: after factoring `f` through `H / ker f`, tensoring the injective factor
with itself remains injective. Hence the comultiplication of an element killed by `f` belongs
to `ker f ⊗ H + H ⊗ ker f`.

The quotient by this Hopf ideal is the coordinate algebra of the scheme-theoretic image of the
represented affine-group morphism. This file packages the canonical factorization

```text
H ⟶ H / ker f ⟶ K
```

as a surjective morphism followed by an injective morphism of commutative Hopf algebras.

## Main declarations

* `TauCeti.HopfIdeal.ker`: the kernel Hopf ideal of an arbitrary Hopf-algebra morphism over a
  field.
* `TauCeti.CommHopfAlgCat.image`: the coordinate Hopf algebra of its scheme-theoretic image.
* `TauCeti.CommHopfAlgCat.imageQuotient` and `TauCeti.CommHopfAlgCat.imageι`: the surjective--
  injective factorization through the image.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §6.

This is image infrastructure for Layer 3, "Subgroups, quotients, components", of the
ReductiveGroups roadmap. Scheme-theoretic images are needed to form products of normal closed
subgroups and, subsequently, the derived subgroup and the unipotent and solvable radicals.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace HopfIdeal

variable {k : Type u} {H : Type v} {K : Type w}
variable [Field k] [CommRing H] [CommRing K]
variable [HopfAlgebra k H] [HopfAlgebra k K]

/-- The tensor square of the quotient map by an ideal has kernel
`I ⊗ H + H ⊗ I`. -/
private theorem ker_tensorProduct_map_quotient (I : Ideal H) :
    RingHom.ker
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).toRingHom =
      leftTensorIdeal (R := k) (H := H) I ⊔ rightTensorIdeal (R := k) (H := H) I := by
  have hker : RingHom.ker (Ideal.Quotient.mkₐ k I) = I :=
    Ideal.Quotient.mkₐ_ker (R₁ := k) I
  change RingHom.ker
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)) = _
  rw [Algebra.TensorProduct.map_ker
    (f := Ideal.Quotient.mkₐ k I) (g := Ideal.Quotient.mkₐ k I)
    (Ideal.Quotient.mkₐ_surjective k I) (Ideal.Quotient.mkₐ_surjective k I),
    leftTensorIdeal_def, rightTensorIdeal_def]
  rw [hker]
  simp only [AlgHom.toRingHom_eq_coe]
  apply congr_arg₂ (· ⊔ ·) <;> rfl

/-- The tensor square of the injective factor through `H / ker f` is injective. -/
private theorem tensor_kerLift_injective (f : H →ₐc[k] K) :
    Function.Injective
      (Algebra.TensorProduct.map
        (Ideal.kerLiftAlg f.toAlgHom) (Ideal.kerLiftAlg f.toAlgHom)) := by
  let f' : (H ⧸ RingHom.ker (f : H →ₐ[k] K)) →ₐ[k] K :=
    Ideal.kerLiftAlg f.toAlgHom
  let _ : Module.Projective k K := Module.projective_of_isSemisimpleRing k K
  let _ : Module.Projective k (H ⧸ RingHom.ker (f : H →ₐ[k] K)) :=
    Module.projective_of_isSemisimpleRing k _
  have hf' : Function.Injective f' := Ideal.kerLiftAlg_injective f.toAlgHom
  exact TensorProduct.map_injective_of_flat_flat f'.toLinearMap f'.toLinearMap hf' hf'

/-- The comultiplication of an element in the ordinary kernel of a Hopf-algebra morphism over a
field belongs to `ker f ⊗ H + H ⊗ ker f`. -/
private theorem comul_mem_ker_tensor_ideal (f : H →ₐc[k] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[k] K)) :
    Coalgebra.comul (R := k) x ∈
      leftTensorIdeal (R := k) (H := H) (RingHom.ker (f : H →ₐ[k] K)) ⊔
        rightTensorIdeal (R := k) (H := H) (RingHom.ker (f : H →ₐ[k] K)) := by
  let I := RingHom.ker (f : H →ₐ[k] K)
  let q : H →ₐ[k] H ⧸ I := Ideal.Quotient.mkₐ k I
  let f' : (H ⧸ I) →ₐ[k] K :=
    Ideal.kerLiftAlg f.toAlgHom
  have hcomp : f'.comp q = f.toAlgHom := by
    exact Ideal.Quotient.liftₐ_comp I f.toAlgHom
      (fun y hy ↦ RingHom.mem_ker.mp hy)
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
              rw [Algebra.TensorProduct.map_comp]
              rfl
      _ = Algebra.TensorProduct.map f.toAlgHom f.toAlgHom
            (Coalgebra.comul (R := k) x) := by rw [hcomp]
      _ = 0 := hzero
  have hqzero :
      Algebra.TensorProduct.map q q (Coalgebra.comul (R := k) x) = 0 :=
    tensor_kerLift_injective f hfactor
  rw [← ker_tensorProduct_map_quotient I, RingHom.mem_ker]
  exact hqzero

/-- The ordinary kernel of a morphism of commutative Hopf algebras over a field, as a Hopf
ideal. No surjectivity hypothesis is needed over a field. -/
@[expose] def ker (f : H →ₐc[k] K) : HopfIdeal k H :=
  ofIdeal (RingHom.ker (f : H →ₐ[k] K))
    (by intro x hx; exact comul_mem_ker_tensor_ideal f hx)
    (fun x hx ↦ by
      have h := CoalgHomClass.counit_comp_apply f x
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simpa [hfx] using h.symm)
    (fun x hx ↦ by
      rw [RingHom.mem_ker]
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simp [hfx, BialgHom.map_antipode f x])

/-- The underlying ideal of the kernel Hopf ideal is the ordinary ring-hom kernel. -/
@[simp]
theorem ker_toIdeal (f : H →ₐc[k] K) :
    (ker f).toIdeal = RingHom.ker (f : H →ₐ[k] K) :=
  rfl

/-- Membership in the kernel Hopf ideal is vanishing under the morphism. -/
@[simp]
theorem mem_ker (f : H →ₐc[k] K) {x : H} : x ∈ ker f ↔ f x = 0 := by
  change (f : H →ₐ[k] K) x = 0 ↔ f x = 0
  rfl

/-- The kernel Hopf ideal is bottom exactly when the morphism is injective. -/
@[simp]
theorem ker_eq_bot_iff (f : H →ₐc[k] K) : ker f = ⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    have hmem : x - y ∈ ker f := by simp [hxy]
    rw [h] at hmem
    exact sub_eq_zero.mp ((mem_bot (R := k) (H := H)).mp hmem)
  · intro hf
    ext x
    simp only [mem_ker, mem_bot]
    exact ⟨fun hx ↦ hf (by simpa using hx), fun hx ↦ by simp [hx]⟩

end HopfIdeal

namespace CommHopfAlgCat

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{v} k}

/-- The coordinate Hopf algebra of the scheme-theoretic image of a morphism of affine groups. -/
noncomputable abbrev image (f : H ⟶ K) : _root_.CommHopfAlgCat.{v} k :=
  quotient H (HopfIdeal.ker f.hom)

/-- The quotient map from the target coordinate algebra onto the coordinate algebra of the
scheme-theoretic image. -/
noncomputable abbrev imageQuotient (f : H ⟶ K) : H ⟶ image f :=
  mkQuotient H (HopfIdeal.ker f.hom)

/-- The injective coordinate morphism from the image coordinate algebra into the source
coordinate algebra. Contravariantly, this is the dominant morphism onto the scheme-theoretic
image. -/
noncomputable abbrev imageι (f : H ⟶ K) : image f ⟶ K :=
  liftQuotient (HopfIdeal.ker f.hom) f (by
    rw [HopfIdeal.ker_toIdeal]
    intro x hx
    exact hx)

/-- The coordinate morphism factors through its scheme-theoretic image.

The reassociated lemma is not marked `simp`: since `imageQuotient` and `imageι` are reducible
abbreviations, `mkQuotient_comp_liftQuotient_assoc` already performs that simplification. -/
@[reassoc]
theorem imageQuotient_comp_imageι (f : H ⟶ K) : imageQuotient f ≫ imageι f = f := by
  exact mkQuotient_comp_liftQuotient (HopfIdeal.ker f.hom) f _

/-- The coordinate map onto the scheme-theoretic image is surjective. -/
theorem imageQuotient_surjective (f : H ⟶ K) : Function.Surjective (imageQuotient f).hom :=
  Ideal.Quotient.mk_surjective

/-- The coordinate map from the scheme-theoretic image into the source coordinate algebra is
injective. -/
theorem imageι_injective (f : H ⟶ K) : Function.Injective (imageι f).hom := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (HopfIdeal.ker f.hom).toIdeal x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (HopfIdeal.ker f.hom).toIdeal y
  rw [liftQuotient_mk, liftQuotient_mk] at hxy
  exact Ideal.Quotient.eq.mpr (by
    rw [HopfIdeal.ker_toIdeal, RingHom.mem_ker]
    rw [map_sub, sub_eq_zero]
    calc
      f.hom.toAlgHom.toRingHom a = f.hom a := rfl
      _ = f.hom b := hxy
      _ = f.hom.toAlgHom.toRingHom b := rfl)

end CommHopfAlgCat

end TauCeti
