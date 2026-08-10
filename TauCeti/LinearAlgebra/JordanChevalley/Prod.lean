/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative

/-!
# Products of multiplicative Jordan decompositions

Semisimple and unipotent linear automorphisms are preserved by componentwise products.  Over a
perfect field, the multiplicative Jordan decomposition of a product automorphism is therefore
computed componentwise.

This supplies product infrastructure for the linear-algebraic functoriality step in Layer 4 of the
ReductiveGroups roadmap.

## Main declarations

* `IsNilpotent.prodMap`: a product of nilpotent endomorphisms is nilpotent.
* `TauCeti.Module.End.IsSemisimple.prodMap`: a product of semisimple endomorphisms is semisimple.
* `TauCeti.GeneralLinearGroup.prodMap`: the componentwise product of two linear automorphisms.
* `TauCeti.GeneralLinearGroup.jordanDecomposition_prodMap`: Jordan decomposition is componentwise
  on product modules.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open LinearMap Polynomial

namespace Module.End

universe u v w

section Semiring

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

@[simp]
private theorem prodMap_pow (f : Module.End K V) (g : Module.End K W) (n : ℕ) :
    (f.prodMap g) ^ n = (f ^ n).prodMap (g ^ n) := by
  induction n with
  | zero => exact LinearMap.prodMap_one.symm
  | succ n hn => rw [pow_succ, pow_succ, pow_succ, hn, LinearMap.prodMap_mul]

/-- The componentwise product of two nilpotent endomorphisms is nilpotent. -/
theorem _root_.IsNilpotent.prodMap {f : Module.End K V} {g : Module.End K W}
    (hf : IsNilpotent f) (hg : IsNilpotent g) : IsNilpotent (f.prodMap g) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m + n, ?_⟩
  rw [prodMap_pow, pow_add, hm, zero_mul, pow_add, hn, mul_zero,
    LinearMap.prodMap_zero]

end Semiring

section CommRing

variable {K : Type u} {V : Type v} {W : Type w}
variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

private theorem aeval_prodMap (f : Module.End K V) (g : Module.End K W) (p : K[X]) :
    aeval (f.prodMap g) p = (aeval f p).prodMap (aeval g p) := by
  have h : aeval (f.prodMap g) =
      (LinearMap.prodMapAlgHom K V W).comp ((aeval f).prod (aeval g)) := by
    ext <;> simp
  exact DFunLike.congr_fun h p

/-- The componentwise product of two semisimple endomorphisms is semisimple. -/
theorem IsSemisimple.prodMap {f : Module.End K V} {g : Module.End K W}
    (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    Module.End.IsSemisimple (f.prodMap g) := by
  rw [Module.End.IsSemisimple] at hf hg ⊢
  let _ : IsSemisimpleModule K[X] (Module.AEval' f) := hf
  let _ : IsSemisimpleModule K[X] (Module.AEval' g) := hg
  let L := LinearMap.range
    (LinearMap.inl K[X] (Module.AEval' f) (Module.AEval' g))
  let R := LinearMap.range
    (LinearMap.inr K[X] (Module.AEval' f) (Module.AEval' g))
  let _ : IsSemisimpleModule K[X] L := IsSemisimpleModule.range _
  let _ : IsSemisimpleModule K[X] R := IsSemisimpleModule.range _
  have hprod : IsSemisimpleModule K[X] (Module.AEval' f × Module.AEval' g) := by
    have hsup : IsSemisimpleModule K[X] ↑(L ⊔ R) :=
      IsSemisimpleModule.sup inferInstance inferInstance
    let _ : IsSemisimpleModule K[X] ↑(L ⊔ R) := hsup
    apply IsSemisimpleModule.of_surjective (L ⊔ R).subtype
    intro x
    have htop : L ⊔ R = ⊤ := LinearMap.sup_range_inl_inr
    exact ⟨⟨x, htop.symm ▸ Submodule.mem_top⟩, rfl⟩
  let E : Module.AEval' (f.prodMap g) ≃ₗ[K[X]]
      Module.AEval' f × Module.AEval' g := {
    toFun x := (x.1, x.2)
    invFun x := (x.1, x.2)
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' p x := by
      -- Unfold the two `AEval` scalar actions to compare their underlying endomorphisms.
      apply Prod.ext
      · change ((aeval (f.prodMap g) p) x).1 = (aeval f p) x.1
        rw [aeval_prodMap]
        rfl
      · change ((aeval (f.prodMap g) p) x).2 = (aeval g p) x.2
        rw [aeval_prodMap]
        rfl
  }
  let _ := hprod
  exact IsSemisimpleModule.congr E

end CommRing

end Module.End

namespace GeneralLinearGroup

universe u v w

section Semiring

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- The product map of two linear automorphisms, acting componentwise on the product module. -/
def prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    GeneralLinearGroup K (V × W) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (g.toLinearEquiv.prodCongr h.toLinearEquiv)

/-- The endomorphism underlying a product-map automorphism is `LinearMap.prodMap`. -/
@[simp]
theorem coe_prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    (prodMap g h : Module.End K (V × W)) =
      (g : Module.End K V).prodMap (h : Module.End K W) :=
  (rfl)

/-- Product maps preserve multiplication. -/
@[simp]
theorem prodMap_mul (g₁ g₂ : GeneralLinearGroup K V) (h₁ h₂ : GeneralLinearGroup K W) :
    prodMap (g₁ * g₂) (h₁ * h₂) = prodMap g₁ h₁ * prodMap g₂ h₂ := by
  ext x <;> rfl

/-- The product map of two identity automorphisms is the identity. -/
@[simp]
theorem prodMap_one : prodMap (1 : GeneralLinearGroup K V) (1 : GeneralLinearGroup K W) = 1 := by
  ext x <;> rfl

/-- Product maps preserve inverses. -/
@[simp]
theorem prodMap_inv (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    prodMap g⁻¹ h⁻¹ = (prodMap g h)⁻¹ := by
  ext x <;> rfl

end Semiring

section CommRing

variable {K : Type u} {V : Type v} {W : Type w}
variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The product map of two semisimple automorphisms is semisimple. -/
theorem IsSemisimple.prodMap {g : GeneralLinearGroup K V} {h : GeneralLinearGroup K W}
    (hg : IsSemisimple g) (hh : IsSemisimple h) : IsSemisimple (prodMap g h) := by
  rw [isSemisimple_def] at hg hh ⊢
  exact Module.End.IsSemisimple.prodMap hg hh

/-- The product map of two unipotent automorphisms is unipotent. -/
theorem IsUnipotent.prodMap {g : GeneralLinearGroup K V} {h : GeneralLinearGroup K W}
    (hg : IsUnipotent g) (hh : IsUnipotent h) : IsUnipotent (prodMap g h) := by
  rw [isUnipotent_def] at hg hh ⊢
  have hp := hg.prodMap hh
  -- Expose the component endomorphisms beneath the product-map and identity coercions.
  rw [show (GeneralLinearGroup.prodMap g h : Module.End K (V × W)) - 1 =
      ((g : Module.End K V) - 1).prodMap ((h : Module.End K W) - 1) by
    rw [coe_prodMap]
    ext x <;> simp]
  exact hp

end CommRing

section PerfectField

variable {K : Type u} {V : Type v} {W : Type w}
variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V] [FiniteDimensional K W]

/-- The multiplicative Jordan decomposition of a product-map automorphism is the product map of
the decompositions of its two factors. -/
theorem jordanDecomposition_prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    jordanDecomposition (prodMap g h) =
      (prodMap (semisimplePart g) (semisimplePart h),
        prodMap (unipotentPart g) (unipotentPart h)) := by
  symm
  apply (eq_jordanDecomposition_iff (prodMap g h) _ _).2
  refine ⟨(isSemisimple_semisimplePart g).prodMap (isSemisimple_semisimplePart h),
    (isUnipotent_unipotentPart g).prodMap (isUnipotent_unipotentPart h), ?_, ?_⟩
  · rw [commute_iff_eq, ← prodMap_mul, ← prodMap_mul]
    exact congrArg₂ prodMap (commute_semisimplePart_unipotentPart g).eq
      (commute_semisimplePart_unipotentPart h).eq
  · rw [← prodMap_mul, semisimplePart_mul_unipotentPart,
      semisimplePart_mul_unipotentPart]

/-- The semisimple factor of a product-map automorphism is computed componentwise. -/
@[simp]
theorem semisimplePart_prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    semisimplePart (prodMap g h) = prodMap (semisimplePart g) (semisimplePart h) := by
  rw [semisimplePart_def]
  exact congrArg Prod.fst (jordanDecomposition_prodMap g h)

/-- The unipotent factor of a product-map automorphism is computed componentwise. -/
@[simp]
theorem unipotentPart_prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    unipotentPart (prodMap g h) = prodMap (unipotentPart g) (unipotentPart h) := by
  rw [unipotentPart_def]
  exact congrArg Prod.snd (jordanDecomposition_prodMap g h)

end PerfectField

end GeneralLinearGroup

end TauCeti
