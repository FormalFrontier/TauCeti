/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

/-!
# Finite bilinear modules

A finite bilinear module is a finite abelian group equipped with a symmetric biadditive pairing
into `ℚ/ℤ`.  The pairing is bundled as its adjoint into Mathlib's `CharacterModule`; this makes
nondegeneracy the assertion that the adjoint is an additive equivalence.

This file provides the basic constructions needed for discriminant forms: isometries, restriction,
form negation, orthogonal direct sums, radicals, orthogonal complements, isotropic subgroups, and
Lagrangians.  Nondegeneracy remains a predicate because restriction to a subgroup can be
degenerate.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

## Main definitions

* `TauCeti.FiniteBilinearModule`: a finite abelian group with a symmetric `ℚ/ℤ`-valued pairing.
* `TauCeti.FiniteBilinearModule.toBilin`: the pairing as a `ℤ`-bilinear map.
* `TauCeti.FiniteBilinearModule.IsNondegenerate`: bijectivity of the adjoint pairing.
* `TauCeti.FiniteBilinearModule.Isometry`: a pairing-preserving additive equivalence.
* `TauCeti.FiniteBilinearModule.orthogonalComplement`: the orthogonal complement of a subgroup.
* `TauCeti.FiniteBilinearModule.IsIsotropic`: vanishing of the pairing on a subgroup.
* `TauCeti.FiniteBilinearModule.IsLagrangian`: equality with the orthogonal complement.
-/

public section

namespace TauCeti

universe u v w

/-- A finite abelian group equipped with a symmetric biadditive pairing into `ℚ/ℤ`.

The pairing is stored as its adjoint `A →+ CharacterModule A`, so biadditivity is part of its
type. -/
structure FiniteBilinearModule where
  /-- The underlying finite abelian group. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [finite : Finite carrier]
  /-- The adjoint of the bilinear pairing. -/
  pairing : carrier →+ CharacterModule carrier
  /-- The pairing is symmetric. -/
  pairing_comm : ∀ x y, pairing x y = pairing y x

attribute [instance] FiniteBilinearModule.addCommGroup FiniteBilinearModule.finite

namespace FiniteBilinearModule

/-- A finite bilinear module coerces to its underlying type. -/
instance : CoeSort FiniteBilinearModule (Type u) := ⟨FiniteBilinearModule.carrier⟩

variable (A : FiniteBilinearModule)

theorem pairing_zero_left (x : A) : A.pairing 0 x = 0 := by
  rw [map_zero]
  rfl

@[simp]
theorem pairing_zero_right (x : A) : A.pairing x 0 = 0 := map_zero _

theorem pairing_add_left (x y z : A) : A.pairing (x + y) z = A.pairing x z + A.pairing y z :=
  DFunLike.congr_fun (map_add A.pairing x y) z

@[simp]
theorem pairing_add_right (x y z : A) : A.pairing x (y + z) = A.pairing x y + A.pairing x z :=
  map_add (A.pairing x) y z

theorem pairing_neg_left (x y : A) : A.pairing (-x) y = -A.pairing x y :=
  DFunLike.congr_fun (map_neg A.pairing x) y

@[simp]
theorem pairing_neg_right (x y : A) : A.pairing x (-y) = -A.pairing x y :=
  map_neg (A.pairing x) y

/-- The bilinear pairing associated to a finite bilinear module, viewed as a `ℤ`-bilinear map. -/
def toBilin : A →ₗ[ℤ] A →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.mk₂' ℤ ℤ (fun x y ↦ A.pairing x y)
    (fun x y z ↦ A.pairing_add_left x y z)
    (fun r x y ↦ by rw [A.pairing_comm (r • x) y, map_zsmul, A.pairing_comm y x])
    (fun x y z ↦ A.pairing_add_right x y z)
    (fun r x y ↦ map_zsmul (A.pairing x) r y)

@[simp]
theorem toBilin_apply (x y : A) : A.toBilin x y = A.pairing x y := by
  rfl

theorem toBilin_isRefl : A.toBilin.IsRefl := fun x y h ↦ by
  rw [toBilin_apply, A.pairing_comm, ← toBilin_apply]
  exact h

/-- A finite bilinear module is nondegenerate when its adjoint pairing is bijective. -/
def IsNondegenerate : Prop := Function.Bijective A.pairing

/-- A nondegenerate pairing identifies its group with the full character module. -/
noncomputable def adjointEquiv (hA : A.IsNondegenerate) : A ≃+ CharacterModule A :=
  AddEquiv.ofBijective A.pairing hA

@[simp]
theorem adjointEquiv_apply (hA : A.IsNondegenerate) (x : A) : A.adjointEquiv hA x = A.pairing x :=
  (rfl)

/-- An isometry of finite bilinear modules is an additive equivalence preserving the pairing. -/
structure Isometry (A : FiniteBilinearModule.{u}) (B : FiniteBilinearModule.{v}) where
  /-- The underlying additive equivalence. -/
  toAddEquiv : A ≃+ B
  /-- The equivalence preserves the bilinear pairing. -/
  map_pairing' : ∀ x y, B.pairing (toAddEquiv x) (toAddEquiv y) = A.pairing x y

namespace Isometry

variable {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{v}}
  {C : FiniteBilinearModule.{w}}

theorem toAddEquiv_injective : Function.Injective (toAddEquiv : Isometry A B → A ≃+ B)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
theorem toAddEquiv_inj {f g : Isometry A B} : f.toAddEquiv = g.toAddEquiv ↔ f = g :=
  toAddEquiv_injective.eq_iff

instance : EquivLike (Isometry A B) A B where
  coe f := f.toAddEquiv
  inv f := f.toAddEquiv.symm
  left_inv f := f.toAddEquiv.left_inv
  right_inv f := f.toAddEquiv.right_inv
  coe_injective' _ _ h _ := toAddEquiv_injective (DFunLike.coe_injective h)

instance : AddEquivClass (Isometry A B) A B where
  map_add f := f.toAddEquiv.map_add'

@[simp]
theorem coe_toAddEquiv (f : Isometry A B) : ⇑f.toAddEquiv = f := rfl

@[simp]
theorem map_pairing (f : Isometry A B) (x y : A) : B.pairing (f x) (f y) = A.pairing x y :=
  f.map_pairing' x y

/-- Two isometries are equal when they agree on all elements. -/
@[ext]
theorem ext {f g : Isometry A B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The identity isometry. -/
def refl (A : FiniteBilinearModule) : Isometry A A where
  toAddEquiv := AddEquiv.refl A
  map_pairing' := by simp

/-- The inverse of an isometry. -/
def symm (f : Isometry A B) : Isometry B A where
  toAddEquiv := f.toAddEquiv.symm
  map_pairing' x y := by
    have := (f.map_pairing' (f.toAddEquiv.symm x) (f.toAddEquiv.symm y)).symm
    simpa using this

/-- The composite of two isometries. -/
def trans (f : Isometry A B) (g : Isometry B C) : Isometry A C where
  toAddEquiv := f.toAddEquiv.trans g.toAddEquiv
  map_pairing' x y := (g.map_pairing' (f.toAddEquiv x) (f.toAddEquiv y)).trans (f.map_pairing' x y)

@[simp]
theorem refl_toAddEquiv (A : FiniteBilinearModule) : (refl A).toAddEquiv = AddEquiv.refl A := (rfl)

@[simp]
theorem symm_toAddEquiv (f : Isometry A B) : f.symm.toAddEquiv = f.toAddEquiv.symm := (rfl)

@[simp]
theorem trans_toAddEquiv (f : Isometry A B) (g : Isometry B C) :
    (f.trans g).toAddEquiv = f.toAddEquiv.trans g.toAddEquiv := (rfl)

@[simp]
theorem apply_refl (A : FiniteBilinearModule) (x : A) : refl A x = x :=
  AddEquiv.refl_apply x

@[simp]
theorem symm_apply_apply (f : Isometry A B) (x : A) : f.symm (f x) = x :=
  f.toAddEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (f : Isometry A B) (x : B) : f (f.symm x) = x :=
  f.toAddEquiv.apply_symm_apply x

@[simp]
theorem apply_trans (f : Isometry A B) (g : Isometry B C) (x : A) : (f.trans g) x = g (f x) :=
  f.toAddEquiv.trans_apply g.toAddEquiv x

private theorem isNondegenerate_of_isometry (f : Isometry A B) (hA : A.IsNondegenerate) :
    B.IsNondegenerate := by
  obtain ⟨hinj, hsurj⟩ := hA
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (EquivLike.surjective f) x
    obtain ⟨y, rfl⟩ := (EquivLike.surjective f) y
    apply congrArg f
    apply hinj
    ext z
    exact (f.map_pairing x z).symm.trans <|
      (DFunLike.congr_fun hxy (f z)).trans (f.map_pairing y z)
  · intro c
    let c' : CharacterModule A := c.comp f.toAddEquiv.toAddMonoidHom
    obtain ⟨x, hx⟩ := hsurj c'
    refine ⟨f x, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := (EquivLike.surjective f) y
    rw [f.map_pairing]
    exact DFunLike.congr_fun hx y

/-- Nondegeneracy is invariant under isometry. -/
theorem isNondegenerate_iff (f : Isometry A B) : A.IsNondegenerate ↔ B.IsNondegenerate :=
  ⟨isNondegenerate_of_isometry f, isNondegenerate_of_isometry f.symm⟩

end Isometry

/-- The adjoint pairing on a restricted finite bilinear module. -/
abbrev restrictPairing (H : AddSubgroup A) (x : H) : CharacterModule H where
  toFun y := A.pairing x.1 y.1
  map_zero' := A.pairing_zero_right x.1
  map_add' y z := by
    simp only [AddSubgroup.coe_add, pairing_add_right]

/-- Restrict a finite bilinear module to an additive subgroup.

No nondegeneracy conclusion is asserted: a subgroup of a nondegenerate module can have a
degenerate restricted pairing. -/
abbrev restrict (H : AddSubgroup A) : FiniteBilinearModule where
  carrier := H
  pairing :=
    { toFun := A.restrictPairing H
      map_zero' := by
        ext x
        exact A.pairing_zero_left x.1
      map_add' := fun x y ↦ by
        ext z
        exact A.pairing_add_left x.1 y.1 z.1 }
  pairing_comm x y := A.pairing_comm x.1 y.1

theorem restrict_pairing (H : AddSubgroup A) (x y : H) :
    (restrict A H).pairing x y = A.pairing x y := (rfl)

/-- Negate the pairing of a finite bilinear module. -/
abbrev neg : FiniteBilinearModule where
  carrier := A
  pairing := -A.pairing
  pairing_comm x y := congrArg Neg.neg (A.pairing_comm x y)

theorem neg_pairing (x y : A) : A.neg.pairing x y = -A.pairing x y := (rfl)

/-- The adjoint pairing on the product of two finite bilinear modules. -/
abbrev prodPairing (B : FiniteBilinearModule) (x : A × B) : CharacterModule (A × B) where
  toFun y := A.pairing x.1 y.1 + B.pairing x.2 y.2
  map_zero' := by simp
  map_add' y z := by
    simp only [Prod.fst_add, Prod.snd_add, pairing_add_right]
    abel

/-- The orthogonal direct sum of two finite bilinear modules. -/
abbrev prod (B : FiniteBilinearModule) : FiniteBilinearModule where
  carrier := A × B
  pairing :=
    { toFun := A.prodPairing B
      map_zero' := by
        ext z
        exact (congrArg₂ (· + ·) (A.pairing_zero_left z.1) (B.pairing_zero_left z.2)).trans
          (zero_add 0)
      map_add' := fun x y ↦ by
        ext z
        exact (congrArg₂ (· + ·)
          (congrArg (fun t ↦ A.pairing t z.1) (Prod.fst_add x y) ▸
            A.pairing_add_left x.1 y.1 z.1)
          (congrArg (fun t ↦ B.pairing t z.2) (Prod.snd_add x y) ▸
            B.pairing_add_left x.2 y.2 z.2)).trans
          (add_add_add_comm _ _ _ _) }
  pairing_comm x y := congrArg₂ (· + ·) (A.pairing_comm x.1 y.1) (B.pairing_comm x.2 y.2)

theorem prod_pairing (B : FiniteBilinearModule) (x y : A × B) :
    (prod A B).pairing x y = A.pairing x.1 y.1 + B.pairing x.2 y.2 := (rfl)

/-- The radical is the kernel of the adjoint pairing. -/
def radical : AddSubgroup A := A.pairing.ker

@[simp]
theorem mem_radical_iff (x : A) : x ∈ A.radical ↔ ∀ y, A.pairing x y = 0 := by
  rw [radical, AddMonoidHom.mem_ker]
  constructor
  · intro hx y
    exact DFunLike.congr_fun hx y
  · intro hx
    ext y
    exact hx y

/-- An element pairing trivially with every element is zero in a nondegenerate module. -/
theorem IsNondegenerate.eq_zero_of_forall_pairing_eq_zero (hA : A.IsNondegenerate) {x : A}
    (hx : ∀ y, A.pairing x y = 0) : x = 0 := by
  apply hA.1
  ext y
  rw [hx y, A.pairing_zero_left]

/-- The radical of a nondegenerate finite bilinear module is trivial. -/
theorem IsNondegenerate.radical_eq_bot (hA : A.IsNondegenerate) : A.radical = ⊥ := by
  apply le_antisymm
  · intro x hx
    simpa only [AddSubgroup.mem_bot] using
      eq_zero_of_forall_pairing_eq_zero A hA ((A.mem_radical_iff x).mp hx)
  · exact bot_le

/-- The orthogonal complement of a subgroup consists of the elements pairing trivially with it. -/
def orthogonalComplement (H : AddSubgroup A) : AddSubgroup A :=
  (H.toIntSubmodule.orthogonalBilin A.toBilin).toAddSubgroup

@[simp]
theorem mem_orthogonalComplement_iff (H : AddSubgroup A) (x : A) :
    x ∈ A.orthogonalComplement H ↔ ∀ y ∈ H, A.pairing x y = 0 := by
  rw [orthogonalComplement, Submodule.mem_toAddSubgroup, Submodule.mem_orthogonalBilin_iff]
  simp_rw [toBilin_apply, A.pairing_comm]
  exact ⟨fun h y hy ↦ h y hy, fun h y hy ↦ h y hy⟩

/-- Orthogonal complements reverse inclusions. -/
theorem orthogonalComplement_anti {H K : AddSubgroup A} (h : H ≤ K) :
    A.orthogonalComplement K ≤ A.orthogonalComplement H :=
  Submodule.orthogonalBilin_le (AddSubgroup.toIntSubmodule.monotone h)

@[simp]
theorem orthogonalComplement_bot : A.orthogonalComplement ⊥ = ⊤ := by
  ext x
  simp

@[simp]
theorem orthogonalComplement_top : A.orthogonalComplement ⊤ = A.radical := by
  ext x
  simp [mem_radical_iff]

/-- The orthogonal complement of the whole group is trivial for a nondegenerate pairing. -/
theorem IsNondegenerate.orthogonalComplement_top_eq_bot (hA : A.IsNondegenerate) :
    A.orthogonalComplement ⊤ = ⊥ := by
  rw [A.orthogonalComplement_top, hA.radical_eq_bot]

/-- Every subgroup is contained in its double orthogonal complement. -/
theorem le_orthogonalComplement_orthogonalComplement (H : AddSubgroup A) :
    H ≤ A.orthogonalComplement (A.orthogonalComplement H) := by
  intro x hx
  have h := Submodule.le_orthogonalBilin_orthogonalBilin (S := H.toIntSubmodule) A.toBilin_isRefl
  rw [← Submodule.toAddSubgroup_toIntSubmodule (H.toIntSubmodule.orthogonalBilin A.toBilin)] at h
  exact h hx

/-- A subgroup is bilinearly isotropic when the pairing vanishes on the subgroup square. -/
def IsIsotropic (H : AddSubgroup A) : Prop := ∀ x ∈ H, ∀ y ∈ H, A.pairing x y = 0

/-- Isotropy is equivalently inclusion in the orthogonal complement. -/
theorem isIsotropic_iff_le_orthogonalComplement (H : AddSubgroup A) :
    A.IsIsotropic H ↔ H ≤ A.orthogonalComplement H := by
  simp only [IsIsotropic, SetLike.le_def, mem_orthogonalComplement_iff]

/-- Isotropy passes to additive subgroups. -/
theorem IsIsotropic.mono {H K : AddSubgroup A} (hK : A.IsIsotropic K) (h : H ≤ K) :
    A.IsIsotropic H := by
  intro x hx y hy
  exact hK x (h hx) y (h hy)

/-- The trivial subgroup is isotropic. -/
@[simp]
theorem isIsotropic_bot : A.IsIsotropic ⊥ := by simp [IsIsotropic]

/-- A Lagrangian is a subgroup equal to its orthogonal complement. -/
def IsLagrangian (H : AddSubgroup A) : Prop := H = A.orthogonalComplement H

/-- Every Lagrangian is isotropic. -/
theorem IsLagrangian.isIsotropic {H : AddSubgroup A} (hH : A.IsLagrangian H) :
    A.IsIsotropic H := by
  rw [A.isIsotropic_iff_le_orthogonalComplement, ← hH]

end FiniteBilinearModule

end TauCeti
