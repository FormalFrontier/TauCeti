/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule

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
  map_pairing : ∀ x y, B.pairing (toAddEquiv x) (toAddEquiv y) = A.pairing x y

namespace Isometry

variable {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{v}}
  {C : FiniteBilinearModule.{w}}

/-- Two isometries are equal when their underlying additive equivalences are equal. -/
@[ext]
theorem ext {f g : Isometry A B} (h : f.toAddEquiv = g.toAddEquiv) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity isometry. -/
def refl (A : FiniteBilinearModule) : Isometry A A where
  toAddEquiv := AddEquiv.refl A
  map_pairing := by simp

/-- The inverse of an isometry. -/
def symm (f : Isometry A B) : Isometry B A where
  toAddEquiv := f.toAddEquiv.symm
  map_pairing x y := by
    simpa using (f.map_pairing (f.toAddEquiv.symm x) (f.toAddEquiv.symm y)).symm

/-- The composite of two isometries. -/
def trans (f : Isometry A B) (g : Isometry B C) : Isometry A C where
  toAddEquiv := f.toAddEquiv.trans g.toAddEquiv
  map_pairing x y := (g.map_pairing _ _).trans (f.map_pairing x y)

@[simp]
theorem refl_toAddEquiv (A : FiniteBilinearModule) : (refl A).toAddEquiv = AddEquiv.refl A := (rfl)

@[simp]
theorem symm_toAddEquiv (f : Isometry A B) : f.symm.toAddEquiv = f.toAddEquiv.symm := (rfl)

@[simp]
theorem trans_toAddEquiv (f : Isometry A B) (g : Isometry B C) :
    (f.trans g).toAddEquiv = f.toAddEquiv.trans g.toAddEquiv := (rfl)

private theorem isNondegenerate_of_isometry (f : Isometry A B) (hA : A.IsNondegenerate) :
    B.IsNondegenerate := by
  obtain ⟨hinj, hsurj⟩ := hA
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := f.toAddEquiv.surjective x
    obtain ⟨y, rfl⟩ := f.toAddEquiv.surjective y
    apply congrArg f.toAddEquiv
    apply hinj
    ext z
    exact (f.map_pairing x z).symm.trans <|
      (DFunLike.congr_fun hxy (f.toAddEquiv z)).trans (f.map_pairing y z)
  · intro c
    let c' : CharacterModule A := c.comp f.toAddEquiv.toAddMonoidHom
    obtain ⟨x, hx⟩ := hsurj c'
    refine ⟨f.toAddEquiv x, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := f.toAddEquiv.surjective y
    rw [f.map_pairing]
    exact DFunLike.congr_fun hx y

/-- Nondegeneracy is invariant under isometry. -/
theorem isNondegenerate_iff (f : Isometry A B) : A.IsNondegenerate ↔ B.IsNondegenerate :=
  ⟨isNondegenerate_of_isometry f, isNondegenerate_of_isometry f.symm⟩

end Isometry

/-- Restrict a finite bilinear module to an additive subgroup.

No nondegeneracy conclusion is asserted: a subgroup of a nondegenerate module can have a
degenerate restricted pairing. -/
abbrev restrict (H : AddSubgroup A) : FiniteBilinearModule where
  carrier := H
  pairing :=
    { toFun := fun x ↦
        show CharacterModule H from
          { toFun := fun y ↦ A.pairing x y
            map_zero' := A.pairing_zero_right x
            map_add' := by
              intro y z
              simpa only [AddSubgroup.coe_add] using A.pairing_add_right x y z }
      map_zero' := by
        ext x
        exact A.pairing_zero_left x
      map_add' := by
        intro x y
        ext z
        exact A.pairing_add_left x y z }
  pairing_comm x y := A.pairing_comm x y

theorem restrict_pairing (H : AddSubgroup A) (x y : H) :
    (restrict A H).pairing x y = A.pairing x y := (rfl)

/-- Negate the pairing of a finite bilinear module. -/
abbrev neg : FiniteBilinearModule where
  carrier := A
  pairing := -A.pairing
  pairing_comm x y := congrArg Neg.neg (A.pairing_comm x y)

theorem neg_pairing (x y : A) : A.neg.pairing x y = -A.pairing x y := (rfl)

/-- The orthogonal direct sum of two finite bilinear modules. -/
abbrev prod (B : FiniteBilinearModule) : FiniteBilinearModule where
  carrier := A × B
  pairing :=
    { toFun := fun x ↦
        show CharacterModule (A × B) from
          { toFun := fun y ↦ A.pairing x.1 y.1 + B.pairing x.2 y.2
            map_zero' := by simp
            map_add' := by
              intro y z
              simp only [Prod.fst_add, Prod.snd_add, pairing_add_right]
              abel }
      map_zero' := by
        ext z
        -- `CharacterModule` has a custom `FunLike` instance, so expose the pointwise goal
        -- explicitly.
        change A.pairing (0 : A) z.1 + B.pairing (0 : B) z.2 = 0
        exact (congrArg₂ (· + ·) (A.pairing_zero_left z.1) (B.pairing_zero_left z.2)).trans
          (zero_add 0)
      map_add' := by
        intro x y
        ext z
        -- See the corresponding comment in `map_zero'`.
        change A.pairing (x.1 + y.1) z.1 + B.pairing (x.2 + y.2) z.2 =
          (A.pairing x.1 z.1 + B.pairing x.2 z.2) +
            (A.pairing y.1 z.1 + B.pairing y.2 z.2)
        rw [A.pairing_add_left, B.pairing_add_left]
        abel }
  pairing_comm x y := by
    -- See the corresponding comment in `map_zero'`.
    change A.pairing x.1 y.1 + B.pairing x.2 y.2 =
      A.pairing y.1 x.1 + B.pairing y.2 x.2
    rw [A.pairing_comm x.1 y.1, B.pairing_comm x.2 y.2]

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
def orthogonalComplement (H : AddSubgroup A) : AddSubgroup A where
  carrier := {x | ∀ y ∈ H, A.pairing x y = 0}
  zero_mem' := by
    intro y hy
    exact A.pairing_zero_left y
  add_mem' := by
    intro x y hx hy z hz
    rw [A.pairing_add_left, hx z hz, hy z hz, zero_add]
  neg_mem' := by
    intro x hx y hy
    rw [A.pairing_neg_left, hx y hy, neg_zero]

@[simp]
theorem mem_orthogonalComplement_iff (H : AddSubgroup A) (x : A) :
    x ∈ A.orthogonalComplement H ↔ ∀ y ∈ H, A.pairing x y = 0 := Iff.rfl

/-- Orthogonal complements reverse inclusions. -/
theorem orthogonalComplement_mono {H K : AddSubgroup A} (h : H ≤ K) :
    A.orthogonalComplement K ≤ A.orthogonalComplement H := by
  intro x hx y hy
  exact hx y (h hy)

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
  intro x hx y hy
  rw [A.pairing_comm]
  exact hy x hx

/-- A subgroup is bilinearly isotropic when the pairing vanishes on the subgroup square. -/
def IsIsotropic (H : AddSubgroup A) : Prop := ∀ x ∈ H, ∀ y ∈ H, A.pairing x y = 0

/-- Isotropy is equivalently inclusion in the orthogonal complement. -/
theorem isIsotropic_iff_le_orthogonalComplement (H : AddSubgroup A) :
    A.IsIsotropic H ↔ H ≤ A.orthogonalComplement H := Iff.rfl

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
