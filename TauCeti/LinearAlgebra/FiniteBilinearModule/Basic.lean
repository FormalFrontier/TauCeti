/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Finite bilinear modules

A finite abelian group equipped with a symmetric biadditive pairing into `ℚ/ℤ`.  The pairing
is stored as its adjoint into Mathlib's `CharacterModule`; nondegeneracy asserts that this
adjoint is bijective.

This file provides the basic constructions needed for discriminant forms: isometries, restriction,
form negation, orthogonal direct sums, radicals, orthogonal complements, isotropic elements,
isotropic subgroups, and Lagrangians.  Nondegeneracy remains a predicate because restriction to a
subgroup can be degenerate.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

## Main definitions

* `TauCeti.FiniteBilinearModule`: a finite abelian group with a symmetric `ℚ/ℤ`-valued pairing.
* `TauCeti.FiniteBilinearModule.toBilin`: the pairing as a `ℤ`-bilinear map.
* `TauCeti.FiniteBilinearModule.IsNondegenerate`: bijectivity of the adjoint pairing.
* `TauCeti.FiniteBilinearModule.Isometry`: a pairing-preserving additive equivalence.
* `TauCeti.FiniteBilinearModule.orthogonalComplement`: the orthogonal complement of a subgroup.
* `TauCeti.FiniteBilinearModule.IsIsotropicElem`: vanishing of the self-pairing on an element.
* `TauCeti.FiniteBilinearModule.IsIsotropic`: vanishing of the pairing on a subgroup.
* `TauCeti.FiniteBilinearModule.IsLagrangian`: equality with the orthogonal complement.

## Main results

* `TauCeti.FiniteBilinearModule.Isometry.map_orthogonalComplement`: an isometry carries
  orthogonal complements to orthogonal complements.
* `TauCeti.FiniteBilinearModule.Isometry.isIsotropic_map_iff`: an isometry transports isotropic
  subgroups.
* `TauCeti.FiniteBilinearModule.Isometry.isLagrangian_map_iff`: an isometry transports Lagrangian
  subgroups.
-/

public section

namespace TauCeti

universe u v w

section CharacterModuleDuality

/-- The canonical embedding of `AddCircle (1 : ℚ)` into `AddCircle (1 : ℝ)`. -/
private noncomputable def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (Rat.castHom ℝ).toAddMonoidHom)
    (fun x hx ↦ by
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        map_zsmul]
      have : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
          ((Rat.castHom ℝ).toAddMonoidHom (1 : ℚ)) = 0 := by
        simp only [RingHom.toAddMonoidHom_eq_coe]
        rw [QuotientAddGroup.coe_mk', QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
        exact ⟨1, by simp⟩
      rw [this, smul_zero])

private theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  intro a b hab
  induction a using QuotientAddGroup.induction_on with | H a =>
  induction b using QuotientAddGroup.induction_on with | H b =>
  have hdiff : ratAddCircleToReal (QuotientAddGroup.mk a - QuotientAddGroup.mk b) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hab
  rw [← QuotientAddGroup.mk_sub] at hdiff
  simp only [ratAddCircleToReal, QuotientAddGroup.lift_mk', AddMonoidHom.coe_comp,
    Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    QuotientAddGroup.coe_mk'] at hdiff
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at hdiff
  obtain ⟨n, hn⟩ := hdiff
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  refine ⟨-n, ?_⟩
  rw [zsmul_eq_mul, mul_one] at hn ⊢
  have hn' : (n : ℝ) = ((a - b : ℚ) : ℝ) := hn
  have hn'' : (n : ℚ) = a - b := by exact_mod_cast hn'
  have : (-n : ℚ) = -a + b := by
    rw [hn'']
    ring
  exact this

/-- The injective map from `CharacterModule M` to `AddChar M Circle`. -/
private noncomputable def characterModuleToAddChar (M : Type*) [AddCommGroup M] :
    CharacterModule M → AddChar M Circle := fun c ↦
  { toFun := fun m ↦ AddCircle.toCircle (ratAddCircleToReal (c m))
    map_zero_eq_one' := by simp
    map_add_eq_mul' := fun x y ↦ by
      simp only [map_add, AddCircle.toCircle_add] }

private theorem characterModuleToAddChar_injective (M : Type*) [AddCommGroup M] :
    Function.Injective (characterModuleToAddChar M) := by
  intro c₁ c₂ h
  ext m
  have h_eq : AddCircle.toCircle (ratAddCircleToReal (c₁ m)) =
      AddCircle.toCircle (ratAddCircleToReal (c₂ m)) := by
    exact DFunLike.congr_fun h m
  have h_real := AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero h_eq
  exact ratAddCircleToReal_injective h_real

/-- The character module of a finite abelian group is finite. -/
instance (M : Type*) [AddCommGroup M] [Finite M] : Finite (CharacterModule M) := by
  have : Finite (AddChar M Circle) :=
    Finite.of_equiv (AddChar M ℂ) AddChar.circleEquivComplex.symm.toEquiv
  exact Finite.of_injective (characterModuleToAddChar M) (characterModuleToAddChar_injective M)

private theorem card_characterModule_le (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) ≤ Nat.card M := by
  cases nonempty_fintype M
  have : Fintype (AddChar M Circle) :=
    Fintype.ofEquiv (AddChar M ℂ) AddChar.circleEquivComplex.symm.toEquiv
  have : Fintype (CharacterModule M) := Fintype.ofFinite _
  have hle := Fintype.card_le_of_injective (characterModuleToAddChar M)
    (characterModuleToAddChar_injective M)
  have hequiv : Fintype.card (AddChar M Circle) = Fintype.card (AddChar M ℂ) :=
    Fintype.card_congr AddChar.circleEquivComplex.toEquiv
  rw [hequiv, AddChar.card_eq] at hle
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hle

/-- The double dual evaluation map is injective. -/
private def characterModuleEval (M : Type*) [AddCommGroup M] :
    M →+ CharacterModule (CharacterModule M) where
  toFun m :=
    { toFun := fun c ↦ c m
      map_zero' := rfl
      map_add' := fun c₁ c₂ ↦ rfl }
  map_zero' := by ext c; exact map_zero c
  map_add' x y := by ext c; exact map_add c x y

private theorem characterModuleEval_injective (M : Type*) [AddCommGroup M] :
    Function.Injective (characterModuleEval M) := by
  intro x y hxy
  have h : ∀ c : CharacterModule M, c (x - y) = 0 := fun c ↦ by
    have hc : c x = c y := DFunLike.congr_fun hxy c
    rw [map_sub, hc, sub_self]
  have hzero := CharacterModule.eq_zero_of_character_apply h
  exact sub_eq_zero.mp hzero

/-- The cardinality of the character module equals the cardinality of the group. -/
theorem natCard_characterModule (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) = Nat.card M := by
  cases nonempty_fintype M
  have : Fintype (CharacterModule M) := Fintype.ofFinite _
  have : Fintype (CharacterModule (CharacterModule M)) := Fintype.ofFinite _
  have h1 : Fintype.card M ≤ Fintype.card (CharacterModule (CharacterModule M)) :=
    Fintype.card_le_of_injective (characterModuleEval M) (characterModuleEval_injective M)
  have h2 : Fintype.card (CharacterModule (CharacterModule M)) ≤
      Fintype.card (CharacterModule M) := by
    have hle := card_characterModule_le (CharacterModule M)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hle
  have h3 : Fintype.card (CharacterModule M) ≤ Fintype.card M := by
    have hle := card_characterModule_le M
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hle
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact le_antisymm h3 (h1.trans h2)

end CharacterModuleDuality

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

theorem isRefl_toBilin : A.toBilin.IsRefl := fun x y h ↦ by
  rw [toBilin_apply, A.pairing_comm, ← toBilin_apply]
  exact h

/-- A finite bilinear module is nondegenerate when its adjoint pairing is bijective. -/
def IsNondegenerate : Prop := Function.Bijective A.pairing

/-- An injective pairing on a finite module is nondegenerate by finite duality. -/
theorem isNondegenerate_of_injective (hA : Function.Injective A.pairing) : A.IsNondegenerate := by
  cases nonempty_fintype A
  have : Fintype (CharacterModule A) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card A.pairing).mpr ⟨hA, ?_⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, natCard_characterModule]

/-- Nondegeneracy is equivalent to injectivity of the adjoint pairing for a finite module. -/
theorem isNondegenerate_iff_injective : A.IsNondegenerate ↔ Function.Injective A.pairing :=
  ⟨And.left, A.isNondegenerate_of_injective⟩

/-- The adjoint pairing of a nondegenerate finite module is injective. -/
theorem IsNondegenerate.injective (hA : A.IsNondegenerate) : Function.Injective A.pairing :=
  hA.1

/-- The adjoint pairing of a nondegenerate finite module is surjective. -/
theorem IsNondegenerate.surjective (hA : A.IsNondegenerate) : Function.Surjective A.pairing :=
  hA.2

/-- The adjoint pairing of a nondegenerate finite module is bijective. -/
theorem IsNondegenerate.bijective (hA : A.IsNondegenerate) : Function.Bijective A.pairing :=
  hA

/-- A nondegenerate pairing identifies its group with the full character module. -/
noncomputable def adjointEquiv (hA : A.IsNondegenerate) : A ≃+ CharacterModule A :=
  AddEquiv.ofBijective A.pairing hA.bijective

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
theorem refl_apply (A : FiniteBilinearModule) (x : A) : refl A x = x :=
  AddEquiv.refl_apply x

@[simp]
theorem symm_apply_apply (f : Isometry A B) (x : A) : f.symm (f x) = x :=
  f.toAddEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (f : Isometry A B) (x : B) : f (f.symm x) = x :=
  f.toAddEquiv.apply_symm_apply x

@[simp]
theorem trans_apply (f : Isometry A B) (g : Isometry B C) (x : A) : (f.trans g) x = g (f x) :=
  f.toAddEquiv.trans_apply g.toAddEquiv x

/-- Nondegeneracy transfers along an isometry. -/
theorem isNondegenerate (f : Isometry A B) (hA : A.IsNondegenerate) : B.IsNondegenerate := by
  rw [B.isNondegenerate_iff_injective]
  intro x y hxy
  obtain ⟨x, rfl⟩ := (EquivLike.surjective f) x
  obtain ⟨y, rfl⟩ := (EquivLike.surjective f) y
  apply congrArg f
  apply hA.injective
  ext z
  have h := DFunLike.congr_fun hxy (f z)
  simpa only [map_pairing] using h

/-- Nondegeneracy is invariant under isometry. -/
theorem isNondegenerate_iff (f : Isometry A B) : A.IsNondegenerate ↔ B.IsNondegenerate :=
  ⟨f.isNondegenerate, f.symm.isNondegenerate⟩

end Isometry

/-- Restrict a finite bilinear module to an additive subgroup.

No nondegeneracy conclusion is asserted: a subgroup of a nondegenerate module can have a
degenerate restricted pairing. -/
abbrev restrict (H : AddSubgroup A) : FiniteBilinearModule where
  carrier := H
  pairing :=
    { toFun := fun (x : H) ↦
        { toFun := fun (y : H) ↦ A.pairing x.1 y.1
          map_zero' := A.pairing_zero_right x.1
          map_add' := fun y z ↦ by
            simp only [AddSubgroup.coe_add, pairing_add_right] }
      map_zero' := by
        ext (x : H)
        exact A.pairing_zero_left x.1
      map_add' := fun (x y : H) ↦ by
        ext (z : H)
        exact A.pairing_add_left x.1 y.1 z.1 }
  pairing_comm x y := A.pairing_comm x.1 y.1

theorem restrict_pairing (H : AddSubgroup A) (x y : H) :
    (restrict A H).pairing x y = A.pairing x.1 y.1 := (rfl)

/-- Negate the pairing of a finite bilinear module. -/
abbrev neg : FiniteBilinearModule where
  carrier := A
  pairing := -A.pairing
  pairing_comm x y := congrArg Neg.neg (A.pairing_comm x y)

theorem neg_pairing (x y : A) : A.neg.pairing x y = -A.pairing x y := (rfl)

/-- Form negation preserves nondegeneracy of a finite bilinear module. -/
@[simp]
theorem isNondegenerate_neg : A.neg.IsNondegenerate ↔ A.IsNondegenerate := by
  rw [A.neg.isNondegenerate_iff_injective, A.isNondegenerate_iff_injective]
  constructor
  · intro h x y hxy
    apply h
    ext z
    exact congrArg Neg.neg (DFunLike.congr_fun hxy z)
  · intro h x y hxy
    apply h
    ext z
    have := DFunLike.congr_fun hxy z
    exact neg_inj.mp this

/-- The orthogonal direct sum of two finite bilinear modules. -/
abbrev prod (B : FiniteBilinearModule) : FiniteBilinearModule where
  carrier := A.carrier × B.carrier
  pairing :=
    { toFun := fun x ↦
        { toFun := fun y ↦ A.pairing x.1 y.1 + B.pairing x.2 y.2
          map_zero' := by
            simp only [Prod.fst_zero, Prod.snd_zero, pairing_zero_right, add_zero]
          map_add' := fun y z ↦ by
            simp only [Prod.fst_add, Prod.snd_add, pairing_add_right]
            abel }
      map_zero' := by
        ext ⟨z₁, z₂⟩
        exact (congrArg₂ (· + ·) (A.pairing_zero_left z₁) (B.pairing_zero_left z₂)).trans
          (add_zero 0)
      map_add' := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ↦ by
        ext ⟨z₁, z₂⟩
        exact (congrArg₂ (· + ·) (A.pairing_add_left x₁ y₁ z₁) (B.pairing_add_left x₂ y₂ z₂)).trans
          (add_add_add_comm (A.pairing x₁ z₁) (A.pairing y₁ z₁) (B.pairing x₂ z₂)
            (B.pairing y₂ z₂)) }
  pairing_comm := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ↦
    congrArg₂ (· + ·) (A.pairing_comm x₁ y₁) (B.pairing_comm x₂ y₂)

theorem prod_pairing (B : FiniteBilinearModule) (x y : A.carrier × B.carrier) :
    (prod A B).pairing x y = A.pairing x.1 y.1 + B.pairing x.2 y.2 :=
  rfl

/-- An orthogonal direct sum of finite bilinear modules is nondegenerate if and only if both
factors are nondegenerate. -/
@[simp]
theorem isNondegenerate_prod (B : FiniteBilinearModule) :
    (A.prod B).IsNondegenerate ↔ A.IsNondegenerate ∧ B.IsNondegenerate := by
  rw [(A.prod B).isNondegenerate_iff_injective, A.isNondegenerate_iff_injective,
    B.isNondegenerate_iff_injective]
  constructor
  · intro h
    constructor
    · intro x y hxy
      have heq : (A.prod B).pairing (x, 0) = (A.prod B).pairing (y, 0) := by
        ext ⟨u, v⟩
        have h1 : (A.prod B).pairing (x, 0) (u, v) = A.pairing x u := by
          rw [prod_pairing, pairing_zero_left, add_zero]
        have h2 : (A.prod B).pairing (y, 0) (u, v) = A.pairing y u := by
          rw [prod_pairing, pairing_zero_left, add_zero]
        rw [h1, h2, DFunLike.congr_fun hxy u]
      have := h heq
      exact Prod.ext_iff.mp this |>.1
    · intro x y hxy
      have heq : (A.prod B).pairing (0, x) = (A.prod B).pairing (0, y) := by
        ext ⟨u, v⟩
        have h1 : (A.prod B).pairing (0, x) (u, v) = B.pairing x v := by
          rw [prod_pairing, pairing_zero_left, zero_add]
        have h2 : (A.prod B).pairing (0, y) (u, v) = B.pairing y v := by
          rw [prod_pairing, pairing_zero_left, zero_add]
        rw [h1, h2, DFunLike.congr_fun hxy v]
      have := h heq
      exact Prod.ext_iff.mp this |>.2
  · rintro ⟨hA, hB⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hxy
    have hx : A.pairing x₁ = A.pairing x₂ := by
      ext u
      have heq := DFunLike.congr_fun hxy (u, 0)
      have h1 : (A.prod B).pairing (x₁, y₁) (u, 0) = A.pairing x₁ u := by
        rw [prod_pairing, pairing_zero_right, add_zero]
      have h2 : (A.prod B).pairing (x₂, y₂) (u, 0) = A.pairing x₂ u := by
        rw [prod_pairing, pairing_zero_right, add_zero]
      exact h1.symm.trans (heq.trans h2)
    have hy : B.pairing y₁ = B.pairing y₂ := by
      ext v
      have heq := DFunLike.congr_fun hxy (0, v)
      have h1 : (A.prod B).pairing (x₁, y₁) (0, v) = B.pairing y₁ v := by
        rw [prod_pairing, pairing_zero_right, zero_add]
      have h2 : (A.prod B).pairing (x₂, y₂) (0, v) = B.pairing y₂ v := by
        rw [prod_pairing, pairing_zero_right, zero_add]
      exact h1.symm.trans (heq.trans h2)
    exact Prod.ext (hA hx) (hB hy)

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

/-- A finite bilinear module is nondegenerate if and only if its radical is trivial. -/
theorem isNondegenerate_iff_radical_eq_bot : A.IsNondegenerate ↔ A.radical = ⊥ :=
  A.isNondegenerate_iff_injective.trans A.pairing.ker_eq_bot_iff.symm

/-- An element pairing trivially with every element is zero in a nondegenerate module. -/
theorem IsNondegenerate.eq_zero_of_forall_pairing_eq_zero (hA : A.IsNondegenerate) {x : A}
    (hx : ∀ y, A.pairing x y = 0) : x = 0 := by
  apply hA.injective
  ext y
  rw [hx y, A.pairing_zero_left]

/-- The radical of a nondegenerate finite bilinear module is trivial. -/
theorem IsNondegenerate.radical_eq_bot (hA : A.IsNondegenerate) : A.radical = ⊥ :=
  A.isNondegenerate_iff_radical_eq_bot.mp hA

/-- A finite bilinear module with trivial radical is nondegenerate. -/
theorem isNondegenerate_of_radical_eq_bot (h : A.radical = ⊥) : A.IsNondegenerate :=
  A.isNondegenerate_iff_radical_eq_bot.mpr h

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
  have h := Submodule.le_orthogonalBilin_orthogonalBilin (S := H.toIntSubmodule) A.isRefl_toBilin
  rw [← Submodule.toAddSubgroup_toIntSubmodule (H.toIntSubmodule.orthogonalBilin A.toBilin)] at h
  exact h hx

/-- An element of a finite bilinear module is isotropic when its self-pairing vanishes. -/
def IsIsotropicElem (x : A) : Prop := A.pairing x x = 0

theorem isIsotropicElem_def (x : A) : A.IsIsotropicElem x ↔ A.pairing x x = 0 := Iff.rfl

/-- The zero element is isotropic. -/
@[simp]
theorem isIsotropicElem_zero : A.IsIsotropicElem 0 := by
  rw [isIsotropicElem_def, pairing_zero_left]

/-- The negative of an isotropic element is isotropic. -/
@[simp]
theorem isIsotropicElem_neg (x : A) : A.IsIsotropicElem (-x) ↔ A.IsIsotropicElem x := by
  rw [isIsotropicElem_def, isIsotropicElem_def, pairing_neg_left, pairing_neg_right, neg_neg]

/-- An isometry preserves isotropic elements. -/
@[simp]
theorem Isometry.isIsotropicElem_iff {B : FiniteBilinearModule} (f : Isometry A B) (x : A) :
    B.IsIsotropicElem (f x) ↔ A.IsIsotropicElem x := by
  rw [isIsotropicElem_def, isIsotropicElem_def, map_pairing]

/-- Form negation preserves isotropic elements. -/
@[simp]
theorem isIsotropicElem_neg_module (x : A) : A.neg.IsIsotropicElem x ↔ A.IsIsotropicElem x := by
  constructor
  · exact neg_eq_zero.mp
  · exact neg_eq_zero.mpr

/-- An element in an orthogonal product is isotropic if and only if the sum of its component
pairings vanishes. -/
@[simp]
theorem isIsotropicElem_prod (B : FiniteBilinearModule) (x : A) (y : B) :
    (A.prod B).IsIsotropicElem (x, y) ↔ A.pairing x x + B.pairing y y = 0 := by
  rfl

/-- A subgroup is bilinearly isotropic when the pairing vanishes on the subgroup square. -/
def IsIsotropic (H : AddSubgroup A) : Prop := ∀ x ∈ H, ∀ y ∈ H, A.pairing x y = 0

/-- Bilinear isotropy of a subgroup, unfolded to its defining property. -/
theorem isIsotropic_def {H : AddSubgroup A} :
    A.IsIsotropic H ↔ ∀ x ∈ H, ∀ y ∈ H, A.pairing x y = 0 :=
  Iff.rfl

/-- An element belonging to an isotropic subgroup is isotropic. -/
theorem isIsotropicElem_of_mem_isIsotropic {H : AddSubgroup A} (hH : A.IsIsotropic H) {x : A}
    (hx : x ∈ H) : A.IsIsotropicElem x :=
  hH x hx x hx

/-- The cyclic subgroup generated by `x` is isotropic if and only if `x` is isotropic. -/
theorem isIsotropic_zmultiples_iff (x : A) :
    A.IsIsotropic (AddSubgroup.zmultiples x) ↔ A.IsIsotropicElem x := by
  constructor
  · intro h
    exact isIsotropicElem_of_mem_isIsotropic A h (AddSubgroup.mem_zmultiples x)
  · intro h u hu v hv
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    have h1 : A.pairing (m • x) (n • x) = m • n • A.pairing x x := by
      rw [A.pairing_comm (m • x) (n • x), map_zsmul, A.pairing_comm (n • x) x, map_zsmul]
    rw [isIsotropicElem_def] at h
    rw [h1, h, smul_zero, smul_zero]

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

/-- A subgroup is Lagrangian exactly when it equals its orthogonal complement. -/
theorem isLagrangian_def (H : AddSubgroup A) :
    A.IsLagrangian H ↔ H = A.orthogonalComplement H := Iff.rfl

/-- Every Lagrangian is isotropic. -/
theorem IsLagrangian.isIsotropic {H : AddSubgroup A} (hH : A.IsLagrangian H) :
    A.IsIsotropic H := by
  rw [A.isIsotropic_iff_le_orthogonalComplement, ← hH]

/-- An isometry carries orthogonal complements to orthogonal complements. -/
@[simp]
theorem Isometry.map_orthogonalComplement {B : FiniteBilinearModule} (f : Isometry A B)
    (H : AddSubgroup A) :
    (A.orthogonalComplement H).map f.toAddEquiv =
      B.orthogonalComplement (H.map f.toAddEquiv) := by
  ext y
  rw [AddSubgroup.mem_map, B.mem_orthogonalComplement_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ w hw
    obtain ⟨z, hz, rfl⟩ := AddSubgroup.mem_map.mp hw
    exact (f.map_pairing x z).trans ((A.mem_orthogonalComplement_iff H x).mp hx z hz)
  · intro hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    rw [A.mem_orthogonalComplement_iff]
    intro z hz
    rw [← f.map_pairing (f.symm y) z, f.apply_symm_apply]
    exact hy (f z) (AddSubgroup.mem_map.mpr ⟨z, hz, rfl⟩)

/-- An isometry transports isotropic subgroups. -/
@[simp]
theorem Isometry.isIsotropic_map_iff {B : FiniteBilinearModule} (f : Isometry A B)
    (H : AddSubgroup A) :
    B.IsIsotropic (H.map f.toAddEquiv) ↔ A.IsIsotropic H := by
  rw [B.isIsotropic_iff_le_orthogonalComplement, A.isIsotropic_iff_le_orthogonalComplement,
    ← f.map_orthogonalComplement, AddSubgroup.map_le_map_iff_of_injective f.toAddEquiv.injective]

/-- An isometry transports Lagrangian subgroups. -/
@[simp]
theorem Isometry.isLagrangian_map_iff {B : FiniteBilinearModule} (f : Isometry A B)
    (H : AddSubgroup A) :
    B.IsLagrangian (H.map f.toAddEquiv) ↔ A.IsLagrangian H := by
  rw [isLagrangian_def, isLagrangian_def, ← f.map_orthogonalComplement,
    (AddSubgroup.map_injective f.toAddEquiv.injective).eq_iff]

end FiniteBilinearModule

end TauCeti
