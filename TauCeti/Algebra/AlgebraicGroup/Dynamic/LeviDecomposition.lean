/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# The dynamic Levi decomposition as a semidirect product

Let `l : 𝔾ₘ → G` be a cocharacter of an affine group. The dynamic parabolic `P(l)` has a
limit homomorphism onto its Levi subgroup `Z(l)`, whose kernel is the dynamic unipotent subgroup
`U(l)`. The inclusion of `Z(l)` in `P(l)` splits this homomorphism.

This file packages those facts as a split group extension and applies Mathlib's general theorem
for split extensions. For every commutative value algebra `A` this gives the canonical
semidirect-product equivalence

```text
U(l)(A) ⋊ Z(l)(A) ≃* P(l)(A).
```

The action is conjugation through the two subgroup inclusions. Characteristic lemmas identify
the equivalence with multiplication, its Levi coordinate with the limit, and its unipotent
coordinate with `g · limit(g)⁻¹`. Thus downstream representability arguments can use the bundled
equivalence without reopening the existence-and-uniqueness proof of the pointwise Levi
factorization.

## Main declarations

* `TauCeti.Cocharacter.limitToLevi`: the limit homomorphism with codomain restricted to the Levi
  subgroup.
* `TauCeti.Cocharacter.leviGroupExtension`: the exact sequence
  `1 → U(l)(A) → P(l)(A) → Z(l)(A) → 1`.
* `TauCeti.Cocharacter.leviGroupExtensionSplitting`: its canonical splitting.
* `TauCeti.Cocharacter.leviConjugation`: the resulting action of `Z(l)(A)` on `U(l)(A)`.
* `TauCeti.Cocharacter.leviDecompositionMulEquiv`: the dynamic Levi decomposition as a
  multiplicative equivalence.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic approach to parabolic subgroups and Levi decomposition in Layer 7,
"Structure theory", of the ReductiveGroups roadmap.
-/

public section

open WithConv

namespace TauCeti.Cocharacter

universe u v w

noncomputable section

variable {R : Type u} {H : Type v} (A : Type w)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [CommSemiring A] [Algebra R A]
variable (l : H →ₐc[R] LaurentPolynomial R)

/-- The dynamic limit homomorphism, with its codomain restricted to the Levi subgroup. -/
noncomputable def limitToLevi : parabolic A l →* levi A l :=
  (limit A l).codRestrict (levi A l) (limit_mem_levi (A := A) (l := l))

/-- The Levi-valued limit has the same underlying point as the ambient-valued limit. -/
@[simp]
theorem coe_limitToLevi_apply (g : parabolic A l) :
    (limitToLevi A l g : WithConv (H →ₐ[R] A)) = limit A l g :=
  by simp [limitToLevi]

/-- Inclusion of the dynamic unipotent subgroup into the dynamic parabolic. -/
noncomputable def unipotentToParabolic : unipotent A l →* parabolic A l :=
  Subgroup.inclusion (unipotent_le_parabolic (A := A) (l := l))

/-- Inclusion of the dynamic Levi subgroup into the dynamic parabolic. -/
noncomputable def leviToParabolic : levi A l →* parabolic A l :=
  Subgroup.inclusion (levi_le_parabolic (A := A) (l := l))

/-- The unipotent inclusion does not change the underlying point. -/
@[simp]
theorem coe_unipotentToParabolic_apply (g : unipotent A l) :
    (unipotentToParabolic A l g : WithConv (H →ₐ[R] A)) = g :=
  by simp [unipotentToParabolic]

/-- The Levi inclusion does not change the underlying point. -/
@[simp]
theorem coe_leviToParabolic_apply (g : levi A l) :
    (leviToParabolic A l g : WithConv (H →ₐ[R] A)) = g :=
  by simp [leviToParabolic]

/-- The dynamic unipotent subgroup is exactly the kernel of the Levi-valued limit, as a subgroup
of the dynamic parabolic. -/
theorem range_unipotentToParabolic_eq_ker_limitToLevi :
    (unipotentToParabolic A l).range = (limitToLevi A l).ker := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    obtain ⟨_, hu⟩ := mem_unipotent_iff.mp u.2
    exact hu
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    have hlimit : limit A l g = 1 := congrArg Subtype.val hg
    have hu : (g : WithConv (H →ₐ[R] A)) ∈ unipotent A l :=
      mem_unipotent_iff.mpr ⟨g.2, hlimit⟩
    exact ⟨⟨g, hu⟩, Subtype.ext rfl⟩

/-- The Levi-valued limit is surjective; the Levi inclusion supplies a preimage of every
element. -/
theorem limitToLevi_surjective : Function.Surjective (limitToLevi A l) := by
  intro z
  refine ⟨leviToParabolic A l z, ?_⟩
  apply Subtype.ext
  exact limit_of_mem_levi z.2

/-- The dynamic parabolic is an extension of its Levi subgroup by its dynamic unipotent
subgroup. -/
noncomputable def leviGroupExtension :
    GroupExtension (unipotent A l) (parabolic A l) (levi A l) where
  inl := unipotentToParabolic A l
  rightHom := limitToLevi A l
  inl_injective := Subgroup.inclusion_injective (unipotent_le_parabolic (A := A) (l := l))
  range_inl_eq_ker_rightHom := range_unipotentToParabolic_eq_ker_limitToLevi A l
  rightHom_surjective := limitToLevi_surjective A l

/-- The kernel inclusion of the dynamic Levi group extension is the subgroup inclusion. -/
@[simp]
theorem leviGroupExtension_inl_apply (u : unipotent A l) :
    (leviGroupExtension A l).inl u = unipotentToParabolic A l u := (rfl)

/-- The projection of the dynamic Levi group extension is the Levi-valued limit. -/
@[simp]
theorem leviGroupExtension_rightHom_apply (g : parabolic A l) :
    (leviGroupExtension A l).rightHom g = limitToLevi A l g := (rfl)

/-- The Levi inclusion canonically splits the dynamic Levi group extension. -/
noncomputable def leviGroupExtensionSplitting :
    (leviGroupExtension A l).Splitting where
  __ := leviToParabolic A l
  rightInverse_rightHom z := by
    rw [leviGroupExtension_rightHom_apply]
    apply Subtype.ext
    rw [coe_limitToLevi_apply]
    -- Normalize the monoid-hom coercion before comparing the two subtype witnesses.
    change limit A l (leviToParabolic A l z) = z
    have hinc : leviToParabolic A l z =
        (⟨z, levi_le_parabolic z.2⟩ : parabolic A l) := Subtype.ext rfl
    rw [hinc]
    exact limit_of_mem_levi z.2

/-- The canonical splitting of the dynamic Levi extension is the Levi subgroup inclusion. -/
@[simp]
theorem leviGroupExtensionSplitting_apply (z : levi A l) :
    leviGroupExtensionSplitting A l z = leviToParabolic A l z := (rfl)

/-- The action of the dynamic Levi subgroup on the dynamic unipotent subgroup by conjugation. -/
noncomputable def leviConjugation : levi A l →* MulAut (unipotent A l) :=
  (leviGroupExtensionSplitting A l).conjAct

/-- The Levi action is the conjugation action associated to the dynamic Levi group extension. -/
theorem leviConjugation_apply (z : levi A l) (u : unipotent A l) :
    leviConjugation A l z u =
      (leviGroupExtension A l).conjAct (leviToParabolic A l z) u := (rfl)

/-- The Levi action is ordinary conjugation on the underlying ambient points. -/
@[simp]
theorem coe_leviConjugation_apply (z : levi A l) (u : unipotent A l) :
    (leviConjugation A l z u : WithConv (H →ₐ[R] A)) =
      (z : WithConv (H →ₐ[R] A)) * u * z⁻¹ := by
  have h := (leviGroupExtension A l).inl_conjAct_comm
    (e := leviGroupExtensionSplitting A l z) (n := u)
  have h' := congrArg (fun p : parabolic A l => (p : WithConv (H →ₐ[R] A))) h
  simpa only [leviGroupExtension_inl_apply, leviGroupExtensionSplitting_apply,
    leviConjugation_apply, coe_unipotentToParabolic_apply, coe_leviToParabolic_apply,
    Subgroup.coe_mul, Subgroup.coe_inv] using h'

/-- **The dynamic Levi decomposition.** The semidirect product of the dynamic unipotent and Levi
subgroups is canonically equivalent to the dynamic parabolic. -/
noncomputable def leviDecompositionMulEquiv :
    (unipotent A l) ⋊[leviConjugation A l] (levi A l) ≃* parabolic A l :=
  (leviGroupExtensionSplitting A l).semidirectProductMulEquiv

/-- The dynamic Levi decomposition equivalence sends `(u, z)` to the product of the two subgroup
inclusions. -/
@[simp]
theorem leviDecompositionMulEquiv_apply
    (x : (unipotent A l) ⋊[leviConjugation A l] (levi A l)) :
    leviDecompositionMulEquiv A l x =
      unipotentToParabolic A l x.left * leviToParabolic A l x.right := (rfl)

/-- The Levi coordinate of the inverse decomposition is the limit of the parabolic point. -/
@[simp]
theorem leviDecompositionMulEquiv_symm_apply_right (g : parabolic A l) :
    ((leviDecompositionMulEquiv A l).symm g).right = limitToLevi A l g := (rfl)

/-- The unipotent coordinate of the inverse decomposition is `g * limit(g)⁻¹`. -/
@[simp]
theorem coe_leviDecompositionMulEquiv_symm_apply_left (g : parabolic A l) :
    (((leviDecompositionMulEquiv A l).symm g).left : WithConv (H →ₐ[R] A)) =
      (g : WithConv (H →ₐ[R] A)) * (limit A l g)⁻¹ := by
  have h := congrArg Subtype.val ((leviDecompositionMulEquiv A l).apply_symm_apply g)
  rw [leviDecompositionMulEquiv_apply] at h
  simp only [coe_unipotentToParabolic_apply, coe_leviToParabolic_apply, Subgroup.coe_mul] at h
  rw [← h, leviDecompositionMulEquiv_symm_apply_right, coe_limitToLevi_apply]
  group

end

end TauCeti.Cocharacter
