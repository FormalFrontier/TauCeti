/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.SemidirectProduct.Normal
import Mathlib.Tactic.Group

/-!
# Equivariance of multiplication from a normal semidirect product

Let `i : N ⟶ G` and `j : H ⟶ G` be normal subgroup objects. Ambient conjugation acts
simultaneously on both factors of the semidirect product `N ⋊ H`: a generalized point `g` sends
`(n, h)` to `(gng⁻¹, ghg⁻¹)`. This file constructs that internal action and proves that the
canonical multiplication homomorphism

```text
N ⋊ H ⟶ G,    (n, h) ↦ i(n) * j(h)
```

is equivariant for simultaneous conjugation on the source and conjugation on the target.

This is the equivariance input for proving that the scheme-theoretic image of this multiplication
map is normal. Together with connectedness, smoothness, and unipotence of the image, that image is
the binary product used in the maximal-dimension construction of the unipotent radical.

## Main declarations

* `TauCeti.GrpObj.Action.normalSemidirectConjugation`: simultaneous ambient conjugation on the
  normal semidirect product.
* `TauCeti.GrpObj.Action.normalSemidirectMul_equivariant`: multiplication from the normal
  semidirect product intertwines simultaneous conjugation with ambient conjugation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §6.a.
* A. Borel, *Linear Algebraic Groups*, Proposition 14.4.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap. It supplies the
simultaneous-conjugation equation needed to prove normality of the binary-product image.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti.GrpObj.Action

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G N H X : C} [GrpObj G] [GrpObj N] [GrpObj H]

/-- Simultaneous ambient conjugation on the two factors, as a morphism to their product. -/
private noncomputable def normalSemidirectConjugationHom
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j] :
    G ⊗ (N ⊗ H) ⟶ N ⊗ H :=
  lift
    (lift (fst G (N ⊗ H)) (snd G (N ⊗ H) ≫ fst N H) ≫ TauCeti.normalConjugation i)
    (lift (fst G (N ⊗ H)) (snd G (N ⊗ H) ≫ snd N H) ≫ TauCeti.normalConjugation j)

@[simp, reassoc]
private theorem normalSemidirectConjugationHom_fst
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j] :
    normalSemidirectConjugationHom i j ≫ fst N H =
      lift (fst G (N ⊗ H)) (snd G (N ⊗ H) ≫ fst N H) ≫
        TauCeti.normalConjugation i := by
  simp [normalSemidirectConjugationHom]

@[simp, reassoc]
private theorem normalSemidirectConjugationHom_snd
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j] :
    normalSemidirectConjugationHom i j ≫ snd N H =
      lift (fst G (N ⊗ H)) (snd G (N ⊗ H) ≫ snd N H) ≫
        TauCeti.normalConjugation j := by
  simp [normalSemidirectConjugationHom]

/-- The first component of simultaneous conjugation on generalized points. -/
private theorem lift_normalSemidirectConjugationHom_fst
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j]
    (g : X ⟶ G) (x : X ⟶ N ⊗ H) :
    (lift g x ≫ normalSemidirectConjugationHom i j) ≫ fst N H =
      lift g (x ≫ fst N H) ≫ TauCeti.normalConjugation i := by
  rw [Category.assoc, normalSemidirectConjugationHom_fst, ← Category.assoc, comp_lift]
  simp only [lift_fst, lift_snd_assoc]

/-- The second component of simultaneous conjugation on generalized points. -/
private theorem lift_normalSemidirectConjugationHom_snd
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j]
    (g : X ⟶ G) (x : X ⟶ N ⊗ H) :
    (lift g x ≫ normalSemidirectConjugationHom i j) ≫ snd N H =
      lift g (x ≫ snd N H) ≫ TauCeti.normalConjugation j := by
  rw [Category.assoc, normalSemidirectConjugationHom_snd, ← Category.assoc, comp_lift]
  simp only [lift_fst, lift_snd_assoc]

/-- The first component of multiplication in the internal semidirect product. -/
private theorem semidirect_mul_fst (A : Action H N) (x y : X ⟶ N ⊗ H) :
    letI := A.semidirectProductGrpObj
    (x * y) ≫ fst N H =
      (x ≫ fst N H) * A.act (x ≫ snd N H) (y ≫ fst N H) := by
  let _ := A.semidirectProductGrpObj
  have h := congrArg SemidirectProduct.left (map_mul (A.pointMulEquiv X) x y)
  simpa only [pointMulEquiv_left, pointMulEquiv_right, SemidirectProduct.mul_left,
    toMulAutHom_apply] using h

/-- The second component of multiplication in the internal semidirect product. -/
private theorem semidirect_mul_snd (A : Action H N) (x y : X ⟶ N ⊗ H) :
    letI := A.semidirectProductGrpObj
    (x * y) ≫ snd N H = (x ≫ snd N H) * (y ≫ snd N H) := by
  let _ := A.semidirectProductGrpObj
  have h := congrArg SemidirectProduct.right (map_mul (A.pointMulEquiv X) x y)
  simpa only [pointMulEquiv_right, SemidirectProduct.mul_right] using h

/-- Simultaneous ambient conjugation is compatible with the conjugation action defining the
normal semidirect product. -/
private theorem normalConjugation_act_compatible
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j]
    (g : X ⟶ G) (h : X ⟶ H) (n : X ⟶ N) :
    lift g ((normalConjugation i j).act h n) ≫ TauCeti.normalConjugation i =
      (normalConjugation i j).act
        (lift g h ≫ TauCeti.normalConjugation j)
        (lift g n ≫ TauCeti.normalConjugation i) := by
  apply (cancel_mono i).1
  simp only [Category.assoc, TauCeti.lift_normalConjugation_comp,
    normalConjugation_act]
  group

/-- Simultaneous ambient conjugation on two normal subgroup objects acts on their normal
semidirect product by group automorphisms. -/
noncomputable def normalSemidirectConjugation
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j] :
    let A := normalConjugation i j
    letI := A.semidirectProductGrpObj
    Action G (N ⊗ H) := by
  let A := normalConjugation i j
  letI := A.semidirectProductGrpObj
  refine
    { hom := normalSemidirectConjugationHom i j
      one_act := fun Y x ↦ ?_
      mul_act := fun Y g₁ g₂ x ↦ ?_
      act_mul := fun Y g x y ↦ ?_ }
  · ext
    · rw [lift_normalSemidirectConjugationHom_fst,
        TauCeti.normalConjugation_one_left]
    · rw [lift_normalSemidirectConjugationHom_snd,
        TauCeti.normalConjugation_one_left]
  · ext
    · rw [lift_normalSemidirectConjugationHom_fst,
        lift_normalSemidirectConjugationHom_fst,
        lift_normalSemidirectConjugationHom_fst,
        TauCeti.normalConjugation_mul_left]
    · rw [lift_normalSemidirectConjugationHom_snd,
        lift_normalSemidirectConjugationHom_snd,
        lift_normalSemidirectConjugationHom_snd,
        TauCeti.normalConjugation_mul_left]
  · ext
    · rw [lift_normalSemidirectConjugationHom_fst, semidirect_mul_fst,
        TauCeti.normalConjugation_mul_right, normalConjugation_act_compatible,
        semidirect_mul_fst, lift_normalSemidirectConjugationHom_fst,
        lift_normalSemidirectConjugationHom_snd,
        lift_normalSemidirectConjugationHom_fst]
    · rw [lift_normalSemidirectConjugationHom_snd, semidirect_mul_snd,
        TauCeti.normalConjugation_mul_right, semidirect_mul_snd,
        lift_normalSemidirectConjugationHom_snd,
        lift_normalSemidirectConjugationHom_snd]

/-- Simultaneous conjugation sends `(n, h)` to the pair of their ambient conjugates. -/
@[simp]
theorem normalSemidirectConjugation_act
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j]
    (g : X ⟶ G) (x : X ⟶ N ⊗ H) :
    let A := normalConjugation i j
    letI := A.semidirectProductGrpObj
    (normalSemidirectConjugation i j).act g x =
      lift
        (lift g (x ≫ fst N H) ≫ TauCeti.normalConjugation i)
        (lift g (x ≫ snd N H) ≫ TauCeti.normalConjugation j) := by
  dsimp only
  let A := normalConjugation i j
  let _ := A.semidirectProductGrpObj
  rw [Action.act_def]
  rw [normalSemidirectConjugation]
  ext
  · rw [lift_normalSemidirectConjugationHom_fst, lift_fst]
  · rw [lift_normalSemidirectConjugationHom_snd, lift_snd]

/-- Multiplication from a normal semidirect product intertwines simultaneous ambient
conjugation on the source with conjugation on the target. -/
theorem normalSemidirectMul_equivariant_apply
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j]
    (g : X ⟶ G) (x : X ⟶ N ⊗ H) :
    let A := normalConjugation i j
    letI := A.semidirectProductGrpObj
    (normalSemidirectConjugation i j).act g x ≫
        (normalSemidirectMul i j).hom.hom =
      g * (x ≫ (normalSemidirectMul i j).hom.hom) * g⁻¹ := by
  dsimp only
  let A := normalConjugation i j
  let _ := A.semidirectProductGrpObj
  rw [normalSemidirectConjugation_act, comp_normalSemidirectMul,
    comp_normalSemidirectMul]
  rw [← Category.assoc, lift_fst, ← Category.assoc, lift_snd]
  simp only [Category.assoc, TauCeti.lift_normalConjugation_comp]
  group

/-- **Multiplication from a normal semidirect product is equivariant for conjugation.** -/
@[reassoc]
theorem normalSemidirectMul_equivariant
    (i : N ⟶ G) [IsMonHom.Normal i] (j : H ⟶ G) [IsMonHom.Normal j] :
    let A := normalConjugation i j
    letI := A.semidirectProductGrpObj
    (normalSemidirectConjugation i j).hom ≫ (normalSemidirectMul i j).hom.hom =
      G ◁ (normalSemidirectMul i j).hom.hom ≫ GrpObj.conj G := by
  dsimp only
  let A := normalConjugation i j
  let _ := A.semidirectProductGrpObj
  have h := normalSemidirectMul_equivariant_apply i j
    (g := fst G (N ⊗ H)) (x := snd G (N ⊗ H))
  rw [Action.act_def, lift_fst_snd, Category.id_comp] at h
  have hwhisker : lift (fst G (N ⊗ H))
      (snd G (N ⊗ H) ≫ (normalSemidirectMul i j).hom.hom) =
        G ◁ (normalSemidirectMul i j).hom.hom := by
    ext <;> simp
  calc
    (normalSemidirectConjugation i j).hom ≫ (normalSemidirectMul i j).hom.hom =
        fst G (N ⊗ H) * (snd G (N ⊗ H) ≫ (normalSemidirectMul i j).hom.hom) *
          (fst G (N ⊗ H))⁻¹ := h
    _ = lift (fst G (N ⊗ H))
          (snd G (N ⊗ H) ≫ (normalSemidirectMul i j).hom.hom) ≫ GrpObj.conj G :=
      (GrpObj.lift_conj_eq_mul_mul_inv _ _).symm
    _ = G ◁ (normalSemidirectMul i j).hom.hom ≫ GrpObj.conj G := by rw [hwhisker]

end TauCeti.GrpObj.Action
