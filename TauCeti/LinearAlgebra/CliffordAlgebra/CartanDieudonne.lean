/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift

/-!
# The one-step Cartan--Dieudonne reduction

Let `g` be an orthogonal automorphism and let `v` have invertible norm. At least one of `g v - v`
and `g v + v` has invertible norm. A reflection in the former carries `g v` to `v`; a reflection
in the latter followed by the reflection in `v` does the same. Since these reflections lift to the
Pin group over a separably closed field of characteristic not two, an element in the range of
`pinToOrthogonal` can be multiplied into `g` to make it fix `v`.

This is the one-vector reduction used by the finite-dimensional Cartan--Dieudonne induction.

## Main result

* `TauCeti.CliffordAlgebra.exists_mem_range_pinToOrthogonal_mul_apply_eq_self`: an element in the
  range of the Pin action corrects an orthogonal automorphism to fix a chosen vector of invertible
  norm.
* `TauCeti.CliffordAlgebra.exists_mem_range_pinToOrthogonal_mul_eqOn_sup`: the correction preserves
  an arbitrary previously fixed subspace when the new vector is orthogonal to it.

## References

This advances Layer 2's "The double cover" target in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v

namespace CliffordAlgebra

variable {K : Type u} {V : Type v} [Field K] [IsSepClosed K]
  [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) [Invertible (2 : K)]

private theorem reflection_mem_range_pinToOrthogonal_of_isSepClosed
    (w : V) [Invertible (Q w)] :
    (⟨QuadraticMap.reflection Q w, QuadraticMap.reflection_mem_orthogonalGroup Q w⟩ :
      QuadraticMap.orthogonalGroup Q) ∈ (pinToOrthogonal Q).range :=
  reflection_mem_range_pinToOrthogonal_of_isSquare Q w
    (IsSepClosed.exists_eq_mul_self _)

/-- Given an orthogonal automorphism `g` and a vector `v` of invertible norm, an element in the
range of the Pin action can be multiplied into `g` so that the product fixes `v`. The correcting
orthogonal element is the image under `pinToOrthogonal` of a lift of either one reflection or two
reflections. -/
theorem exists_mem_range_pinToOrthogonal_mul_apply_eq_self
    (g : QuadraticMap.orthogonalGroup Q) (v : V)
    [Invertible (Q v)] :
    ∃ r : QuadraticMap.orthogonalGroup Q, r ∈ (pinToOrthogonal Q).range ∧
      (((r * g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) v = v) := by
  have hmap : Q ((g : V ≃ₗ[K] V) v) = Q v :=
    QuadraticMap.map_app_of_mem_orthogonalGroup g.2 v
  rcases QuadraticMap.isUnit_sub_or_add_of_map_eq Q _ v hmap
      (isUnit_of_invertible (Q v)).ne_zero with hsub | hadd
  · let : Invertible (Q ((g : V ≃ₗ[K] V) v - v)) := hsub.invertible
    let r : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) v - v),
        QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    refine ⟨r, reflection_mem_range_pinToOrthogonal_of_isSepClosed Q _, ?_⟩
    -- Expose the underlying automorphisms of the subgroup product before applying the reflection
    -- computation.
    change QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) v - v)
      ((g : V ≃ₗ[K] V) v) = v
    exact QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ v hmap
  · have : Invertible (Q ((g : V ≃ₗ[K] V) v - -v)) := by
      simpa only [sub_neg_eq_add] using hadd.invertible
    let r₁ : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    let r₂ : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) v - -v),
        QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    refine ⟨r₁ * r₂,
      (pinToOrthogonal Q).range.mul_mem
        (reflection_mem_range_pinToOrthogonal_of_isSepClosed Q v)
        (reflection_mem_range_pinToOrthogonal_of_isSepClosed Q _), ?_⟩
    -- Expose the two underlying reflections before applying their public computation equations.
    change QuadraticMap.reflection Q v
      (QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) v - -v)
        ((g : V ≃ₗ[K] V) v)) = v
    rw [QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ (-v)
      (hmap.trans (Q.map_neg v).symm), map_neg, QuadraticMap.reflection_apply_self, neg_neg]

omit [IsSepClosed K] in
private theorem associated_apply_of_mem_orthogonalGroup
    (g : QuadraticMap.orthogonalGroup Q) (x y : V) :
    QuadraticMap.associated Q ((g : V ≃ₗ[K] V) x) ((g : V ≃ₗ[K] V) y) =
      QuadraticMap.associated Q x y := by
  simp only [QuadraticMap.associated_apply, ← map_add,
    QuadraticMap.map_app_of_mem_orthogonalGroup g.2]

omit [IsSepClosed K] in
private theorem reflection_fixes_of_mem_orthogonal
    (W : Submodule K V) (u : V) [Invertible (Q u)]
    (hu : u ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W)
    {w : V} (hw : w ∈ W) :
    QuadraticMap.reflection Q u w = w := by
  apply QuadraticMap.reflection_apply_of_isOrtho
  apply QuadraticMap.associated_isOrtho.mp
  simpa only [QuadraticMap.associated_isSymm] using hu w hw

omit [IsSepClosed K] [Invertible (2 : K)] in
private theorem linearEquiv_eqOn_sup_span_singleton
    (f : V ≃ₗ[K] V) (W : Submodule K V) (x : V)
    (hW : ∀ w ∈ W, f w = w) (hx : f x = x) :
    ∀ y ∈ W ⊔ Submodule.span K {x}, f y = y := by
  apply LinearMap.eqOn_sup (f := f) (g := LinearEquiv.refl K V)
  · intro w hw
    simpa only [LinearEquiv.refl_apply] using hW w hw
  · apply LinearMap.eqOn_span'
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    -- Remove the identity-equivalence coercion introduced by `eqOn_span'`.
    change f x = x
    exact hx

/-- Given an orthogonal automorphism that fixes `W` and an anisotropic vector `x` orthogonal to
`W`, a Pin-range correction makes the product fix `W ⊔ K ∙ x` pointwise. -/
theorem exists_mem_range_pinToOrthogonal_mul_eqOn_sup
    (g : QuadraticMap.orthogonalGroup Q) (W : Submodule K V)
    (hfix : ∀ w ∈ W, ((g : V ≃ₗ[K] V) w) = w)
    (x : V) [Invertible (Q x)]
    (hx : x ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W) :
    ∃ r : QuadraticMap.orthogonalGroup Q, r ∈ (pinToOrthogonal Q).range ∧
      ∀ y ∈ W ⊔ Submodule.span K {x},
        (((r * g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) y) = y := by
  let B : LinearMap.BilinForm K V := QuadraticMap.associated Q
  have hmap : Q ((g : V ≃ₗ[K] V) x) = Q x :=
    QuadraticMap.map_app_of_mem_orthogonalGroup g.2 x
  have hgx : (g : V ≃ₗ[K] V) x ∈ B.orthogonal W := by
    intro w hw
    calc
      B w ((g : V ≃ₗ[K] V) x) =
          B ((g : V ≃ₗ[K] V) w) ((g : V ≃ₗ[K] V) x) := by
            rw [hfix w hw]
      _ = B w x := associated_apply_of_mem_orthogonalGroup Q g w x
      _ = 0 := hx w hw
  have hsub : (g : V ≃ₗ[K] V) x - x ∈ B.orthogonal W := by
    intro w hw
    have hwx : B w x = 0 := hx w hw
    simp only [map_sub, hgx w hw, hwx, sub_self]
  have hadd : (g : V ≃ₗ[K] V) x + x ∈ B.orthogonal W := by
    intro w hw
    have hwx : B w x = 0 := hx w hw
    simp only [map_add, hgx w hw, hwx, add_zero]
  rcases QuadraticMap.isUnit_sub_or_add_of_map_eq Q _ x hmap
      (isUnit_of_invertible (Q x)).ne_zero with hsubUnit | haddUnit
  · let : Invertible (Q ((g : V ≃ₗ[K] V) x - x)) := hsubUnit.invertible
    let r : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - x),
        QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    refine ⟨r, reflection_mem_range_pinToOrthogonal_of_isSepClosed Q _, ?_⟩
    apply linearEquiv_eqOn_sup_span_singleton _ W x
    · intro w hw
      -- Expose the reflection underlying the subgroup product before applying its pointwise API.
      change QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - x)
        ((g : V ≃ₗ[K] V) w) = w
      rw [hfix w hw]
      exact reflection_fixes_of_mem_orthogonal Q W _ hsub hw
    · -- Expose the reflection underlying the subgroup product at the new generator.
      change QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - x)
        ((g : V ≃ₗ[K] V) x) = x
      exact QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ x hmap
  · have : Invertible (Q ((g : V ≃ₗ[K] V) x - -x)) := by
      simpa only [sub_neg_eq_add] using haddUnit.invertible
    have hadd' : (g : V ≃ₗ[K] V) x - -x ∈ B.orthogonal W := by
      simpa only [sub_neg_eq_add] using hadd
    let r₁ : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q x, QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    let r₂ : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - -x),
        QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    refine ⟨r₁ * r₂,
      (pinToOrthogonal Q).range.mul_mem
        (reflection_mem_range_pinToOrthogonal_of_isSepClosed Q x)
        (reflection_mem_range_pinToOrthogonal_of_isSepClosed Q _), ?_⟩
    apply linearEquiv_eqOn_sup_span_singleton _ W x
    · intro w hw
      -- Expose the two reflections underlying the subgroup product.
      change QuadraticMap.reflection Q x
        (QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - -x)
          ((g : V ≃ₗ[K] V) w)) = w
      rw [hfix w hw, reflection_fixes_of_mem_orthogonal Q W _ hadd' hw,
        reflection_fixes_of_mem_orthogonal Q W _ hx hw]
    · -- Expose the two reflections underlying the subgroup product at the new generator.
      change QuadraticMap.reflection Q x
        (QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) x - -x)
          ((g : V ≃ₗ[K] V) x)) = x
      rw [QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ (-x)
        (hmap.trans (Q.map_neg x).symm), map_neg, QuadraticMap.reflection_apply_self, neg_neg]

end CliffordAlgebra
end TauCeti
