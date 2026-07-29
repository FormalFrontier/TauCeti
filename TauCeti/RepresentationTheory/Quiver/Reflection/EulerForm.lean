/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Basic
public import TauCeti.RepresentationTheory.Quiver.Reflection.DimensionVector

/-!
# The Euler and Tits forms under reflection of a quiver at a vertex

Reflecting a quiver at a vertex does not change its underlying graph, so it changes neither the
Tits form (`TauCeti.titsForm_reflect`) nor its polarization (`TauCeti.titsPolarForm_reflect`), and
hence not the simple reflections on dimension vectors either
(`TauCeti.vertexPreReflection_reflect_apply`). The Euler form *does* change, since it records the
orientation; what survives is the Bernstein-Gelfand-Ponomarev identity at a **sink** `i`: the
Euler form of the reflected quiver, evaluated at the simple reflections `sᵢ d` and `sᵢ e`, is the
Euler form of the original quiver evaluated at `d` and `e`
(`TauCeti.eulerForm_reflect_vertexPreReflection`).

## Main results

* `TauCeti.titsForm_reflect`, `TauCeti.titsPolarForm_reflect`: the Tits form and its polarization
  are unchanged by reflection at a vertex.
* `TauCeti.vertexPreReflection_reflect_apply`: so is every simple reflection on dimension vectors.
* `TauCeti.eulerForm_reflect_vertexPreReflection`: at a sink, the Euler form is transported by the
  simple reflection at that vertex.

## References

This is the dimension-vector shadow of the Layer 4 reflection-functor target
`dim (C⁺ᵢ M) = sᵢ · dim M` of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Derksen--Weyman,
*An Introduction to Quiver Representations*, and Bernstein--Gelfand--Ponomarev, *Coxeter functors
and Gabriel's theorem*.
-/

public section

namespace TauCeti

open _root_.Quiver

open scoped BigOperators

universe u v

/-! ### Two sum manipulations -/

/-- A double sum over a finite type is determined by the symmetrization of its summand. -/
private theorem sum_sum_eq_of_add_swap_eq {W : Type*} [Fintype W] {F G : W → W → ℤ}
    (h : ∀ a b : W, F a b + F b a = G a b + G b a) :
    ∑ a : W, ∑ b : W, F a b = ∑ a : W, ∑ b : W, G a b := by
  have hF : ∑ a : W, ∑ b : W, F b a = ∑ a : W, ∑ b : W, F a b := Finset.sum_comm
  have hG : ∑ a : W, ∑ b : W, G b a = ∑ a : W, ∑ b : W, G a b := Finset.sum_comm
  have hsum : ∑ a : W, ∑ b : W, (F a b + F b a) = ∑ a : W, ∑ b : W, (G a b + G b a) :=
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ h a b
  simp only [Finset.sum_add_distrib] at hsum
  rw [hF, hG] at hsum
  linarith

/-- The arithmetic heart of the reflection identity for the Euler form. Here `N` plays the role of
the arrow-count matrix of the quiver, whose `i`-th row vanishes because `i` is a sink, and `N'`
that of the quiver reflected at `i`; `d'` and `e'` are the reflections of `d` and `e`. -/
private theorem sub_sum_sum_eq_of_reflect_data {W : Type*} [Fintype W] (i : W)
    (N N' : W → W → ℤ) (d e d' e' : W → ℤ)
    (hN : ∀ b : W, N i b = 0) (hN'row : ∀ b : W, N' i b = N b i)
    (hN'col : ∀ a : W, N' a i = 0)
    (hN' : ∀ a b : W, a ≠ i → b ≠ i → N' a b = N a b)
    (hd : ∀ w : W, w ≠ i → d' w = d w) (he : ∀ w : W, w ≠ i → e' w = e w)
    (hdi : d' i = (∑ w : W, N w i * d w) - d i)
    (hei : e' i = (∑ w : W, N w i * e w) - e i) :
    (∑ w : W, d' w * e' w) - ∑ a : W, ∑ b : W, N' a b * (d' a * e' b)
      = (∑ w : W, d w * e w) - ∑ a : W, ∑ b : W, N a b * (d a * e b) := by
  classical
  have hsplit : ∀ f : W → ℤ, ∑ w : W, f w = f i + ∑ w ∈ Finset.univ.erase i, f w := fun f ↦
    (Finset.add_sum_erase _ f (Finset.mem_univ i)).symm
  have hCd : ∑ w ∈ Finset.univ.erase i, N w i * d w = ∑ w : W, N w i * d w :=
    Finset.sum_erase _ (by simp [hN i])
  have hCe : ∑ w ∈ Finset.univ.erase i, N w i * e w = ∑ w : W, N w i * e w :=
    Finset.sum_erase _ (by simp [hN i])
  have h₁ : ∑ w : W, d' w * e' w
      = d' i * e' i + ∑ w ∈ Finset.univ.erase i, d w * e w := by
    rw [hsplit fun w ↦ d' w * e' w]
    congr 1
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [hd w (Finset.ne_of_mem_erase hw), he w (Finset.ne_of_mem_erase hw)]
  have h₂ : ∑ w : W, d w * e w
      = d i * e i + ∑ w ∈ Finset.univ.erase i, d w * e w := hsplit fun w ↦ d w * e w
  have h₃ : ∑ a : W, ∑ b : W, N' a b * (d' a * e' b)
      = d' i * (∑ w : W, N w i * e w)
        + ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, N a b * (d a * e b) := by
    rw [hsplit fun a ↦ ∑ b : W, N' a b * (d' a * e' b)]
    congr 1
    · rw [hsplit fun b ↦ N' i b * (d' i * e' b), hN'row i, hN i, zero_mul, zero_add,
        ← hCe, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [hN'row b, he b (Finset.ne_of_mem_erase hb)]
      ring
    · refine Finset.sum_congr rfl fun a ha ↦ ?_
      rw [hsplit fun b ↦ N' a b * (d' a * e' b), hN'col a, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [hN' a b (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hb),
        hd a (Finset.ne_of_mem_erase ha), he b (Finset.ne_of_mem_erase hb)]
  have h₄ : ∑ a : W, ∑ b : W, N a b * (d a * e b)
      = (∑ w : W, N w i * d w) * e i
        + ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, N a b * (d a * e b) := by
    have hzero : ∑ b : W, N i b * (d i * e b) = 0 :=
      Finset.sum_eq_zero fun b _ ↦ by rw [hN b, zero_mul]
    rw [hsplit fun a ↦ ∑ b : W, N a b * (d a * e b), hzero, zero_add, ← hCd, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hsplit fun b ↦ N a b * (d a * e b)]
    ring
  rw [h₁, h₂, h₃, h₄, hdi, hei]
  ring

variable {V : Type u} [_root_.Quiver.{v} V] [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
  [DecidableEq V]

/-- `TauCeti.eulerForm_eq_sum_card` for the reflected quiver, with the sums re-indexed by the
vertex type `V` itself and the arrow counts written as `TauCeti.Quiver.reflectHom` counts.

`Quiver.Reflect V i` is a type synonym for `V`, so this is the generic expansion up to
unfolding that synonym and its `Fintype` instances; the point of stating it is that `linarith`
and `ring` compare atoms only up to reducible transparency, and so cannot see a
`Quiver.Reflect V i`-indexed sum and a `V`-indexed one as the same term. Where a tactic does
unfold the synonym (`refine`, in `TauCeti.eulerForm_reflect_vertexPreReflection` below), the
generic lemma is used directly instead. -/
private theorem eulerForm_reflect_eq_sum_card (i : V) (d e : V → ℤ) :
    eulerForm (Quiver.Reflect V i) d e =
      (∑ w : V, d w * e w)
        - ∑ a : V, ∑ b : V, (Fintype.card (Quiver.reflectHom i a b) : ℤ) * (d a * e b) :=
  eulerForm_eq_sum_card (Quiver.Reflect V i) d e

/-! ### The Tits form is unchanged -/

/-- Reflecting at a vertex leaves unchanged every arrow-weighted double sum whose weight is
symmetric in the two vertices, because reflection preserves the underlying graph. -/
private theorem sum_sum_card_reflectHom (i : V) (S : V → V → ℤ) (hS : ∀ a b : V, S a b = S b a) :
    ∑ a : V, ∑ b : V, (Fintype.card (Quiver.reflectHom i a b) : ℤ) * S a b
      = ∑ a : V, ∑ b : V, (Fintype.card (a ⟶ b) : ℤ) * S a b := by
  refine sum_sum_eq_of_add_swap_eq fun a b ↦ ?_
  have hc : (Fintype.card (Quiver.reflectHom i a b) : ℤ)
      + (Fintype.card (Quiver.reflectHom i b a) : ℤ)
      = (Fintype.card (a ⟶ b) : ℤ) + (Fintype.card (b ⟶ a) : ℤ) := by
    exact_mod_cast Quiver.card_reflectHom_add_swap i a b
  rw [hS b a]
  linear_combination S a b * hc

/-- Reflecting at a vertex leaves the Tits form unchanged: the Tits form depends only on the
underlying graph of the quiver, not on its orientation. -/
theorem titsForm_reflect (i : V) (d : V → ℤ) :
    titsForm (Quiver.Reflect V i) d = titsForm V d := by
  have key := sum_sum_card_reflectHom i (fun a b ↦ d a * d b) fun a b ↦ mul_comm (d a) (d b)
  rw [titsForm_def, titsForm_def, eulerForm_reflect_eq_sum_card, eulerForm_eq_sum_card]
  linarith [key]

/-- Reflecting at a vertex leaves the polarized Tits form unchanged. -/
theorem titsPolarForm_reflect (i : V) (d e : V → ℤ) :
    titsPolarForm (Quiver.Reflect V i) d e = titsPolarForm V d e := by
  have key := sum_sum_card_reflectHom i (fun a b ↦ d a * e b + e a * d b) fun a b ↦ by ring
  have hsplit : ∀ N : V → V → ℤ,
      ∑ a : V, ∑ b : V, N a b * (d a * e b + e a * d b)
        = (∑ a : V, ∑ b : V, N a b * (d a * e b)) + ∑ a : V, ∑ b : V, N a b * (e a * d b) :=
    fun N ↦ by simp only [mul_add, Finset.sum_add_distrib]
  rw [hsplit, hsplit] at key
  rw [titsPolarForm_def, titsPolarForm_def, eulerForm_reflect_eq_sum_card,
    eulerForm_reflect_eq_sum_card, eulerForm_eq_sum_card, eulerForm_eq_sum_card]
  linarith [key]

/-- Reflecting at a vertex leaves every simple reflection on dimension vectors unchanged, since
these are built from the polarized Tits form, which reflection preserves. -/
theorem vertexPreReflection_reflect_apply (i j : V) (d : V → ℤ) (w : V) :
    vertexPreReflection (Quiver.Reflect V i) j d w = vertexPreReflection V j d w := by
  by_cases hw : w = j
  · rw [hw, vertexPreReflection_apply_self, vertexPreReflection_apply_self]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    congr 1
    exact_mod_cast Quiver.card_reflectHom_add_swap i j x
  · rw [vertexPreReflection_apply_of_ne (Quiver.Reflect V i) j d hw,
      vertexPreReflection_apply_of_ne V j d hw]

/-! ### The Euler form at a sink -/

/-- At a sink `i`, the Euler form of the quiver reflected at `i` is carried to the Euler form of
the original quiver by the simple reflection `sᵢ` on dimension vectors:
`⟨sᵢ d, sᵢ e⟩` for `Q.reflect i` equals `⟨d, e⟩` for `Q`.

This is the numerical identity behind the Bernstein-Gelfand-Ponomarev reflection functor at a
sink, which realizes `sᵢ` on dimension vectors. -/
theorem eulerForm_reflect_vertexPreReflection {i : V} (h : Quiver.IsSink i) (d e : V → ℤ) :
    eulerForm (Quiver.Reflect V i) (vertexPreReflection V i d) (vertexPreReflection V i e)
      = eulerForm V d e := by
  have hcard : ∀ b : V, (Fintype.card (i ⟶ b) : ℤ) = 0 := fun b ↦ by
    rw [Fintype.card_eq_zero_iff.mpr (h b), Nat.cast_zero]
  have hself : ∀ f : V → ℤ, vertexPreReflection V i f i
      = (∑ w : V, (Fintype.card (w ⟶ i) : ℤ) * f w) - f i := fun f ↦ by
    rw [vertexPreReflection_apply_self, sub_eq_neg_add]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [hcard x, zero_add]
  rw [eulerForm_eq_sum_card (Quiver.Reflect V i), eulerForm_eq_sum_card V]
  refine sub_sum_sum_eq_of_reflect_data i (fun a b ↦ (Fintype.card (a ⟶ b) : ℤ))
    (fun a b ↦ (Fintype.card (Quiver.reflectHom i a b) : ℤ)) d e _ _
    hcard (fun b ↦ by rw [Quiver.card_reflectHom_left])
    (fun a ↦ by rw [Quiver.card_reflectHom_right_of_isSink h, Nat.cast_zero])
    (fun a b ha hb ↦ by rw [Quiver.card_reflectHom_of_ne_of_ne ha hb])
    (fun x hx ↦ vertexPreReflection_apply_of_ne V i d hx)
    (fun x hx ↦ vertexPreReflection_apply_of_ne V i e hx) (hself d) (hself e)

end TauCeti
