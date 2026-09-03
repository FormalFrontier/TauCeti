/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.EulerForm

/-!
# A positive definite Tits form forces acyclicity

A directed cycle is an obstruction to positive definiteness of the Tits form. Let `p` be a closed
path of positive length and let `d` be the indicator vector of the set `S` of vertices it visits.
Every vertex of `p` is the source of an arrow of `p`, and that arrow lands in `S` again, so the
arrow term of `TauCeti.eulerForm` at `d` already absorbs the whole diagonal term: `titsForm d ≤ 0`
while `d ≠ 0`. Hence a finite quiver whose Tits form is positive definite is acyclic
(`TauCeti.isAcyclic_of_titsForm_posDef`).

The counting is with distinct arrows, not with the arrows of `p` listed in order: a closed path may
traverse the same arrow twice, and the Euler form counts each arrow of the quiver once. The
injection that survives that is `v ↦ (an arrow of p out of v)`, whose injectivity is only that
distinct vertices are distinct sources; it appears below as the bound "each row of the arrow sum,
indexed by a vertex of `S`, is at least one".

The length-one case is the looplessness `TauCeti.isEmpty_hom_self_of_titsForm_posDef` that the
reflection identities need, proved there directly from the arrow count at a single vertex.

The generic path facts used in the counting argument are
`TauCeti.exists_hom_mem_path_vertices_of_mem_dropLast` and
`TauCeti.exists_hom_mem_path_vertices`, from
`TauCeti.RepresentationTheory.Quiver.FirstArrow`.

## Main result

* `TauCeti.isAcyclic_of_titsForm_posDef`: **a finite quiver whose Tits form is positive definite is
  acyclic.**

## References

The positive definiteness of the Tits form is the numerical side of the ADE condition in Gabriel's
theorem, Layer 5 of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`; this
file supplies the acyclicity that the reflection-functor induction there assumes separately. See
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
Ch. VII.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

section PosDef

variable {V : Type u} [_root_.Quiver.{v} V] [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]

/-- **A finite quiver whose Tits form is positive definite is acyclic.** The indicator vector of the
vertices visited by a closed path of positive length has Tits value at most zero: each of its
vertices contributes `1` to the diagonal sum and, being the source of an arrow of the path, at least
`1` to the arrow sum as well. -/
theorem isAcyclic_of_titsForm_posDef (hpd : (titsForm V).PosDef) : Quiver.IsAcyclic V := by
  classical
  rw [Quiver.isAcyclic_def]
  intro a p
  by_contra hp
  set S : Finset V := p.vertices.toFinset with hS
  set d : V → ℤ := fun v ↦ if v ∈ S then 1 else 0 with hd
  have hmem : ∀ v : V, v ∈ S ↔ v ∈ p.vertices := fun v ↦ by rw [hS, List.mem_toFinset]
  have hone : ∀ v ∈ S, d v = 1 := by
    intro v hv
    simp [hd, hv]
  have hd0 : d ≠ 0 := by
    intro h
    have := congrFun h a
    rw [hone a ((hmem a).mpr (Path.start_mem_vertices p))] at this
    exact one_ne_zero this
  have hdd : ∀ v : V, d v * d v = d v := by
    intro v
    simp only [hd]
    split <;> ring
  have hnn : ∀ v : V, 0 ≤ d v := by
    intro v
    simp only [hd]
    split <;> norm_num
  have hsq : ∑ v : V, d v * d v = (S.card : ℤ) := by
    rw [Finset.sum_congr rfl fun v _ ↦ hdd v]
    simp only [hd]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hterm : ∀ u v : V, 0 ≤ (Fintype.card (u ⟶ v) : ℤ) * (d u * d v) := fun u v ↦
    mul_nonneg (Int.natCast_nonneg _) (mul_nonneg (hnn u) (hnn v))
  have hrow : ∀ u ∈ S, (1 : ℤ) ≤ ∑ v : V, (Fintype.card (u ⟶ v) : ℤ) * (d u * d v) := by
    intro u hu
    obtain ⟨w, hw, ⟨e⟩⟩ :=
      TauCeti.exists_hom_mem_path_vertices p hp ((hmem u).mp hu)
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun v ↦ (Fintype.card (u ⟶ v) : ℤ) * (d u * d v))
      (fun v _ ↦ hterm u v) (Finset.mem_univ w))
    rw [hone u hu, hone w ((hmem w).mpr hw), mul_one, mul_one, Nat.one_le_cast]
    exact Fintype.card_pos_iff.mpr ⟨e⟩
  have hge : (S.card : ℤ) ≤ ∑ u : V, ∑ v : V, (Fintype.card (u ⟶ v) : ℤ) * (d u * d v) := by
    calc (S.card : ℤ) = ∑ _u ∈ S, (1 : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ u ∈ S, ∑ v : V, (Fintype.card (u ⟶ v) : ℤ) * (d u * d v) := Finset.sum_le_sum hrow
      _ ≤ ∑ u : V, ∑ v : V, (Fintype.card (u ⟶ v) : ℤ) * (d u * d v) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            fun u _ _ ↦ Finset.sum_nonneg fun v _ ↦ hterm u v
  have hpos := hpd d hd0
  rw [titsForm_def, eulerForm_eq_sum_card, hsq] at hpos
  linarith

end PosDef

end TauCeti
