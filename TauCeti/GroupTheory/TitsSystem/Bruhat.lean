/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.GroupTheory.TitsSystem.Basic

/-!
# Bruhat decomposition of a Tits system

For a Tits system `(B, N)`, every element of the ambient group belongs to a double coset
`B n B` represented by an element `n ∈ N`. Thus the canonical map from `N` to `B \ G / B`
is surjective, and the union of the Bruhat cells is the whole group.

The proof uses the multiplication axiom first for a simple reflection. Since the simple
reflections generate `W = N / (B ∩ N)` and are involutions, induction in `W` shows that left
multiplication by any Bruhat cell preserves the union of the cells. That union is consequently a
subgroup containing both `B` and `N`, hence is all of `G` by the generation axiom.

## Main declarations

* `TauCeti.TitsSystem.bruhatCells`: the union of the double cosets `B n B`, for `n ∈ N`.
* `TauCeti.TitsSystem.bruhatCells_eq_univ`: the Bruhat cells cover the ambient group.
* `TauCeti.TitsSystem.exists_mem_doubleCoset`: every group element lies in a cell represented
  by `N`.
* `TauCeti.TitsSystem.doubleCosetMk_surjective`: the induced map `N → B \ G / B` is
  surjective.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 28.1.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.

This supplies the abstract Bruhat decomposition in Layer 7, "Bruhat decomposition and BN-pairs /
Tits systems", of the ReductiveGroups roadmap.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- The union of the Bruhat cells `B n B` represented by elements `n` of `N`. -/
def bruhatCells : Set G :=
  ⋃ n : T.subgroupN,
    DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB

/-- An element lies in the union of Bruhat cells exactly when it lies in a cell represented by
an element of `N`. -/
theorem mem_bruhatCells_iff (g : G) :
    g ∈ T.bruhatCells ↔
      ∃ n : T.subgroupN,
        g ∈ DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB := by
  simp only [bruhatCells, Set.mem_iUnion]

/-- Representatives of the same element of `N / (B ∩ N)` determine the same Bruhat cell. -/
private theorem doubleCoset_eq_of_mk_eq {n m : T.subgroupN}
    (h : (QuotientGroup.mk n : T.WeylGroup) = QuotientGroup.mk m) :
    DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB =
      DoubleCoset.doubleCoset (m : G) T.subgroupB T.subgroupB := by
  obtain ⟨z, hz, hnz⟩ := (QuotientGroup.mk'_eq_mk' T.intersection).mp h
  apply DoubleCoset.doubleCoset_eq_of_mem
  apply DoubleCoset.mem_doubleCoset.mpr
  refine ⟨1, T.subgroupB.one_mem, (z⁻¹ : G),
    T.subgroupB.inv_mem ((T.mem_intersection z).mp hz), ?_⟩
  simpa only [one_mul, Subgroup.coe_mul, Subgroup.coe_inv] using
    congrArg Subtype.val (eq_mul_inv_of_mul_eq hnz)

/-- The identity Bruhat cell acts on the union of Bruhat cells by left multiplication. -/
private theorem oneCell_mul_bruhatCells_subset :
    DoubleCoset.doubleCoset (1 : G) T.subgroupB T.subgroupB * T.bruhatCells ⊆
      T.bruhatCells := by
  rw [doubleCoset_one_self]
  rintro g ⟨b, hb, x, hx, rfl⟩
  rw [T.mem_bruhatCells_iff] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hn
  exact DoubleCoset.mem_doubleCoset.mpr
    ⟨b * b₁, T.subgroupB.mul_mem hb hb₁, b₂, hb₂, by simp [mul_assoc]⟩

/-- The property of a Weyl-group element needed to multiply arbitrary Bruhat cells. -/
private def MultipliesBruhatCells (q : T.WeylGroup) : Prop :=
  ∀ n : T.subgroupN, QuotientGroup.mk n = q →
    ∀ w : T.subgroupN,
      DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB *
          DoubleCoset.doubleCoset (w : G) T.subgroupB T.subgroupB ⊆
        T.bruhatCells

/-- The identity of the Weyl group preserves the union of Bruhat cells. -/
private theorem multipliesBruhatCells_one : T.MultipliesBruhatCells 1 := by
  intro n hn w
  rw [T.doubleCoset_eq_of_mk_eq hn]
  exact (Set.mul_subset_mul_left <| Set.subset_iUnion (fun v : T.subgroupN ↦
      DoubleCoset.doubleCoset (v : G) T.subgroupB T.subgroupB) w).trans
    T.oneCell_mul_bruhatCells_subset

/-- A simple reflection preserves the union of Bruhat cells. -/
private theorem multipliesBruhatCells_simple
    (q : T.WeylGroup) (hq : q ∈ T.simple) : T.MultipliesBruhatCells q := by
  obtain ⟨r, hrq, hr⟩ := T.mul_doubleCoset_subset q hq
  intro n hn w
  rw [T.doubleCoset_eq_of_mk_eq (hn.trans hrq.symm)]
  refine (hr w).trans ?_
  rw [Set.union_subset_iff]
  exact ⟨Set.subset_iUnion (fun v : T.subgroupN ↦
      DoubleCoset.doubleCoset (v : G) T.subgroupB T.subgroupB) (r * w),
    Set.subset_iUnion (fun v : T.subgroupN ↦
      DoubleCoset.doubleCoset (v : G) T.subgroupB T.subgroupB) w⟩

/-- The multiplication property is closed under products in the Weyl group. -/
private theorem MultipliesBruhatCells.mul {q₁ q₂ : T.WeylGroup}
    (hq₁ : T.MultipliesBruhatCells q₁) (hq₂ : T.MultipliesBruhatCells q₂) :
    T.MultipliesBruhatCells (q₁ * q₂) := by
  intro n hn w
  obtain ⟨n₁, hn₁⟩ := QuotientGroup.mk'_surjective T.intersection q₁
  obtain ⟨n₂, hn₂⟩ := QuotientGroup.mk'_surjective T.intersection q₂
  have hn₁n₂ : QuotientGroup.mk (n₁ * n₂) = q₁ * q₂ := by
    rw [← QuotientGroup.mk'_apply T.intersection, map_mul, hn₁, hn₂]
  rw [T.doubleCoset_eq_of_mk_eq (hn.trans hn₁n₂.symm)]
  rintro g ⟨x, hx, y, hy, rfl⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  let x₁ : G := b₁ * (n₁ : G)
  let x₂ : G := (n₂ : G) * b₂
  have hx₁ : x₁ ∈ DoubleCoset.doubleCoset (n₁ : G) T.subgroupB T.subgroupB :=
    DoubleCoset.mem_doubleCoset.mpr
      ⟨b₁, hb₁, 1, T.subgroupB.one_mem, by simp [x₁]⟩
  have hx₂ : x₂ ∈ DoubleCoset.doubleCoset (n₂ : G) T.subgroupB T.subgroupB :=
    DoubleCoset.mem_doubleCoset.mpr
      ⟨1, T.subgroupB.one_mem, b₂, hb₂, by simp [x₂]⟩
  have hx₂y : x₂ * y ∈ T.bruhatCells :=
    hq₂ n₂ hn₂ w ⟨x₂, hx₂, y, hy, rfl⟩
  obtain ⟨v, hv⟩ := (T.mem_bruhatCells_iff (x₂ * y)).mp hx₂y
  have hx₁xy : x₁ * (x₂ * y) ∈ T.bruhatCells :=
    hq₁ n₁ hn₁ v ⟨x₁, hx₁, x₂ * y, hv, rfl⟩
  simpa only [x₁, x₂, Subgroup.coe_mul, mul_assoc] using hx₁xy

/-- Every Weyl-group element preserves the union of Bruhat cells. -/
private theorem multipliesBruhatCells (q : T.WeylGroup) : T.MultipliesBruhatCells q := by
  have hq : q ∈ Subgroup.closure T.simple := by
    rw [T.closure_simple]
    exact Subgroup.mem_top q
  induction hq using Subgroup.closure_induction'' with
  | mem s hs => exact T.multipliesBruhatCells_simple s hs
  | inv_mem s hs =>
      have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (T.simple_sq_eq_one hs)
      rw [hinv]
      exact T.multipliesBruhatCells_simple s hs
  | one => exact T.multipliesBruhatCells_one
  | mul q₁ q₂ _ _ hq₁ hq₂ =>
      exact MultipliesBruhatCells.mul (T := T) hq₁ hq₂

/-- The union of Bruhat cells is closed under multiplication. -/
private theorem bruhatCells_mul_mem {x y : G}
    (hx : x ∈ T.bruhatCells) (hy : y ∈ T.bruhatCells) : x * y ∈ T.bruhatCells := by
  obtain ⟨n, hn⟩ := (T.mem_bruhatCells_iff x).mp hx
  obtain ⟨w, hw⟩ := (T.mem_bruhatCells_iff y).mp hy
  exact T.multipliesBruhatCells (QuotientGroup.mk n) n rfl w ⟨x, hn, y, hw, rfl⟩

/-- The union of Bruhat cells is closed under inversion. -/
private theorem bruhatCells_inv_mem {x : G} (hx : x ∈ T.bruhatCells) :
    x⁻¹ ∈ T.bruhatCells := by
  obtain ⟨n, hn⟩ := (T.mem_bruhatCells_iff x).mp hx
  refine (T.mem_bruhatCells_iff x⁻¹).mpr ⟨n⁻¹, ?_⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hn
  exact DoubleCoset.mem_doubleCoset.mpr
    ⟨b₂⁻¹, T.subgroupB.inv_mem hb₂, b₁⁻¹, T.subgroupB.inv_mem hb₁, by
      simp [mul_assoc]⟩

/-- The Bruhat cells cover the ambient group. -/
@[simp] theorem bruhatCells_eq_univ : T.bruhatCells = Set.univ := by
  let C : Subgroup G :=
    { carrier := T.bruhatCells
      one_mem' := (T.mem_bruhatCells_iff 1).mpr
        ⟨1, DoubleCoset.mem_doubleCoset_self T.subgroupB T.subgroupB 1⟩
      mul_mem' := fun hx hy ↦ T.bruhatCells_mul_mem hx hy
      inv_mem' := fun hx ↦ T.bruhatCells_inv_mem hx }
  have hcarrier : (C : Set G) = T.bruhatCells := rfl
  have hBN : (T.subgroupB : Set G) ∪ T.subgroupN ⊆ C := by
    rintro g (hg | hg)
    · exact (T.mem_bruhatCells_iff g).mpr
        ⟨1, DoubleCoset.mem_doubleCoset.mpr
          ⟨g, hg, 1, T.subgroupB.one_mem, by simp⟩⟩
    · exact (T.mem_bruhatCells_iff g).mpr
        ⟨⟨g, hg⟩, DoubleCoset.mem_doubleCoset_self T.subgroupB T.subgroupB g⟩
  have htop : C = ⊤ := by
    rw [← top_le_iff, ← T.closure_subgroupB_union_subgroupN]
    exact (Subgroup.closure_le C).mpr hBN
  exact hcarrier.symm.trans <|
    (congrArg (fun H : Subgroup G ↦ (H : Set G)) htop).trans Subgroup.coe_top

/-- Every element of the ambient group belongs to a Bruhat cell represented by an element of
`N`. -/
theorem exists_mem_doubleCoset (g : G) :
    ∃ n : T.subgroupN,
      g ∈ DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB := by
  rw [← T.mem_bruhatCells_iff, T.bruhatCells_eq_univ]
  exact Set.mem_univ g

/-- The canonical map from `N` to the double-coset quotient `B \ G / B` is surjective. -/
theorem doubleCosetMk_surjective :
    Function.Surjective
      (fun n : T.subgroupN ↦
        DoubleCoset.mk T.subgroupB T.subgroupB (n : G)) := by
  rintro ⟨g⟩
  obtain ⟨n, hn⟩ := T.exists_mem_doubleCoset g
  refine ⟨n, ?_⟩
  exact Quotient.sound (DoubleCoset.doubleCoset_eq_of_mem hn).symm

end TauCeti.TitsSystem
