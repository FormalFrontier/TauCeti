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

The file also establishes the rank-one multiplication law. If `s` is simple and `w` belongs to
the Weyl group, then `(B s B)(B w B)` is either `B (s w) B` or
`B (s w) B ∪ B w B`. This sharpens the subset appearing among the Tits-system axioms: the
adjacent cell always occurs, and the product can acquire only the original cell in addition.

The proof uses the multiplication axiom first for a simple reflection. Since the simple
reflections generate `W = N / (B ∩ N)` and are involutions, induction in `W` shows that left
multiplication by any Bruhat cell preserves the union of the cells. That union is consequently a
subgroup containing both `B` and `N`, hence is all of `G` by the generation axiom.

## Main declarations

* `TauCeti.TitsSystem.bruhatCells`: the union of the double cosets `B n B`, for `n ∈ N`.
* `TauCeti.TitsSystem.bruhatCell`: the Bruhat cell indexed by an element of the Weyl group.
* `TauCeti.TitsSystem.mem_bruhatCell_iff`: membership in a Weyl-indexed Bruhat cell in terms of
  a representative in `N`.
* `TauCeti.TitsSystem.bruhatCells_eq_univ`: the Bruhat cells cover the ambient group.
* `TauCeti.TitsSystem.bruhatCell_mul_eq_or_eq_union_of_mem_simple`: multiplication on the left by
  a simple Bruhat cell gives either the adjacent cell or its union with the original cell.
* `TauCeti.TitsSystem.bruhatCell_mul_self_eq_union_of_mem_simple`: the square of a simple cell is
  its union with the identity cell.
* `TauCeti.TitsSystem.exists_mem_doubleCoset`: every group element lies in a cell represented
  by `N`.
* `TauCeti.TitsSystem.doubleCosetMk_surjective`: the induced map `N → B \ G / B` is
  surjective.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 29.1--29.2.
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

/-- Representatives of the same class modulo `B ∩ N` determine the same `B`-double coset. -/
private theorem doubleCoset_eq_of_mk_eq (B N : Subgroup G) [(B.subgroupOf N).Normal]
    {n m : N}
    (h : (QuotientGroup.mk n : N ⧸ (B.subgroupOf N)) = QuotientGroup.mk m) :
    DoubleCoset.doubleCoset (n : G) B B = DoubleCoset.doubleCoset (m : G) B B := by
  obtain ⟨z, hz, hnz⟩ := (QuotientGroup.mk'_eq_mk' (B.subgroupOf N)).mp h
  apply DoubleCoset.doubleCoset_eq_of_mem
  apply DoubleCoset.mem_doubleCoset.mpr
  refine ⟨1, B.one_mem, (z⁻¹ : G), B.inv_mem hz, ?_⟩
  simpa only [one_mul, Subgroup.coe_mul, Subgroup.coe_inv] using
    congrArg Subtype.val (eq_mul_inv_of_mul_eq hnz)

/-- The Bruhat cell `B w B` indexed by an element `w` of the Weyl group. -/
noncomputable def bruhatCell (w : T.WeylGroup) : Set G :=
  w.liftOn' (fun n : T.subgroupN ↦
    DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB) fun _n _m h ↦
      doubleCoset_eq_of_mk_eq T.subgroupB T.subgroupN (Quotient.sound h)

/-- The Bruhat cell at the class of `n ∈ N` is the double coset `B n B`. -/
@[simp]
theorem bruhatCell_mk (n : T.subgroupN) :
    T.bruhatCell (QuotientGroup.mk n) =
      DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB :=
  Quotient.liftOn'_mk'' _ _ _

/-- Membership in a Weyl-indexed Bruhat cell is witnessed by some representative in `N`. -/
theorem mem_bruhatCell_iff {g : G} {w : T.WeylGroup} :
    g ∈ T.bruhatCell w ↔
      ∃ n : T.subgroupN, QuotientGroup.mk n = w ∧
        g ∈ DoubleCoset.doubleCoset (n : G) T.subgroupB T.subgroupB := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  constructor
  · intro hg
    exact ⟨n, rfl, by simpa only [bruhatCell_mk] using hg⟩
  · rintro ⟨m, hm, hg⟩
    rw [bruhatCell_mk, ← doubleCoset_eq_of_mk_eq T.subgroupB T.subgroupN hm]
    exact hg

/-- The Bruhat cell indexed by the identity of the Weyl group is `B`. -/
@[simp]
theorem bruhatCell_one : T.bruhatCell 1 = (T.subgroupB : Set G) := by
  calc
    T.bruhatCell 1 = T.bruhatCell (QuotientGroup.mk (1 : T.subgroupN)) := by
      rw [QuotientGroup.mk_one]
    _ = DoubleCoset.doubleCoset (1 : G) T.subgroupB T.subgroupB := T.bruhatCell_mk 1
    _ = T.subgroupB := doubleCoset_one_self T.subgroupB

/-- The union over `N` defining `bruhatCells` can equivalently be indexed canonically by the Weyl
group. -/
theorem bruhatCells_eq_iUnion_bruhatCell :
    T.bruhatCells = ⋃ w : T.WeylGroup, T.bruhatCell w := by
  rw [bruhatCells, ← (QuotientGroup.mk'_surjective T.intersection).iUnion_comp]
  simp only [QuotientGroup.mk'_apply, bruhatCell_mk]

/-- A product of double cosets is stable under the outer subgroup actions. -/
private theorem doubleCoset_subset_mul_doubleCoset_of_mem (B C D : Subgroup G) {a c x : G}
    (hx : x ∈ DoubleCoset.doubleCoset a B C * DoubleCoset.doubleCoset c C D) :
    DoubleCoset.doubleCoset x B D ⊆
      DoubleCoset.doubleCoset a B C * DoubleCoset.doubleCoset c C D := by
  rintro y hy
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
  obtain ⟨u, hu, v, hv, rfl⟩ := hx
  refine ⟨b₁ * u, ?_, v * b₂, ?_, by simp only [mul_assoc]⟩
  · obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hu
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨b₁ * a₁, B.mul_mem hb₁ ha₁, a₂, ha₂, by simp [mul_assoc]⟩
  · obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hv
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨c₁, hc₁, c₂ * b₂, D.mul_mem hc₂ hb₂, by simp [mul_assoc]⟩

/-- The double coset of a product occurs in the product of the corresponding double cosets. -/
private theorem doubleCoset_mul_subset_mul_doubleCoset (B C D : Subgroup G) (r w : G) :
    DoubleCoset.doubleCoset (r * w) B D ⊆
      DoubleCoset.doubleCoset r B C * DoubleCoset.doubleCoset w C D := by
  rintro x hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  refine ⟨b₁ * r, ?_, w * b₂, ?_, ?_⟩
  · exact DoubleCoset.mem_doubleCoset.mpr
      ⟨b₁, hb₁, 1, C.one_mem, by simp⟩
  · exact DoubleCoset.mem_doubleCoset.mpr
      ⟨1, C.one_mem, b₂, hb₂, by simp⟩
  · simp only [mul_assoc]

/-- **Multiplication by a simple Bruhat cell.** If `r` represents a simple reflection and `w`
lies in `N`, then `(B r B)(B w B)` is either the adjacent cell `B (r w) B` or the union of that
cell with `B w B`.

The conclusion is independent of the chosen representative `r` of the simple reflection. -/
private theorem mul_doubleCoset_eq_or_eq_union_of_mem_simple {s : T.WeylGroup}
    (hs : s ∈ T.simple)
    (r : T.subgroupN) (hr : (QuotientGroup.mk r : T.WeylGroup) = s)
    (w : T.subgroupN) :
    DoubleCoset.doubleCoset (r : G) T.subgroupB T.subgroupB *
          DoubleCoset.doubleCoset (w : G) T.subgroupB T.subgroupB =
        DoubleCoset.doubleCoset ((r * w : T.subgroupN) : G) T.subgroupB T.subgroupB ∨
      DoubleCoset.doubleCoset (r : G) T.subgroupB T.subgroupB *
          DoubleCoset.doubleCoset (w : G) T.subgroupB T.subgroupB =
        DoubleCoset.doubleCoset ((r * w : T.subgroupN) : G) T.subgroupB T.subgroupB ∪
          DoubleCoset.doubleCoset (w : G) T.subgroupB T.subgroupB := by
  obtain ⟨r₀, hr₀, hsubset⟩ := T.mul_doubleCoset_subset s hs
  have hrr₀ :
      DoubleCoset.doubleCoset (r : G) T.subgroupB T.subgroupB =
        DoubleCoset.doubleCoset (r₀ : G) T.subgroupB T.subgroupB :=
    doubleCoset_eq_of_mk_eq T.subgroupB T.subgroupN (hr.trans hr₀.symm)
  have hrwr₀w :
      DoubleCoset.doubleCoset ((r * w : T.subgroupN) : G) T.subgroupB T.subgroupB =
        DoubleCoset.doubleCoset ((r₀ * w : T.subgroupN) : G) T.subgroupB T.subgroupB := by
    apply doubleCoset_eq_of_mk_eq T.subgroupB T.subgroupN
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hr, hr₀]
  rw [hrr₀, hrwr₀w]
  let A := DoubleCoset.doubleCoset (r₀ : G) T.subgroupB T.subgroupB *
    DoubleCoset.doubleCoset (w : G) T.subgroupB T.subgroupB
  let C := DoubleCoset.doubleCoset ((r₀ * w : T.subgroupN) : G)
    T.subgroupB T.subgroupB
  let D := DoubleCoset.doubleCoset (w : G) T.subgroupB T.subgroupB
  have hC : C ⊆ A := by
    simpa only [C, A, Subgroup.coe_mul] using
      doubleCoset_mul_subset_mul_doubleCoset T.subgroupB T.subgroupB T.subgroupB
        (r₀ : G) (w : G)
  have hsubset' : A ⊆ C ∪ D := hsubset w
  by_cases hw : (w : G) ∈ A
  · right
    apply Set.Subset.antisymm hsubset'
    exact Set.union_subset hC
      (doubleCoset_subset_mul_doubleCoset_of_mem T.subgroupB T.subgroupB T.subgroupB hw)
  · left
    apply Set.Subset.antisymm
    · intro x hx
      rcases hsubset' hx with hxC | hxD
      · exact hxC
      · exfalso
        apply hw
        apply doubleCoset_subset_mul_doubleCoset_of_mem
          T.subgroupB T.subgroupB T.subgroupB hx
        rw [DoubleCoset.doubleCoset_eq_of_mem hxD]
        exact DoubleCoset.mem_doubleCoset_self T.subgroupB T.subgroupB (w : G)
    · exact hC

/-- **Weyl-indexed multiplication by a simple Bruhat cell.** For a simple reflection `s` and a
Weyl-group element `w`, the product of their cells is either the cell at `s * w` or its union
with the cell at `w`. -/
theorem bruhatCell_mul_eq_or_eq_union_of_mem_simple {s : T.WeylGroup} (hs : s ∈ T.simple)
    (w : T.WeylGroup) :
    T.bruhatCell s * T.bruhatCell w = T.bruhatCell (s * w) ∨
      T.bruhatCell s * T.bruhatCell w = T.bruhatCell (s * w) ∪ T.bruhatCell w := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective T.intersection s
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective T.intersection w
  simpa only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, Subgroup.comap_subtype,
    bruhatCell_mk] using
    T.mul_doubleCoset_eq_or_eq_union_of_mem_simple hs r rfl n

/-- The square of a simple Bruhat cell is the union of that cell with the identity cell:
`(B s B)(B s B) = B ∪ B s B`.

The nondegeneracy axiom rules out the smaller alternative in
`TauCeti.TitsSystem.bruhatCell_mul_eq_or_eq_union_of_mem_simple`. -/
@[simp]
theorem bruhatCell_mul_self_eq_union_of_mem_simple {s : T.WeylGroup} (hs : s ∈ T.simple) :
    T.bruhatCell s * T.bruhatCell s = T.bruhatCell 1 ∪ T.bruhatCell s := by
  obtain ⟨r, hr, b, hb⟩ := T.exists_conj_not_mem s hs
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (T.simple_sq_eq_one hs)
  have hr_inv :
      (QuotientGroup.mk r⁻¹ : T.WeylGroup) = QuotientGroup.mk r := by
    calc
      (QuotientGroup.mk r⁻¹ : T.WeylGroup) = (QuotientGroup.mk r)⁻¹ :=
        QuotientGroup.mk_inv T.intersection r
      _ = s⁻¹ := congrArg Inv.inv hr
      _ = s := hs_inv
      _ = QuotientGroup.mk r := hr.symm
  have hr_inv_cell :=
    doubleCoset_eq_of_mk_eq T.subgroupB T.subgroupN hr_inv
  have hsecond :
      (b : G) * (r⁻¹ : T.subgroupN) ∈
        DoubleCoset.doubleCoset (r : G) T.subgroupB T.subgroupB := by
    rw [← hr_inv_cell]
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨b, b.property, 1, T.subgroupB.one_mem, by simp⟩
  have hx_rep : (r : G) * (b : G) * (r : G)⁻¹ ∈
      DoubleCoset.doubleCoset (r : G) T.subgroupB T.subgroupB *
        DoubleCoset.doubleCoset (r : G) T.subgroupB T.subgroupB := by
    refine ⟨r, DoubleCoset.mem_doubleCoset_self T.subgroupB T.subgroupB (r : G),
      (b : G) * (r⁻¹ : T.subgroupN), hsecond, ?_⟩
    simp only [Subgroup.coe_inv, mul_assoc]
  have hx : (r : G) * (b : G) * (r : G)⁻¹ ∈ T.bruhatCell s * T.bruhatCell s := by
    rw [← hr]
    simpa only [Subgroup.comap_subtype, bruhatCell_mk] using hx_rep
  rcases T.bruhatCell_mul_eq_or_eq_union_of_mem_simple hs s with hsmall | hbig
  · exfalso
    have hx' := hx
    rw [hsmall, T.simple_sq_eq_one hs, bruhatCell_one] at hx'
    exact hb hx'
  · simpa only [T.simple_sq_eq_one hs] using hbig

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
  rw [doubleCoset_eq_of_mk_eq T.subgroupB T.subgroupN hn]
  exact (Set.mul_subset_mul_left <| Set.subset_iUnion (fun v : T.subgroupN ↦
      DoubleCoset.doubleCoset (v : G) T.subgroupB T.subgroupB) w).trans
    T.oneCell_mul_bruhatCells_subset

/-- A simple reflection preserves the union of Bruhat cells. -/
private theorem multipliesBruhatCells_simple
    (q : T.WeylGroup) (hq : q ∈ T.simple) : T.MultipliesBruhatCells q := by
  obtain ⟨r, hrq, hr⟩ := T.mul_doubleCoset_subset q hq
  intro n hn w
  rw [doubleCoset_eq_of_mk_eq T.subgroupB T.subgroupN (hn.trans hrq.symm)]
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
  rw [doubleCoset_eq_of_mk_eq T.subgroupB T.subgroupN (hn.trans hn₁n₂.symm)]
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
