/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Triangular

/-!
# Ordering a Kostant weight basis

The positive-root triangularity results for Kostant root subgroups require an integral weight
basis ordered so that adding a positive multiple of a root moves to a smaller index. This file
constructs such an ordering from a degree functional which is positive on the chosen roots.

For a finite weight-basis index `η`, `orderedWeightIndexEquiv degree wt` numbers the indices by
`Fin (Fintype.card η)`. It first orders indices by decreasing value of `degree (wt x)` and uses an
arbitrary finite numbering only to break ties. Thus the mathematical property of the numbering
does not depend on the tie-breaker: `orderedWeight_lt_of_eq_add_nsmul` proves that every positive
weight shift moves strictly towards the beginning.

The final results apply this construction to the existing triangularity API. In particular,
`range_kostantRootSubgroupMatrix_le_upperUnitriangular_orderedWeightBasis` places each root
subgroup whose root has positive degree in the upper-unitriangular group without retaining an
ordering hypothesis.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.orderedWeightIndexEquiv`: a finite numbering by decreasing
  degree.
* `TauCeti.UniversalEnvelopingAlgebra.orderedWeightBasis`: a weight basis reindexed by that
  numbering.
* `TauCeti.UniversalEnvelopingAlgebra.orderedWeight`: the corresponding weight function.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.orderedWeight_lt_of_eq_add_nsmul`: a positive root shift
  strictly decreases the numbered index.
* `isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis`:
  a positive-degree root subgroup is upper unitriangular in the ordered basis.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§21, 26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 8.2.

This supplies the ordered positive-root basis needed by the Borel component of the pinned
Chevalley--Demazure construction in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, which
is consumed by milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ η : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]
variable {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

noncomputable section

/-! ## Ordering finite weight indices -/

/-- The auxiliary order on a finite weight index: decreasing weight degree, with an arbitrary
finite numbering used only to break ties. -/
@[instance_reducible]
private noncomputable def weightIndexLinearOrder [Fintype η]
    (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) : LinearOrder η :=
  LinearOrder.lift'
    (fun x => toLex (OrderDual.toDual (degree (wt x)), Fintype.equivFin η x))
    (fun _ _ h => (Fintype.equivFin η).injective (congrArg (fun z => (ofLex z).2) h))

/-- Number a finite family of weights by decreasing value under `degree`. Indices of equal degree
are ordered by an arbitrary finite numbering; no theorem below depends on that tie-breaker. -/
def orderedWeightIndexEquiv [Fintype η]
    (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) : η ≃ Fin (Fintype.card η) :=
  letI := weightIndexLinearOrder degree wt
  (Fintype.orderIsoFinOfCardEq η rfl).symm.toEquiv

omit [IsOrderedAddMonoid D] in
/-- A strictly larger weight degree receives a strictly smaller ordered index. -/
theorem orderedWeightIndexEquiv_lt_of_degree_lt [Fintype η]
    (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) {r s : η}
    (hrs : degree (wt s) < degree (wt r)) :
    orderedWeightIndexEquiv degree wt r < orderedWeightIndexEquiv degree wt s := by
  let _ := weightIndexLinearOrder degree wt
  apply (Fintype.orderIsoFinOfCardEq η rfl).symm.lt_iff_lt.mpr
  -- `LinearOrder.lift'` has no comparison lemma, so expose its defining lexicographic order.
  change toLex (OrderDual.toDual (degree (wt r)), Fintype.equivFin η r) <
    toLex (OrderDual.toDual (degree (wt s)), Fintype.equivFin η s)
  exact Prod.Lex.left _ _ hrs

/-- Adding a positive multiple of a positive-degree root strictly decreases the ordered index. -/
theorem orderedWeightIndexEquiv_lt_of_eq_add_nsmul [Fintype η]
    (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) {α : κ → ℤ}
    (hα : 0 < degree α) {r s : η} {n : ℕ} (hn : 0 < n)
    (hrs : wt r = wt s + n • α) :
    orderedWeightIndexEquiv degree wt r < orderedWeightIndexEquiv degree wt s := by
  apply orderedWeightIndexEquiv_lt_of_degree_lt degree wt
  rw [hrs, map_add, map_nsmul]
  exact lt_add_of_pos_right _ (nsmul_pos hα hn.ne')

/-! ## The ordered basis and its weights -/

omit [Module ℚ V] in
/-- A finite basis reindexed by decreasing degree of its recorded weights. -/
def orderedWeightBasis [Fintype η] (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ)
    (b : Module.Basis η ℤ V) : Module.Basis (Fin (Fintype.card η)) ℤ V :=
  b.reindex (orderedWeightIndexEquiv degree wt)

/-- The weight attached to an index of `orderedWeightBasis`. -/
def orderedWeight [Fintype η] (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) :
    Fin (Fintype.card η) → κ → ℤ :=
  wt ∘ (orderedWeightIndexEquiv degree wt).symm

omit [Module ℚ V] [IsOrderedAddMonoid D] in
@[simp]
theorem orderedWeightBasis_apply [Fintype η] (degree : (κ → ℤ) →+ D)
    (wt : η → κ → ℤ) (b : Module.Basis η ℤ V) (x : Fin (Fintype.card η)) :
    orderedWeightBasis degree wt b x = b ((orderedWeightIndexEquiv degree wt).symm x) := by
  rw [orderedWeightBasis, Module.Basis.reindex_apply]

omit [IsOrderedAddMonoid D] in
@[simp]
theorem orderedWeight_apply [Fintype η] (degree : (κ → ℤ) →+ D)
    (wt : η → κ → ℤ) (x : Fin (Fintype.card η)) :
    orderedWeight degree wt x = wt ((orderedWeightIndexEquiv degree wt).symm x) := (rfl)

omit [IsOrderedAddMonoid D] in
/-- The ordered basis has the same weight-vector property as the original basis. -/
theorem isCartanWeightVector_orderedWeightBasis [Fintype η]
    (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) (b : Module.Basis η ℤ V)
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) (b x))
    (x : Fin (Fintype.card η)) :
    IsCartanWeightVector h ρ (orderedWeight degree wt x) (orderedWeightBasis degree wt b x) := by
  rw [orderedWeightBasis_apply, orderedWeight_apply]
  exact hwt _

/-- In the reindexed weight basis, adding a positive multiple of a positive-degree root moves
strictly towards the beginning. This is the order hypothesis used by positive-root triangularity. -/
theorem orderedWeight_lt_of_eq_add_nsmul [Fintype η]
    (degree : (κ → ℤ) →+ D) (wt : η → κ → ℤ) {α : κ → ℤ}
    (hα : 0 < degree α) {r s : Fin (Fintype.card η)} {n : ℕ} (hn : 0 < n)
    (hrs : orderedWeight degree wt r = orderedWeight degree wt s + n • α) : r < s := by
  have h := orderedWeightIndexEquiv_lt_of_eq_add_nsmul degree wt hα hn
    (r := (orderedWeightIndexEquiv degree wt).symm r)
    (s := (orderedWeightIndexEquiv degree wt).symm s) hrs
  simpa only [Equiv.apply_symm_apply] using h

/-! ## Positive root subgroups in the ordered basis -/

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable [Fintype η] (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)
variable (degree : (κ → ℤ) →+ D)

omit [IsOrderedAddMonoid D] in
/-- Reindexing a subgroup basis preserves its weight-vector property after coercion to the
ambient rational representation. -/
theorem isCartanWeightVector_coe_orderedWeightBasis
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (x : Fin (Fintype.card η)) :
    IsCartanWeightVector h ρ (orderedWeight degree wt x)
      (((orderedWeightBasis degree wt b x : M) : V)) := by
  rw [orderedWeightBasis_apply, orderedWeight_apply]
  exact hwt _

/-- A root operator of positive degree is strictly upper triangular in every positive divided
power when the underlying weight basis is reordered by decreasing degree. -/
theorem isUpperTriangular_toMatrix_integralDividedPower_orderedWeightBasis
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {i : ι} {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hdegree : 0 < degree α) {n : ℕ} (hn : 0 < n) :
    (LinearMap.toMatrix (orderedWeightBasis degree wt b) (orderedWeightBasis degree wt b)
      (integralDividedPower
        (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
        (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem
          e h ρ hM i n hv))).IsUpperTriangular := by
  apply isUpperTriangular_toMatrix_integralDividedPower e h ρ M hM
    (orderedWeightBasis degree wt b) (orderedWeight degree wt)
    (isCartanWeightVector_coe_orderedWeightBasis h ρ M b wt degree hwt) hα
    (fun {_ _ n} hn hrs ↦ orderedWeight_lt_of_eq_add_nsmul degree wt hdegree hn hrs) hn

/-- A root subgroup of positive degree is upper unitriangular in the weight basis ordered by
decreasing degree. The choice used to order equal-degree weight spaces does not enter the proof. -/
theorem isUpperUnitriangular_kostantRootSubgroupMatrix_orderedWeightBasis
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {i : ι} {α : κ → ℤ} (hnil : IsNilpotent
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i) (hdegree : 0 < degree α)
    {A : Type*} [CommRing A]
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ((kostantRootSubgroupMatrix e h ρ M hM i hnil
        (orderedWeightBasis degree wt b) f :
          Matrix.GeneralLinearGroup (Fin (Fintype.card η)) A) :
      Matrix (Fin (Fintype.card η)) (Fin (Fintype.card η)) A).IsUpperUnitriangular := by
  apply isUpperUnitriangular_kostantRootSubgroupMatrix e h ρ M hM
    (orderedWeightBasis degree wt b) (orderedWeight degree wt) i hnil
    (isCartanWeightVector_coe_orderedWeightBasis h ρ M b wt degree hwt) hα
  intro r s n hn hrs
  exact orderedWeight_lt_of_eq_add_nsmul degree wt hdegree hn hrs

/-- The image of every positive-degree root subgroup lies in the upper-unitriangular subgroup
after reindexing the weight basis by decreasing degree. -/
theorem range_kostantRootSubgroupMatrix_le_upperUnitriangular_orderedWeightBasis
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {i : ι} {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hdegree : 0 < degree α)
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    {A : Type*} [CommRing A] :
    (kostantRootSubgroupMatrix e h ρ M hM i hnil
      (orderedWeightBasis degree wt b) (A := A)).range ≤
        upperUnitriangularGroup (Fin (Fintype.card η)) A := by
  apply range_kostantRootSubgroupMatrix_le_upperUnitriangular e h ρ M hM
    (orderedWeightBasis degree wt b) (orderedWeight degree wt) i hnil
    (isCartanWeightVector_coe_orderedWeightBasis h ρ M b wt degree hwt) hα
  intro r s n hn hrs
  exact orderedWeight_lt_of_eq_add_nsmul degree wt hdegree hn hrs

end

end TauCeti.UniversalEnvelopingAlgebra
