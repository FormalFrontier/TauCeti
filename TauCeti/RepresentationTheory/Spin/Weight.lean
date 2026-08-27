/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Subalgebra
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction

/-!
# The weights of the spinor module

A polarization of a quadratic space `(V, Q)` splits it as `W ⊕ W' ⊕ L` with `W` and `W'`
isotropic and in perfect `QuadraticMap.polar`-pairing, and `TauCeti.spinAction` makes the exterior
algebra `S = ⋀·W` a module over `CliffordAlgebra Q`. This file diagonalizes `S`.

Fix a basis `w : ι → W`. The pairing turns each coordinate functional of that basis into a vector
`w' i` of `W'`, and the Clifford bivector

```text
H i = bivector Q (w i) (w' i) = ⅟2 (ι (w i) * ι (w' i) - ι (w' i) * ι (w i))
```

is a quadratic element of the Clifford algebra, so it lies in the Lie subalgebra
`CliffordAlgebra.quadraticLieSubalgebra Q` that realizes `𝔰𝔬(V, Q)`. These elements commute
(`TauCeti.SpinPolarizationData.lie_diagonalBivector_diagonalBivector`), and they act *diagonally*
on the exterior basis of `S`: on the basis vector indexed by
a finite set `s` of indices — the wedge of the `w i` for `i ∈ s` — the element `H i` acts by

```text
spinWeight K s i = if i ∈ s then ⅟2 else -⅟2.
```

So the weight of that basis vector is the **half-integer sign vector** `½(±1, …, ±1)`, the signs
recording which basis vectors of `W` occur. Half-integrality is recorded literally, in
`TauCeti.spinWeight_add_self_of_mem` and `TauCeti.spinWeight_add_self_of_notMem`: twice a weight
is `±1`.

Two facts pin the diagonalization down. The simultaneous eigenspace at the eigenvalue tuple
`spinWeight K s` is exactly the *line* spanned by the corresponding exterior basis vector
(`TauCeti.spinWeightSpace_spinWeight`), and, over a ring without zero divisors, every other tuple
of eigenvalues has zero simultaneous eigenspace
(`TauCeti.spinWeightSpace_eq_bot_of_notMem_range`). Hence, for a finite index type, the tuples
that do occur are exactly the sign vectors (`TauCeti.range_spinWeight`), and, when `K` is
nontrivial, there are `2 ^ l` of them on an index type of cardinality `l`
(`TauCeti.ncard_range_spinWeight`); their lines exhaust
`S` (`TauCeti.iSup_spinWeightSpace_eq_top`).

The cancellation behind the first of those needs no field: two distinct sign vectors differ in
some coordinate by `±1`, a unit, so a coefficient annihilated by that difference vanishes over any
commutative ring in which `2` is invertible.

What is deliberately absent: the elements `H i` are only shown to commute, and no Lie subalgebra
of `CliffordAlgebra.quadraticLieSubalgebra Q` is exhibited as a Cartan subalgebra, so "weight"
below always means a tuple of simultaneous eigenvalues for the indexed family `H`, not a linear
character of a Cartan subalgebra. No ordering of `ι` is used to single out a Borel, so no weight
is called highest here; the elements `H i` are not compared with a matrix model of `𝔰𝔬(2l + 1)`
or `𝔰𝔬(2l)`; and the abstract `Bₗ`/`Dₗ` root data are not mentioned. Those comparisons are the
rest of the layer this file opens.

## Main definitions

* `TauCeti.SpinPolarizationData.diagonalBivector`: the Clifford bivector `H i` of a basis vector of
  `W` and its dual vector in `W'`.
* `TauCeti.spinWeight`: the sign vector `½(±1, …, ±1)` attached to a finite set of indices.
* `TauCeti.spinWeightSpace`: the simultaneous eigenspace of the elements `H i` at a prescribed
  tuple of eigenvalues.

## Main results

* `TauCeti.SpinPolarizationData.lie_diagonalBivector_diagonalBivector`: **the diagonal bivectors
  commute.**
* `TauCeti.SpinPolarizationData.spinAction_diagonalBivector_basis`: **the diagonal bivectors act
  diagonally on the exterior basis**, by `⅟2` or `-⅟2`.
* `TauCeti.spinWeightSpace_spinWeight`: **each weight space is the line spanned by its exterior
  basis vector.**
* `TauCeti.spinWeightSpace_eq_bot_of_notMem_range` and `TauCeti.spinWeightSpace_ne_bot_iff`: no
  other tuple of eigenvalues occurs.
* `TauCeti.iSup_spinWeightSpace_eq_top`: the weight spaces exhaust the spinor module.
* `TauCeti.range_spinWeight`: for a finite index type the weights are exactly the sign vectors,
  and, when `K` is nontrivial, `TauCeti.ncard_range_spinWeight` counts them: there are `2 ^ l` of
  them on an index type of cardinality `l`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1: the weights
  `½(±1, …, ±1)` of the spin module `S = ⋀·W`.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 5, "Weights of the spin module".
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The sign-vector weights -/

/-- The **weight** of the exterior basis vector indexed by a finite set `s`: the half-integer
sign vector `½(±1, …, ±1)` whose `i`-th sign records whether `i` occurs in `s`. -/
def spinWeight (K : Type u) [CommRing K] [Invertible (2 : K)] {ι : Type w} [DecidableEq ι]
    (s : Finset ι) (i : ι) : K :=
  if i ∈ s then ⅟(2 : K) else -⅟(2 : K)

section Weight

variable {K : Type u} [CommRing K] [Invertible (2 : K)] {ι : Type w} [DecidableEq ι]

theorem spinWeight_apply (s : Finset ι) (i : ι) :
    spinWeight K s i = if i ∈ s then ⅟(2 : K) else -⅟(2 : K) :=
  -- `(rfl)`, not `rfl`: the body of `spinWeight` is not `@[expose]`d.
  (rfl)

@[simp]
theorem spinWeight_of_mem {s : Finset ι} {i : ι} (h : i ∈ s) :
    spinWeight K s i = ⅟(2 : K) := by
  simp [spinWeight_apply, h]

@[simp]
theorem spinWeight_of_notMem {s : Finset ι} {i : ι} (h : i ∉ s) :
    spinWeight K s i = -⅟(2 : K) := by
  simp [spinWeight_apply, h]

/-- Twice the inverse of `2` is `1`: the scalar identity behind half-integrality. -/
private theorem invOf_two_add_invOf_two : (⅟(2 : K)) + ⅟(2 : K) = 1 := by
  rw [← two_mul, mul_invOf_self]

/-- **The weights are half-integral**: twice the weight at an occupied index is `1`. -/
theorem spinWeight_add_self_of_mem {s : Finset ι} {i : ι} (h : i ∈ s) :
    spinWeight K s i + spinWeight K s i = 1 := by
  rw [spinWeight_of_mem h]
  exact invOf_two_add_invOf_two

/-- **The weights are half-integral**: twice the weight at a vacant index is `-1`. -/
theorem spinWeight_add_self_of_notMem {s : Finset ι} {i : ι} (h : i ∉ s) :
    spinWeight K s i + spinWeight K s i = -1 := by
  rw [spinWeight_of_notMem h, ← neg_add, invOf_two_add_invOf_two]

/-- Distinct index sets have weights that differ by a **unit** in some coordinate. This is the
cancellation making the weight spaces one-dimensional over an arbitrary commutative ring. -/
theorem exists_spinWeight_sub_eq_one_or_neg_one {s t : Finset ι} (h : s ≠ t) :
    ∃ i, spinWeight K s i - spinWeight K t i = 1 ∨ spinWeight K s i - spinWeight K t i = -1 := by
  obtain ⟨i, hi⟩ := not_forall.mp fun hall => h (Finset.ext hall)
  refine ⟨i, ?_⟩
  by_cases his : i ∈ s
  · have hit : i ∉ t := fun hit => hi ⟨fun _ => hit, fun _ => his⟩
    exact Or.inl <| by
      rw [spinWeight_of_mem his, spinWeight_of_notMem hit, sub_neg_eq_add,
        invOf_two_add_invOf_two]
  · have hit : i ∈ t := by
      by_contra hit
      exact hi ⟨fun h' => absurd h' his, fun h' => absurd h' hit⟩
    exact Or.inr <| by
      rw [spinWeight_of_notMem his, spinWeight_of_mem hit, sub_eq_add_neg, ← neg_add,
        invOf_two_add_invOf_two]

/-- Distinct index sets carry distinct weights. -/
theorem spinWeight_injective [Nontrivial K] :
    Function.Injective (spinWeight K (ι := ι)) := by
  intro s t hst
  by_contra h
  obtain ⟨i, hi⟩ := exists_spinWeight_sub_eq_one_or_neg_one (K := K) h
  rw [hst, sub_self] at hi
  rcases hi with hi | hi
  · exact one_ne_zero hi.symm
  · exact one_ne_zero (neg_eq_zero.mp hi.symm)

/-- **The values of `TauCeti.spinWeight` are exactly the sign vectors** `½(±1, …, ±1)`, when the
index type is finite. Together with `TauCeti.spinWeightSpace_ne_bot_iff` this says the tuples of
eigenvalues occurring in the spinor module are exactly those sign vectors;
`TauCeti.ncard_range_spinWeight` counts them. -/
theorem range_spinWeight [Finite ι] :
    Set.range (spinWeight K (ι := ι)) = {χ : ι → K | ∀ i, χ i = ⅟(2 : K) ∨ χ i = -⅟(2 : K)} := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  ext χ
  constructor
  · rintro ⟨s, rfl⟩ i
    by_cases h : i ∈ s
    · exact Or.inl (spinWeight_of_mem h)
    · exact Or.inr (spinWeight_of_notMem h)
  · intro hχ
    refine ⟨Finset.univ.filter fun i => χ i = ⅟(2 : K), ?_⟩
    funext i
    by_cases h : χ i = ⅟(2 : K)
    · rw [spinWeight_of_mem (by simp [h]), h]
    · rw [spinWeight_of_notMem (by simp [h]), (hχ i).resolve_left h]

/-- **There are exactly `2 ^ l` sign vectors** on a finite index type of cardinality `l`: distinct
index sets carry distinct weights, and there are `2 ^ l` index sets. -/
theorem ncard_range_spinWeight [Finite ι] [Nontrivial K] :
    (Set.range (spinWeight K (ι := ι))).ncard = 2 ^ Nat.card ι := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [Set.ncard_range_of_injective spinWeight_injective, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_finset]

end Weight

namespace SpinPolarizationData

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [LinearOrder ι] (b : Module.Basis ι K P.W)

/-! ### The diagonal bivectors -/

variable [Invertible (2 : K)]

/-- The `i`-th **diagonal bivector** of a polarization with a chosen basis of its isotropic
summand: the Clifford bivector of the `i`-th basis vector and its dual. -/
noncomputable def diagonalBivector (i : ι) : CliffordAlgebra Q :=
  bivector Q (b i : V) (P.dualVector b i : V)

omit [LinearOrder ι] in
theorem diagonalBivector_def (i : ι) :
    P.diagonalBivector b i = bivector Q (b i : V) (P.dualVector b i : V) :=
  -- `(rfl)`, not `rfl`: the body of `diagonalBivector` is not `@[expose]`d.
  (rfl)

omit [LinearOrder ι] in
/-- The diagonal bivectors are quadratic elements of the Clifford algebra, so they lie in the Lie
subalgebra that realizes `𝔰𝔬(V, Q)`. -/
theorem diagonalBivector_mem_quadraticLieSubalgebra (i : ι) :
    P.diagonalBivector b i ∈ quadraticLieSubalgebra Q := by
  rw [diagonalBivector_def]
  exact bivector_mem_quadraticLieSubalgebra Q _ _

/-- **The diagonal bivectors commute.** Of the four polar values entering the bracket of two
Clifford bivectors only the two Kronecker pairings survive, and off the diagonal they vanish too;
on the diagonal the two surviving contributions cancel. -/
theorem lie_diagonalBivector_diagonalBivector (i j : ι) :
    ⁅P.diagonalBivector b i, P.diagonalBivector b j⁆ = 0 := by
  have h2 : polar Q (b i : V) (b j : V) = 0 := P.polar_W_eq_zero (b i) (b j)
  have h3 : polar Q (P.dualVector b i : V) (P.dualVector b j : V) = 0 :=
    P.polar_W'_eq_zero _ _
  by_cases h : i = j
  · subst h
    have h1 : polar Q (P.dualVector b i : V) (b i : V) = 1 := by
      rw [QuadraticMap.polar_comm]
      exact P.polar_dualVector_self b i
    have h4 : polar Q (b i : V) (P.dualVector b i : V) = 1 := P.polar_dualVector_self b i
    rw [diagonalBivector_def, lie_bivector_bivector, h1, h2, h3, h4]
    simp only [one_smul, zero_smul, sub_zero, zero_sub, bivector_def, map_neg, mul_neg, neg_mul]
    module
  · have hji : ¬ j = i := fun hji => h hji.symm
    have h1 : polar Q (P.dualVector b i : V) (b j : V) = 0 := by
      rw [QuadraticMap.polar_comm, P.polar_dualVector b i j]
      simp [hji]
    have h4 : polar Q (b i : V) (P.dualVector b j : V) = 0 := by
      rw [P.polar_dualVector b j i]
      simp [h]
    rw [diagonalBivector_def, diagonalBivector_def, lie_bivector_bivector, h1, h2, h3, h4]
    simp [bivector_def]

/-! ### The diagonal action on the exterior basis -/

omit [Invertible (2 : K)] in
/-- Creation after annihilation at the same index is the **occupation projection**: it fixes the
exterior basis vectors containing that index and kills the others. -/
theorem wedge_contract_dualVector_basis (i : ι) (s : Finset ι) :
    P.wedge (b i) (P.contract (P.dualVector b i) (b.ExteriorAlgebra s)) =
      if i ∈ s then b.ExteriorAlgebra s else 0 := by
  rw [P.contract_apply, pairingEquiv_dualVector, P.wedge_apply]
  exact ExteriorAlgebra.ι_mul_contractLeft_coord_basis b i s

omit [Invertible (2 : K)] in
/-- Annihilation after creation at the same index is the complementary **vacancy projection**,
by the creation–annihilation anticommutator and the Kronecker pairing. -/
theorem contract_dualVector_wedge_basis (i : ι) (s : Finset ι) :
    P.contract (P.dualVector b i) (P.wedge (b i) (b.ExteriorAlgebra s)) =
      b.ExteriorAlgebra s - if i ∈ s then b.ExteriorAlgebra s else 0 := by
  rw [P.contract_wedge (b i) (P.dualVector b i), P.polar_dualVector_self b i, one_smul,
    wedge_contract_dualVector_basis]

/-- **The diagonal bivectors act diagonally on the exterior basis** of the spinor module: the `i`-th
one multiplies the basis vector indexed by `s` by `⅟2` when `i ∈ s` and by `-⅟2` otherwise, so
that basis vector is a weight vector of weight `TauCeti.spinWeight K s`. -/
@[simp]
theorem spinAction_diagonalBivector_basis (i : ι) (s : Finset ι) :
    spinAction Q P (P.diagonalBivector b i) (b.ExteriorAlgebra s) =
      spinWeight K s i • b.ExteriorAlgebra s := by
  rw [diagonalBivector_def, bivector_def, map_smul, map_sub, map_mul, map_mul, spinAction_ι,
    spinAction_ι, P.cliffordOperator_coe_W, P.cliffordOperator_coe_W']
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
  rw [wedge_contract_dualVector_basis, contract_dualVector_wedge_basis]
  by_cases h : i ∈ s
  · rw [spinWeight_of_mem h]
    simp [h]
  · rw [spinWeight_of_notMem h]
    simp [h]

end SpinPolarizationData

/-! ### The weight-space decomposition -/

section WeightSpace

variable {K : Type u} [CommRing K] [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [LinearOrder ι] (b : Module.Basis ι K P.W)

/-- The **weight space** of the spinor module at a tuple `χ` of prescribed eigenvalues: the
simultaneous eigenspace of the operators `H i`, the `i`-th one acting with eigenvalue `χ i`. -/
noncomputable def spinWeightSpace (Q : QuadraticForm K V) (P : SpinPolarizationData Q)
    (b : Module.Basis ι K P.W) (χ : ι → K) : Submodule K (ExteriorAlgebra K P.W) :=
  ⨅ i : ι, Module.End.eigenspace (spinAction Q P (P.diagonalBivector b i)) (χ i)

omit [LinearOrder ι] in
theorem spinWeightSpace_def (χ : ι → K) :
    spinWeightSpace Q P b χ =
      ⨅ i : ι, Module.End.eigenspace (spinAction Q P (P.diagonalBivector b i)) (χ i) :=
  -- `(rfl)`, not `rfl`: the body of `spinWeightSpace` is not `@[expose]`d.
  (rfl)

omit [LinearOrder ι] in
/-- Membership in a weight space, unfolded: a spinor lies in it exactly when every `H i` scales
it by the prescribed eigenvalue `χ i`. -/
@[simp]
theorem mem_spinWeightSpace_iff {χ : ι → K} {x : ExteriorAlgebra K P.W} :
    x ∈ spinWeightSpace Q P b χ ↔ ∀ i, spinAction Q P (P.diagonalBivector b i) x = χ i • x := by
  rw [spinWeightSpace_def, Submodule.mem_iInf]
  exact forall_congr' fun _ => Module.End.mem_eigenspace_iff

/-- The exterior basis vector indexed by `s` lies in the weight space at `spinWeight K s`. -/
theorem basis_mem_spinWeightSpace (s : Finset ι) :
    b.ExteriorAlgebra s ∈ spinWeightSpace Q P b (spinWeight K s) :=
  (mem_spinWeightSpace_iff P b).mpr fun i => P.spinAction_diagonalBivector_basis b i s

/-- The diagonal bivectors are diagonal in the exterior basis, read on coordinates: applying `H i`
scales the `t`-th coordinate of any spinor by the `i`-th entry of the weight of `t`. -/
theorem repr_spinAction_diagonalBivector (i : ι) (t : Finset ι) (x : ExteriorAlgebra K P.W) :
    b.ExteriorAlgebra.repr (spinAction Q P (P.diagonalBivector b i) x) t =
      spinWeight K t i * b.ExteriorAlgebra.repr x t := by
  have key :
      (Finsupp.lapply t).comp (b.ExteriorAlgebra.repr.toLinearMap.comp
          (spinAction Q P (P.diagonalBivector b i) : Module.End K (ExteriorAlgebra K P.W))) =
        spinWeight K t i •
          (Finsupp.lapply t).comp b.ExteriorAlgebra.repr.toLinearMap := by
    apply b.ExteriorAlgebra.ext
    intro s
    by_cases hst : s = t
    · subst hst
      simp [SpinPolarizationData.spinAction_diagonalBivector_basis]
    · simp [SpinPolarizationData.spinAction_diagonalBivector_basis, hst]
  simpa using LinearMap.congr_fun key x

/-- **Each weight space of the spinor module is a line**, spanned by the exterior basis vector
carrying that weight. Distinct sign vectors differ somewhere by a unit, which is what forces every
other coordinate of a weight vector to vanish. -/
@[simp]
theorem spinWeightSpace_spinWeight (s : Finset ι) :
    spinWeightSpace Q P b (spinWeight K s) = K ∙ b.ExteriorAlgebra s := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [mem_spinWeightSpace_iff] at hx
    have hzero : ∀ t : Finset ι, t ≠ s → b.ExteriorAlgebra.repr x t = 0 := by
      intro t ht
      obtain ⟨i, hi⟩ := exists_spinWeight_sub_eq_one_or_neg_one (K := K) ht
      have hcoord := repr_spinAction_diagonalBivector P b i t x
      rw [hx i, map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
      have hsub : (spinWeight K t i - spinWeight K s i) * b.ExteriorAlgebra.repr x t = 0 := by
        rw [sub_mul, ← hcoord, sub_self]
      rcases hi with hi | hi
      · rwa [hi, one_mul] at hsub
      · rw [hi, neg_one_mul, neg_eq_zero] at hsub
        exact hsub
    have hrepr : b.ExteriorAlgebra.repr x = Finsupp.single s (b.ExteriorAlgebra.repr x s) := by
      ext t
      by_cases hts : t = s
      · rw [hts]
        simp
      · have hst : ¬ s = t := fun h => hts h.symm
        rw [hzero t hts, Finsupp.single_apply]
        simp [hst]
    have hxeq : x = b.ExteriorAlgebra.repr x s • b.ExteriorAlgebra s := by
      apply b.ExteriorAlgebra.repr.injective
      rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
      exact hrepr
    rw [hxeq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact basis_mem_spinWeightSpace P b s

/-- **No tuple of eigenvalues other than a sign vector occurs** in the spinor module, over a ring
without zero divisors. -/
theorem spinWeightSpace_eq_bot_of_notMem_range [NoZeroDivisors K] {χ : ι → K}
    (hχ : χ ∉ Set.range (spinWeight K (ι := ι))) :
    spinWeightSpace Q P b χ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_spinWeightSpace_iff] at hx
  rw [Submodule.mem_bot]
  apply b.ExteriorAlgebra.repr.injective
  rw [map_zero]
  ext t
  have hne : spinWeight K t ≠ χ := fun h => hχ ⟨t, h⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hcoord := repr_spinAction_diagonalBivector P b i t x
  rw [hx i, map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
  have hsub : (spinWeight K t i - χ i) * b.ExteriorAlgebra.repr x t = 0 := by
    rw [sub_mul, ← hcoord, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hi
  · simpa using h

/-- **The weights of the spinor module are exactly the sign vectors**: a tuple of eigenvalues has
a nonzero simultaneous eigenspace precisely when it is one of the `TauCeti.spinWeight K s`. -/
@[simp]
theorem spinWeightSpace_ne_bot_iff [Nontrivial K] [NoZeroDivisors K] {χ : ι → K} :
    spinWeightSpace Q P b χ ≠ ⊥ ↔ χ ∈ Set.range (spinWeight K (ι := ι)) := by
  constructor
  · intro h
    by_contra hχ
    exact h (spinWeightSpace_eq_bot_of_notMem_range P b hχ)
  · rintro ⟨s, rfl⟩
    rw [spinWeightSpace_spinWeight, Ne, Submodule.span_singleton_eq_bot]
    exact b.ExteriorAlgebra.ne_zero s

/-- **The weight spaces exhaust the spinor module**: the lines carrying the sign vectors span
`S = ⋀·W`. -/
theorem iSup_spinWeightSpace_eq_top :
    ⨆ s : Finset ι, spinWeightSpace Q P b (spinWeight K s) = ⊤ := by
  rw [eq_top_iff, ← b.ExteriorAlgebra.span_eq, Submodule.span_le]
  rintro y ⟨s, rfl⟩
  exact Submodule.mem_iSup_of_mem s (basis_mem_spinWeightSpace P b s)

end WeightSpace

end TauCeti
