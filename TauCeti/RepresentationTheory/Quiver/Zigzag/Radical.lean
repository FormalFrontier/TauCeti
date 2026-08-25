/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.SemisimpleQuotient
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Multiplication
public import TauCeti.RingTheory.Jacobson.MulOpposite

/-!
# The radical filtration of a zigzag algebra

For a finite simple graph without isolated vertices over a field, the Jacobson radical of the
zigzag relation quotient is its positive-length part.  This file makes that statement intrinsic:
`TauCeti.zigzagTrivialCoeff` reads off the coefficients of the vertex idempotents, and the radical
is its kernel.  In the vertex-arrow-volume basis this is precisely the span of the arrows and
volumes.

The multiplication table then gives the whole filtration.  A product of two radical elements is
in the span of the volume classes, every volume annihilates the radical, and hence the third
radical power vanishes.  Conversely every volume is a product of a dart with its reverse, so the
second radical layer is exactly the volume span.

## Main definitions

* `TauCeti.zigzagTrivialCoeff`: the algebra homomorphism from the zigzag quotient to
  `DoubledQuiver G → k` that retains the vertex coefficients.
* `TauCeti.zigzagPositiveSpan`: the span of the arrow and volume basis classes.
* `TauCeti.zigzagVolumeSpan`: the span of the volume basis classes.

## Main results

* `TauCeti.jacobson_nonisolatedZigzagQuotient_eq_ker`: the Jacobson radical is the kernel of
  `TauCeti.zigzagTrivialCoeff`, equivalently the positive-length span.
* `TauCeti.restrictScalars_jacobson_sq_nonisolatedZigzagQuotient_eq_zigzagVolumeSpan`: its square
  is the volume span.
* `TauCeti.jacobson_pow_three_nonisolatedZigzagQuotient_eq_bot`: its third power is zero.

## References

This proves the radical-filtration part of Layer 2 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.  See Huerfano--Khovanov, *A category for the
adjoint representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag
algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable {V : Type u}

section CommRing

variable (k : Type w) [CommRing k] (G : SimpleGraph V) [Finite V]

/-! ### The vertex-coefficient homomorphism -/

private theorem trivialCoeff_eq_zero_of_isZigzagRelator
    {x : pathAlgebra k (DoubledQuiver G)} (hx : IsZigzagRelator k G x) :
    PathAlgebra.trivialCoeff k (DoubledQuiver G) x = 0 := by
  cases hx with
  | quadratic hq =>
      cases hq with
      | nonreturn p hp _ =>
          exact PathAlgebra.trivialCoeff_ofPath_of_length_pos (hp.symm ▸ by omega)
      | equal_backtracks p q hp hq =>
          rw [map_sub,
            PathAlgebra.trivialCoeff_ofPath_of_length_pos (hp.symm ▸ by omega),
            PathAlgebra.trivialCoeff_ofPath_of_length_pos (hq.symm ▸ by omega), sub_zero]
  | long_path p hp =>
      exact PathAlgebra.trivialCoeff_ofPath_of_length_pos (by omega)

/-- The vertex-coefficient homomorphism of the zigzag relation quotient.  It sends a vertex
idempotent to its indicator function and kills every arrow and volume class. -/
noncomputable def zigzagTrivialCoeff :
    nonisolatedZigzagQuotient k G →ₐ[k] (DoubledQuiver G → k) :=
  zigzagLift k G (PathAlgebra.trivialCoeff k (DoubledQuiver G)) fun _ hx =>
    trivialCoeff_eq_zero_of_isZigzagRelator k G hx

/-- The vertex-coefficient homomorphism after the zigzag quotient map is the path-algebra
trivial-coefficient homomorphism. -/
@[simp]
theorem zigzagTrivialCoeff_zigzagMk (x : pathAlgebra k (DoubledQuiver G)) :
    zigzagTrivialCoeff k G (zigzagMk k G x) =
      PathAlgebra.trivialCoeff k (DoubledQuiver G) x := by
  exact zigzagLift_zigzagMk k G _ _ x

/-- The vertex idempotent at `i` has coefficient one at `i` and zero at every other vertex. -/
@[simp]
theorem zigzagTrivialCoeff_vertexIdempotent [DecidableEq V] (i j : V) :
    zigzagTrivialCoeff k G (zigzagMk k G (vertexIdempotent k (vertex G i))) (vertex G j) =
      if i = j then 1 else 0 := by
  classical
  rw [zigzagTrivialCoeff_zigzagMk, PathAlgebra.trivialCoeff_vertexIdempotent, Pi.single_apply]
  simp only [(vertex_injective G).eq_iff, eq_comm]

/-- Every arrow class has zero vertex coefficient. Deliberately not a `simp` lemma,
`TauCeti.PathAlgebra.ofArrow_eq_ofPath` already rewriting its left-hand side. -/
theorem zigzagTrivialCoeff_ofArrow (d : G.Dart) :
    zigzagTrivialCoeff k G (zigzagMk k G (ofArrow (arrow G d.adj))) = 0 := by
  rw [zigzagTrivialCoeff_zigzagMk, PathAlgebra.trivialCoeff_ofArrow]

/-- Every volume class has zero vertex coefficient. -/
@[simp]
theorem zigzagTrivialCoeff_zigzagVolume (i : V) :
    zigzagTrivialCoeff k G (zigzagVolume k G i) = 0 := by
  rcases em (exists j, G.Adj i j) with ⟨j, h⟩ | h
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G h, zigzagTrivialCoeff_zigzagMk,
      backtrackElem_eq_ofPath, PathAlgebra.trivialCoeff_ofPath_of_length_pos]
    simp [length_backtrackPath]
  · rw [zigzagVolume_eq_zero_of_isIsolated k G (fun j hj => h ⟨j, hj⟩), map_zero]

/-- Every family of vertex coefficients occurs. -/
theorem zigzagTrivialCoeff_surjective : Function.Surjective (zigzagTrivialCoeff k G) := by
  intro f
  obtain ⟨x, rfl⟩ := PathAlgebra.trivialCoeff_surjective k (DoubledQuiver G) f
  exact ⟨zigzagMk k G x, zigzagTrivialCoeff_zigzagMk k G x⟩

/-! ### The positive-length and volume spans -/

/-- The positive-length subspace of a zigzag algebra: the span of its arrow and volume basis
classes.  The Jacobson radical is identified with this subspace below. -/
noncomputable def zigzagPositiveSpan : Submodule k (nonisolatedZigzagQuotient k G) :=
  Submodule.span k (zigzagBasisFun k G '' Set.range Sum.inr)

/-- The degree-two subspace of a zigzag algebra: the span of its volume classes.  This is the
second radical layer. -/
noncomputable def zigzagVolumeSpan : Submodule k (nonisolatedZigzagQuotient k G) :=
  Submodule.span k (Set.range (zigzagVolume k G))

variable {k G}

/-- Every arrow class belongs to the positive-length span. -/
theorem zigzagMk_ofArrow_mem_zigzagPositiveSpan (d : G.Dart) :
    zigzagMk k G (ofArrow (arrow G d.adj)) ∈ zigzagPositiveSpan k G := by
  rw [zigzagPositiveSpan, ← zigzagBasisFun_inr_inl]
  exact Submodule.subset_span ⟨.inr (.inl d), ⟨.inl d, rfl⟩, rfl⟩

/-- Every volume class belongs to the positive-length span. -/
theorem zigzagVolume_mem_zigzagPositiveSpan (i : V) :
    zigzagVolume k G i ∈ zigzagPositiveSpan k G := by
  rw [zigzagPositiveSpan, ← zigzagBasisFun_inr_inr]
  exact Submodule.subset_span ⟨.inr (.inr i), ⟨.inr i, rfl⟩, rfl⟩

/-- Every volume class belongs to the volume span. -/
theorem zigzagVolume_mem_zigzagVolumeSpan (i : V) :
    zigzagVolume k G i ∈ zigzagVolumeSpan k G :=
  Submodule.subset_span (Set.mem_range_self i)

/-- The volume span is contained in the positive-length span. -/
theorem zigzagVolumeSpan_le_zigzagPositiveSpan :
    zigzagVolumeSpan k G ≤ zigzagPositiveSpan k G := by
  rw [zigzagVolumeSpan, Submodule.span_le, Set.range_subset_iff]
  exact zigzagVolume_mem_zigzagPositiveSpan

/-- The positive-length span is characterized by vanishing vertex coordinates. -/
theorem mem_zigzagPositiveSpan_iff (hns : ∀ i : V, ∃ j, G.Adj i j)
    {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagPositiveSpan k G ↔
      ∀ i : V, (zigzagBasis k G hns).repr x (.inl i) = 0 := by
  rw [zigzagPositiveSpan]
  simp_rw [← zigzagBasis_apply k G hns]
  rw [(zigzagBasis k G hns).mem_span_image, Finsupp.support_subset_iff]
  constructor
  · intro h i
    exact h (.inl i) (by simp)
  · intro h b hb
    rcases b with i | c
    · exact h i
    · exact False.elim (hb ⟨c, rfl⟩)

/-- The volume span is characterized by vanishing vertex and arrow coordinates. -/
theorem mem_zigzagVolumeSpan_iff (hns : ∀ i : V, ∃ j, G.Adj i j)
    {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagVolumeSpan k G ↔
      (∀ i : V, (zigzagBasis k G hns).repr x (.inl i) = 0) ∧
      ∀ d : G.Dart, (zigzagBasis k G hns).repr x (.inr (.inl d)) = 0 := by
  rw [zigzagVolumeSpan]
  have hrange : Set.range (zigzagVolume k G) =
      zigzagBasisFun k G '' Set.range (fun i => Sum.inr (Sum.inr i)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨.inr (.inr i), ⟨i, rfl⟩, zigzagBasisFun_inr_inr k G i⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (zigzagBasisFun_inr_inr k G i).symm⟩
  rw [hrange]
  simp_rw [← zigzagBasis_apply k G hns]
  rw [(zigzagBasis k G hns).mem_span_image, Finsupp.support_subset_iff]
  constructor
  · intro h
    exact ⟨fun i => h (.inl i) (by simp), fun d => h (.inr (.inl d)) (by simp)⟩
  · rintro ⟨hv, ha⟩ b hb
    rcases b with i | d | i
    · exact hv i
    · exact ha d
    · exact False.elim (hb ⟨i, rfl⟩)

/-- Evaluating the vertex-coefficient homomorphism at `i` reads the `i`-th vertex coordinate in
the vertex-arrow-volume basis. -/
theorem zigzagTrivialCoeff_apply_eq_repr (hns : ∀ i : V, ∃ j, G.Adj i j)
    (x : nonisolatedZigzagQuotient k G) (i : V) :
    zigzagTrivialCoeff k G x (vertex G i) =
      (zigzagBasis k G hns).repr x (.inl i) := by
  classical
  have repr_basisFun (b : ZigzagBasisIndex G) :
      (zigzagBasis k G hns).repr (zigzagBasisFun k G b) = Finsupp.single b 1 := by
    rw [← zigzagBasis_apply k G hns, Module.Basis.repr_self]
  have coord_basisFun (b b' : ZigzagBasisIndex G) :
      (zigzagBasis k G hns).coord b (zigzagBasisFun k G b') = if b' = b then 1 else 0 := by
    rw [Module.Basis.coord_apply, repr_basisFun, Finsupp.single_apply]
  have key : (LinearMap.proj (vertex G i)).comp (zigzagTrivialCoeff k G).toLinearMap =
      (zigzagBasis k G hns).coord (.inl i) := by
    refine (zigzagBasis k G hns).ext fun b => ?_
    rw [LinearMap.comp_apply, LinearMap.proj_apply, zigzagBasis_apply, coord_basisFun]
    rcases b with j | d | j
    · simp only [zigzagBasisFun_inl, AlgHom.toLinearMap_apply,
        zigzagTrivialCoeff_vertexIdempotent, Sum.inl.injEq, eq_comm]
    · simp only [zigzagBasisFun_inr_inl, AlgHom.toLinearMap_apply,
        zigzagTrivialCoeff_ofArrow, Pi.zero_apply, Sum.inr_ne_inl, ↓reduceIte]
    · simp only [zigzagBasisFun_inr_inr, AlgHom.toLinearMap_apply,
        zigzagTrivialCoeff_zigzagVolume, Pi.zero_apply, Sum.inr_ne_inl, ↓reduceIte]
  exact LinearMap.congr_fun key x

/-- The kernel of the vertex-coefficient map is exactly the positive-length span. -/
theorem ker_zigzagTrivialCoeff_eq_zigzagPositiveSpan (hns : ∀ i : V, ∃ j, G.Adj i j) :
    (RingHom.ker (zigzagTrivialCoeff k G).toRingHom).restrictScalars k =
      zigzagPositiveSpan k G := by
  ext x
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, mem_zigzagPositiveSpan_iff hns, funext_iff]
  simp only [Pi.zero_apply]
  constructor
  · intro hx i
    rw [← zigzagTrivialCoeff_apply_eq_repr hns]
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hx (vertex G i)
  · intro hx i
    obtain ⟨j, rfl⟩ := (vertexEquiv G).surjective i
    rw [vertexEquiv_apply]
    have hj : zigzagTrivialCoeff k G x (vertex G j) = 0 := by
      rw [zigzagTrivialCoeff_apply_eq_repr hns, hx]
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hj

/-! ### Products in the positive-length filtration -/

/-- Multiplying two positive-length elements gives a linear combination of volume classes. -/
theorem mul_mem_zigzagVolumeSpan {x y : nonisolatedZigzagQuotient k G}
    (hx : x ∈ zigzagPositiveSpan k G) (hy : y ∈ zigzagPositiveSpan k G) :
    x * y ∈ zigzagVolumeSpan k G := by
  rw [zigzagPositiveSpan] at hx hy
  refine Submodule.span_induction₂ (p := fun x y _ _ => x * y ∈ zigzagVolumeSpan k G)
    ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
    rcases hb with ⟨c, rfl⟩
    rcases hb' with ⟨c', rfl⟩
    rcases c with d | i <;> rcases c' with e | j
    · rcases eq_or_ne e d.symm with rfl | h
      · rw [zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inl,
          zigzagMk_ofArrow_mul_ofArrow_symm]
        exact Submodule.subset_span (Set.mem_range_self _)
      · rw [zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inl,
          zigzagMk_ofArrow_mul_ofArrow_of_ne k G h]
        exact Submodule.zero_mem _
    · rw [zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr,
        zigzagMk_ofArrow_mul_zigzagVolume]
      exact Submodule.zero_mem _
    · rw [zigzagBasisFun_inr_inr, zigzagBasisFun_inr_inl,
        zigzagVolume_mul_zigzagMk_ofArrow]
      exact Submodule.zero_mem _
    · rw [zigzagBasisFun_inr_inr, zigzagBasisFun_inr_inr,
        zigzagVolume_mul_zigzagVolume]
      exact Submodule.zero_mem _
  · intro x y z _ _ _ hxy hxz
    rw [add_mul]
    exact Submodule.add_mem _ hxy hxz
  · intro x y z _ _ _ hxy hxz
    rw [mul_add]
    exact Submodule.add_mem _ hxy hxz
  · intro a x y _ _ hxy
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem _ a hxy
  · intro a x y _ _ hxy
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ a hxy

/-- A volume combination annihilates every positive-length element on the left. -/
theorem mul_eq_zero_of_mem_zigzagVolumeSpan_of_mem_zigzagPositiveSpan
    {x y : nonisolatedZigzagQuotient k G}
    (hx : x ∈ zigzagVolumeSpan k G) (hy : y ∈ zigzagPositiveSpan k G) : x * y = 0 := by
  rw [zigzagVolumeSpan] at hx
  rw [zigzagPositiveSpan] at hy
  refine Submodule.span_induction₂ (p := fun x y _ _ => x * y = 0)
    ?_ (by simp) (by simp) (by simp_all [add_mul]) (by simp_all [mul_add])
    (by simp_all [Algebra.smul_mul_assoc]) (by simp_all [Algebra.mul_smul_comm]) hx hy
  rintro _ _ ⟨i, rfl⟩ ⟨b, hb, rfl⟩
  rcases hb with ⟨c, rfl⟩
  rcases c with d | j
  · rw [zigzagBasisFun_inr_inl, zigzagVolume_mul_zigzagMk_ofArrow]
  · rw [zigzagBasisFun_inr_inr, zigzagVolume_mul_zigzagVolume]

/-- Three positive-length elements have zero product. -/
theorem mul_mul_eq_zero_of_mem_zigzagPositiveSpan {x y z : nonisolatedZigzagQuotient k G}
    (hx : x ∈ zigzagPositiveSpan k G) (hy : y ∈ zigzagPositiveSpan k G)
    (hz : z ∈ zigzagPositiveSpan k G) : (x * y) * z = 0 :=
  mul_eq_zero_of_mem_zigzagVolumeSpan_of_mem_zigzagPositiveSpan
    (mul_mem_zigzagVolumeSpan hx hy) hz

end CommRing

/-! ### Identification with the Jacobson radical -/

variable (k : Type w) [Field k] (G : SimpleGraph V) [Finite V]

variable {k G}

/-- **The Jacobson radical of a zigzag relation quotient is its positive-length part.** -/
theorem jacobson_nonisolatedZigzagQuotient_eq_ker (hns : ∀ i : V, ∃ j, G.Adj i j) :
    Ring.jacobson (nonisolatedZigzagQuotient k G) =
      RingHom.ker (zigzagTrivialCoeff k G).toRingHom := by
  let _ : RingHomSurjective (zigzagTrivialCoeff k G).toRingHom :=
    ⟨zigzagTrivialCoeff_surjective k G⟩
  refine le_antisymm ?_ ?_
  · refine (Ring.le_comap_jacobson (f := (zigzagTrivialCoeff k G).toRingHom)).trans ?_
    rw [IsSemisimpleRing.jacobson_eq_bot (DoubledQuiver G → k),
      ← RingHom.ker_eq_comap_bot]
  · intro x hx
    rw [Ring.mem_jacobson_iff_isUnit_one_add_mul_left]
    intro y
    apply IsNilpotent.isUnit_one_add
    refine ⟨3, ?_⟩
    rw [pow_three]
    have hxy : y * x ∈ zigzagPositiveSpan k G := by
      rw [← ker_zigzagTrivialCoeff_eq_zigzagPositiveSpan hns]
      exact (RingHom.ker (zigzagTrivialCoeff k G).toRingHom).mul_mem_left y hx
    rw [← mul_assoc]
    exact mul_mul_eq_zero_of_mem_zigzagPositiveSpan
      (x := y * x) (y := y * x) (z := y * x) hxy hxy hxy

/-- The Jacobson radical, viewed as a `k`-submodule, is the span of the arrow and volume basis
classes. -/
theorem restrictScalars_jacobson_nonisolatedZigzagQuotient_eq_zigzagPositiveSpan
    (hns : ∀ i : V, ∃ j, G.Adj i j) :
    (Ring.jacobson (nonisolatedZigzagQuotient k G)).restrictScalars k =
      zigzagPositiveSpan k G := by
  rw [jacobson_nonisolatedZigzagQuotient_eq_ker hns,
    ker_zigzagTrivialCoeff_eq_zigzagPositiveSpan hns]

/-- Every volume class belongs to the square of the Jacobson radical: it is the product of an
arrow with its reverse. -/
theorem zigzagVolume_mem_jacobson_sq (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    zigzagVolume k G i ∈ Ring.jacobson (nonisolatedZigzagQuotient k G) ^ 2 := by
  obtain ⟨j, hij⟩ := hns i
  let d : G.Dart := ⟨(i, j), hij⟩
  -- Ideal powers use the submodule successor recursion, so expose `2` as a successor.
  rw [show 2 = 1 + 1 by omega, Ideal.IsTwoSided.pow_succ, Submodule.pow_one]
  have hd : zigzagMk k G (ofArrow (arrow G d.symm.adj)) ∈
      Ring.jacobson (nonisolatedZigzagQuotient k G) := by
    rw [jacobson_nonisolatedZigzagQuotient_eq_ker hns, RingHom.mem_ker]
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
      zigzagTrivialCoeff_ofArrow k G d.symm
  have hdr : zigzagMk k G (ofArrow (arrow G d.adj)) ∈
      Ring.jacobson (nonisolatedZigzagQuotient k G) := by
    rw [jacobson_nonisolatedZigzagQuotient_eq_ker hns, RingHom.mem_ker]
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
      zigzagTrivialCoeff_ofArrow k G d
  have hprod := Ideal.mul_mem_mul hd hdr
  have hprod' : zigzagVolume k G d.symm.snd ∈
      Ring.jacobson (nonisolatedZigzagQuotient k G) *
        Ring.jacobson (nonisolatedZigzagQuotient k G) :=
    (zigzagMk_ofArrow_mul_ofArrow_symm k G d.symm) ▸ hprod
  simpa [d] using hprod'

/-- **The square of the Jacobson radical is the volume span.** -/
theorem restrictScalars_jacobson_sq_nonisolatedZigzagQuotient_eq_zigzagVolumeSpan
    (hns : ∀ i : V, ∃ j, G.Adj i j) :
    (Ring.jacobson (nonisolatedZigzagQuotient k G) ^ 2).restrictScalars k =
      zigzagVolumeSpan k G := by
  apply le_antisymm
  · intro x hx
    -- Ideal powers use the submodule successor recursion, so expose `2` as a successor.
    rw [show 2 = 1 + 1 by omega, Ideal.IsTwoSided.pow_succ, Submodule.pow_one] at hx
    refine Submodule.mul_induction_on
      (M := Ring.jacobson (nonisolatedZigzagQuotient k G))
      (N := Ring.jacobson (nonisolatedZigzagQuotient k G))
      (C := fun z => z ∈ zigzagVolumeSpan k G) hx
      (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have hx' : x ∈ zigzagPositiveSpan k G := by
        rw [← restrictScalars_jacobson_nonisolatedZigzagQuotient_eq_zigzagPositiveSpan hns]
        exact hx
      have hy' : y ∈ zigzagPositiveSpan k G := by
        rw [← restrictScalars_jacobson_nonisolatedZigzagQuotient_eq_zigzagPositiveSpan hns]
        exact hy
      exact mul_mem_zigzagVolumeSpan hx' hy'
    · exact Submodule.add_mem _ hx hy
  · rw [zigzagVolumeSpan, Submodule.span_le, Set.range_subset_iff]
    exact zigzagVolume_mem_jacobson_sq hns

/-- **The third power of the Jacobson radical of a zigzag algebra vanishes.** -/
theorem jacobson_pow_three_nonisolatedZigzagQuotient_eq_bot
    (hns : ∀ i : V, ∃ j, G.Adj i j) :
    Ring.jacobson (nonisolatedZigzagQuotient k G) ^ 3 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  -- `Submodule.pow_succ` is stated with the exponent syntactically as a successor.
  rw [show 3 = 2 + 1 by omega, Submodule.pow_succ] at hx
  refine Submodule.mul_induction_on
    (M := Ring.jacobson (nonisolatedZigzagQuotient k G) ^ 2)
    (N := Ring.jacobson (nonisolatedZigzagQuotient k G))
    (C := fun z => z ∈ (⊥ : Ideal (nonisolatedZigzagQuotient k G))) hx
    (fun y hy z hz => ?_) (fun x y hx hy => ?_)
  · have hyv : y ∈ zigzagVolumeSpan k G := by
      rw [← restrictScalars_jacobson_sq_nonisolatedZigzagQuotient_eq_zigzagVolumeSpan hns]
      exact hy
    have hzp : z ∈ zigzagPositiveSpan k G := by
      rw [← restrictScalars_jacobson_nonisolatedZigzagQuotient_eq_zigzagPositiveSpan hns]
      exact hz
    exact mul_eq_zero_of_mem_zigzagVolumeSpan_of_mem_zigzagPositiveSpan hyv hzp
  · exact Submodule.add_mem _ hx hy

end TauCeti
