/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Radical
public import TauCeti.RingTheory.PrimitiveIdempotent

/-!
# Vertex projectives of a zigzag algebra

For a finite simple graph without isolated vertices, this file constructs the left projective
module at a vertex `i` as the principal left ideal `Z e_i` in the zigzag relation quotient.  Right
multiplication by `e_i` is a projection from the regular module onto this ideal, so the module is
projective.  Its idempotent is primitive, so the module is also indecomposable.

The vertex projective has an explicit basis: the idempotent `e_i`, the arrows whose tail is `i`,
and the volume class `x_i`.  Thus its dimension is `2 + deg(i)`.  The choice of arrows with tail
`i`, rather than head `i`, is forced by Tau Ceti's later-factor-first convention: `Z e_i` consists
of paths which begin at `i`.

## Main definitions

* `TauCeti.zigzagProjective`: the left ideal `Z e_i`.
* `TauCeti.ZigzagProjectiveBasisIndex`: one vertex generator, the darts leaving `i`, and one
  volume generator.
* `TauCeti.zigzagProjectiveBasis`: the corresponding basis of `Z e_i`.

## Main results

* `TauCeti.zigzagProjective_projective`: `Z e_i` is projective as a left `Z`-module.
* `TauCeti.isIndecomposableModule_zigzagProjective`: `Z e_i` is indecomposable.
* `TauCeti.finrank_zigzagProjective`: `dim_k Z e_i = 2 + deg(i)`.

## References

This is the vertex-projective part of Layer 3 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.  See Huerfano--Khovanov, *A category for the
adjoint representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag
algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- The vertex idempotent of the zigzag relation quotient. -/
noncomputable abbrev zigzagVertexIdempotent (i : V) : nonisolatedZigzagQuotient k G :=
  zigzagMk k G (vertexIdempotent k (vertex G i))

/-- The left projective of the zigzag relation quotient at `i`, namely the principal left ideal
`Z e_i`. -/
noncomputable def zigzagProjective (i : V) : Ideal (nonisolatedZigzagQuotient k G) :=
  Ideal.span {zigzagVertexIdempotent k G i}

/-- Membership in `Z e_i`: an element belongs to the vertex projective exactly when right
multiplication by `e_i` fixes it. -/
@[simp]
theorem mem_zigzagProjective_iff {i : V} {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagProjective k G i ↔ x * zigzagVertexIdempotent k G i = x :=
  mem_span_singleton_iff_mul_eq_self (zigzagMk_vertexIdempotent_mul_self k G i)

/-- The distinguished generator `e_i` of the vertex projective. -/
noncomputable def zigzagProjectiveGenerator (i : V) : zigzagProjective k G i :=
  spanSingletonGenerator (zigzagVertexIdempotent k G i)

@[simp]
theorem coe_zigzagProjectiveGenerator (i : V) :
    (zigzagProjectiveGenerator k G i : nonisolatedZigzagQuotient k G) =
      zigzagVertexIdempotent k G i :=
  coe_spanSingletonGenerator _

/-! ### Projectivity -/

/-- Right multiplication by `e_i`, corestricted to `Z e_i`. -/
noncomputable def zigzagProjectiveProjection (i : V) :
    nonisolatedZigzagQuotient k G →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G i where
  toFun x := ⟨x * zigzagVertexIdempotent k G i,
    Ideal.mem_span_singleton'.2 ⟨x, rfl⟩⟩
  map_add' x y := Subtype.ext (add_mul x y _)
  map_smul' x y := Subtype.ext (mul_assoc x y _)

@[simp]
theorem coe_zigzagProjectiveProjection (i : V) (x : nonisolatedZigzagQuotient k G) :
    (zigzagProjectiveProjection k G i x : nonisolatedZigzagQuotient k G) =
      x * zigzagVertexIdempotent k G i :=
  (rfl)

/-- Projecting an element of `Z e_i` back onto `Z e_i` fixes it. -/
@[simp]
theorem zigzagProjectiveProjection_coe (i : V) (x : zigzagProjective k G i) :
    zigzagProjectiveProjection k G i (x : nonisolatedZigzagQuotient k G) = x := by
  apply Subtype.ext
  rw [coe_zigzagProjectiveProjection]
  exact (mem_zigzagProjective_iff k G).mp x.2

/-- The projection onto `Z e_i` splits its inclusion into the regular module. -/
theorem zigzagProjectiveProjection_comp_subtype (i : V) :
    (zigzagProjectiveProjection k G i).comp (zigzagProjective k G i).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact zigzagProjectiveProjection_coe k G i x

/-- The vertex ideal `Z e_i` is a projective left module over the zigzag relation quotient. -/
theorem zigzagProjective_projective (i : V) :
    Module.Projective (nonisolatedZigzagQuotient k G) (zigzagProjective k G i) :=
  Module.Projective.of_split (zigzagProjective k G i).subtype
    (zigzagProjectiveProjection k G i) (zigzagProjectiveProjection_comp_subtype k G i)

/-! ### Indecomposability -/

/-- A vertex idempotent is nonzero in the zigzag relation quotient. -/
theorem zigzagVertexIdempotent_ne_zero (i : V) : zigzagVertexIdempotent k G i ≠ 0 := by
  classical
  intro hi
  have h := zigzagTrivialCoeff_vertexIdempotent k G i i
  rw [← zigzagVertexIdempotent, hi, map_zero, Pi.zero_apply] at h
  simp at h

/-- An idempotent in the kernel of the vertex-coefficient map vanishes.  The kernel is the
Jacobson radical, whose third power is zero. -/
private theorem eq_zero_of_isIdempotentElem_of_zigzagTrivialCoeff_eq_zero
    (hns : ∀ i : V, ∃ j, G.Adj i j) {x : nonisolatedZigzagQuotient k G}
    (hx : IsIdempotentElem x) (hcoeff : zigzagTrivialCoeff k G x = 0) : x = 0 := by
  have hjac : x ∈ Ring.jacobson (nonisolatedZigzagQuotient k G) := by
    rw [jacobson_nonisolatedZigzagQuotient_eq_ker hns, RingHom.mem_ker]
    exact hcoeff
  have hpow := Ideal.pow_mem_pow hjac 3
  rw [jacobson_pow_three_nonisolatedZigzagQuotient_eq_bot hns, Ideal.mem_bot,
    pow_three, hx.eq, hx.eq] at hpow
  exact hpow

/-- If two orthogonal idempotents sum to zero, the first one is zero. -/
private theorem eq_zero_of_isIdempotentElem_of_add_eq_zero_of_mul_eq_zero {a b : k}
    (ha : IsIdempotentElem a) (hsum : a + b = 0) (hmul : a * b = 0) : a = 0 := by
  have hab : a = -b := eq_neg_of_add_eq_zero_left hsum
  calc
    a = a * a := ha.eq.symm
    _ = a * (-b) := congrArg (a * ·) hab
    _ = -(a * b) := mul_neg _ _
    _ = 0 := by rw [hmul, neg_zero]

/-- The vertex idempotents of a zigzag relation quotient are primitive.  Modulo the Jacobson
radical they are the coordinate idempotents in the product `V → k`; an idempotent summand which
vanishes there lies in the nilpotent radical and is therefore zero. -/
theorem isPrimitiveIdempotent_zigzagVertexIdempotent
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    IsPrimitiveIdempotent (zigzagVertexIdempotent k G i) := by
  classical
  refine
    { isIdempotentElem := zigzagMk_vertexIdempotent_mul_self k G i
      ne_zero := zigzagVertexIdempotent_ne_zero k G i
      eq_zero_or_eq_zero_of_add := ?_ }
  intro e₁ e₂ he₁ he₂ he₁₂ he₂₁ hsum
  let φ := zigzagTrivialCoeff k G
  have hφe₁ : IsIdempotentElem (φ e₁) := he₁.map φ.toRingHom
  have hφe₂ : IsIdempotentElem (φ e₂) := he₂.map φ.toRingHom
  have hφ₁₂ : φ e₁ * φ e₂ = 0 := by rw [← map_mul, he₁₂, map_zero]
  have hφ₂₁ : φ e₂ * φ e₁ = 0 := by rw [← map_mul, he₂₁, map_zero]
  have hφsum : φ e₁ + φ e₂ = φ (zigzagVertexIdempotent k G i) := by
    rw [← map_add, hsum]
  have hvalue₁ (j : V) :
      IsIdempotentElem (zigzagTrivialCoeff k G e₁ (vertex G j)) := by
    -- Unfold the pointwise idempotence hidden by the `IsIdempotentElem` wrapper.
    change zigzagTrivialCoeff k G e₁ (vertex G j) *
        zigzagTrivialCoeff k G e₁ (vertex G j) = zigzagTrivialCoeff k G e₁ (vertex G j)
    simpa only [φ, Pi.mul_apply] using congrArg (fun f => f (vertex G j)) hφe₁.eq
  have hvalue₂ (j : V) :
      IsIdempotentElem (zigzagTrivialCoeff k G e₂ (vertex G j)) := by
    -- Unfold the pointwise idempotence hidden by the `IsIdempotentElem` wrapper.
    change zigzagTrivialCoeff k G e₂ (vertex G j) *
        zigzagTrivialCoeff k G e₂ (vertex G j) = zigzagTrivialCoeff k G e₂ (vertex G j)
    simpa only [φ, Pi.mul_apply] using congrArg (fun f => f (vertex G j)) hφe₂.eq
  have hmul₁₂ (j : V) : zigzagTrivialCoeff k G e₁ (vertex G j) *
      zigzagTrivialCoeff k G e₂ (vertex G j) = 0 := by
    simpa only [φ, Pi.mul_apply, Pi.zero_apply] using
      congrArg (fun f => f (vertex G j)) hφ₁₂
  have hmul₂₁ (j : V) : zigzagTrivialCoeff k G e₂ (vertex G j) *
      zigzagTrivialCoeff k G e₁ (vertex G j) = 0 := by
    simpa only [φ, Pi.mul_apply, Pi.zero_apply] using
      congrArg (fun f => f (vertex G j)) hφ₂₁
  have hsum_ne {j : V} (hji : j ≠ i) :
      zigzagTrivialCoeff k G e₁ (vertex G j) +
        zigzagTrivialCoeff k G e₂ (vertex G j) = 0 := by
    have h := congrArg (fun f => f (vertex G j)) hφsum
    simpa only [Pi.add_apply, φ, zigzagVertexIdempotent,
      zigzagTrivialCoeff_vertexIdempotent, ite_eq_right hji.symm] using h
  have hsumi : zigzagTrivialCoeff k G e₁ (vertex G i) +
      zigzagTrivialCoeff k G e₂ (vertex G i) = 1 := by
    have h := congrArg (fun f => f (vertex G i)) hφsum
    simpa [φ, zigzagVertexIdempotent] using h
  have hi : zigzagTrivialCoeff k G e₁ (vertex G i) = 0 ∨
      zigzagTrivialCoeff k G e₂ (vertex G i) = 0 :=
    (isPrimitiveIdempotent_one (A := k)).eq_zero_or_eq_zero_of_add
      (hvalue₁ i) (hvalue₂ i) (hmul₁₂ i) (hmul₂₁ i) hsumi
  rcases hi with hi₁ | hi₂
  · left
    apply eq_zero_of_isIdempotentElem_of_zigzagTrivialCoeff_eq_zero k G hns he₁
    funext v
    obtain ⟨j, rfl⟩ := (vertexEquiv G).surjective v
    simp only [vertexEquiv_apply, Pi.zero_apply]
    rcases eq_or_ne j i with rfl | hji
    · exact hi₁
    · exact eq_zero_of_isIdempotentElem_of_add_eq_zero_of_mul_eq_zero (k := k)
        (hvalue₁ j) (hsum_ne hji) (hmul₁₂ j)
  · right
    apply eq_zero_of_isIdempotentElem_of_zigzagTrivialCoeff_eq_zero k G hns he₂
    funext v
    obtain ⟨j, rfl⟩ := (vertexEquiv G).surjective v
    simp only [vertexEquiv_apply, Pi.zero_apply]
    rcases eq_or_ne j i with rfl | hji
    · exact hi₂
    · exact eq_zero_of_isIdempotentElem_of_add_eq_zero_of_mul_eq_zero (k := k)
        (hvalue₂ j) (by simpa only [add_comm] using hsum_ne hji) (hmul₂₁ j)

/-- The vertex projective `Z e_i` is indecomposable as a left module over the zigzag relation
quotient. -/
theorem isIndecomposableModule_zigzagProjective
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    IsIndecomposableModule (nonisolatedZigzagQuotient k G) (zigzagProjective k G i) :=
  (isPrimitiveIdempotent_zigzagVertexIdempotent k G hns i).isIndecomposableModule

/-! ### The vertex-projective basis -/

/-- Basis indices for `Z e_i`: its vertex generator, the darts with tail `i`, and its volume
generator. -/
abbrev ZigzagProjectiveBasisIndex (i : V) :=
  Unit ⊕ {d : G.Dart // d.fst = i} ⊕ Unit

/-- The vertex, outgoing-arrow and volume family in `Z e_i`. -/
noncomputable def zigzagProjectiveBasisFun (i : V) :
    ZigzagProjectiveBasisIndex G i → zigzagProjective k G i
  | .inl _ => zigzagProjectiveGenerator k G i
  | .inr (.inl d) =>
      ⟨zigzagMk k G (ofArrow (arrow G d.1.adj)),
        (mem_zigzagProjective_iff k G).2 (by
          simpa only [zigzagVertexIdempotent, d.2] using
            zigzagMk_ofArrow_mul_vertexIdempotent k G d.1)⟩
  | .inr (.inr _) =>
      ⟨zigzagVolume k G i,
        (mem_zigzagProjective_iff k G).2
          (zigzagVolume_mul_zigzagMk_vertexIdempotent k G i)⟩

@[simp]
theorem coe_zigzagProjectiveBasisFun_inl (i : V) (a : Unit) :
    (zigzagProjectiveBasisFun k G i (.inl a) : nonisolatedZigzagQuotient k G) =
      zigzagVertexIdempotent k G i := by
  rw [zigzagProjectiveBasisFun, coe_zigzagProjectiveGenerator]

@[simp]
theorem coe_zigzagProjectiveBasisFun_inr_inl (i : V) (d : {d : G.Dart // d.fst = i}) :
    (zigzagProjectiveBasisFun k G i (.inr (.inl d)) : nonisolatedZigzagQuotient k G) =
      zigzagMk k G (ofArrow (arrow G d.1.adj)) :=
  (rfl)

@[simp]
theorem coe_zigzagProjectiveBasisFun_inr_inr (i : V) (a : Unit) :
    (zigzagProjectiveBasisFun k G i (.inr (.inr a)) : nonisolatedZigzagQuotient k G) =
      zigzagVolume k G i :=
  (rfl)

/-- The projective-basis indices embed in the vertex-arrow-volume basis indices. -/
private def zigzagProjectiveBasisIndexEmbedding (i : V) :
    ZigzagProjectiveBasisIndex G i ↪ ZigzagBasisIndex G where
  toFun
    | .inl _ => .inl i
    | .inr (.inl d) => .inr (.inl d.1)
    | .inr (.inr _) => .inr (.inr i)
  inj' a b h := by
    rcases a with _ | d | _
    · rcases b with _ | e | _
      · rfl
      · cases h
      · cases h
    · rcases b with _ | e | _
      · cases h
      · have hde : d = e := Subtype.ext (Sum.inl.inj (Sum.inr.inj h))
        rw [hde]
      · cases h
    · rcases b with _ | e | _
      · cases h
      · cases h
      · rfl

/-- The vertex, outgoing-arrow and volume family in `Z e_i` is linearly independent. -/
theorem linearIndependent_zigzagProjectiveBasisFun (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    LinearIndependent k (zigzagProjectiveBasisFun k G i) := by
  let val : zigzagProjective k G i →ₗ[k] nonisolatedZigzagQuotient k G :=
    { toFun := fun x => x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearIndependent.of_comp val ?_
  have hfun :
      ⇑val ∘ zigzagProjectiveBasisFun k G i =
        zigzagBasisFun k G ∘ zigzagProjectiveBasisIndexEmbedding G i := by
    funext b
    -- Expose the local inclusion; the public coercion lemmas then identify each basis vector.
    rcases b with _ | d | _
    · change (zigzagProjectiveBasisFun k G i (.inl ()) :
          nonisolatedZigzagQuotient k G) = zigzagBasisFun k G (.inl i)
      rw [coe_zigzagProjectiveBasisFun_inl, zigzagBasisFun_inl]
    · change (zigzagProjectiveBasisFun k G i (.inr (.inl d)) :
          nonisolatedZigzagQuotient k G) = zigzagBasisFun k G (.inr (.inl d.1))
      rw [coe_zigzagProjectiveBasisFun_inr_inl, zigzagBasisFun_inr_inl]
    · change (zigzagProjectiveBasisFun k G i (.inr (.inr ())) :
          nonisolatedZigzagQuotient k G) = zigzagBasisFun k G (.inr (.inr i))
      rw [coe_zigzagProjectiveBasisFun_inr_inr, zigzagBasisFun_inr_inr]
  exact hfun ▸ (linearIndependent_zigzagBasisFun k G hns).comp _
    (zigzagProjectiveBasisIndexEmbedding G i).injective

/-- Multiplying any element of the zigzag quotient by the vertex idempotent `e_i` lands in the
span of the vertex, outgoing-arrow and volume family of `Z e_i`. -/
private theorem mul_zigzagVertexIdempotent_mem_span_range_zigzagProjectiveBasisFun (i : V)
    (x : nonisolatedZigzagQuotient k G) :
    x * zigzagVertexIdempotent k G i ∈
      Submodule.span k (Set.range fun b : ZigzagProjectiveBasisIndex G i =>
        (zigzagProjectiveBasisFun k G i b : nonisolatedZigzagQuotient k G)) := by
  set S := Submodule.span k (Set.range fun b : ZigzagProjectiveBasisIndex G i =>
    (zigzagProjectiveBasisFun k G i b : nonisolatedZigzagQuotient k G))
  have hx : x ∈ Submodule.span k (Set.range (zigzagBasisFun k G)) := by
    rw [span_range_zigzagBasisFun_eq_top]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ =>
    x * zigzagVertexIdempotent k G i ∈ S) ?_ (by simp) ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩
    rcases b with j | d | j
    · rcases eq_or_ne j i with rfl | hji
      · rw [zigzagBasisFun_inl, zigzagMk_vertexIdempotent_mul_self]
        exact Submodule.subset_span
          ⟨.inl (), coe_zigzagProjectiveBasisFun_inl k G j ()⟩
      · rw [zigzagBasisFun_inl,
          zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G hji]
        exact Submodule.zero_mem _
    · rcases eq_or_ne d.fst i with hdi | hdi
      · rw [zigzagBasisFun_inr_inl, ← hdi, zigzagMk_ofArrow_mul_vertexIdempotent]
        exact Submodule.subset_span
          ⟨.inr (.inl ⟨d, hdi⟩),
            coe_zigzagProjectiveBasisFun_inr_inl k G i ⟨d, hdi⟩⟩
      · rw [zigzagBasisFun_inr_inl,
          zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G d hdi.symm]
        exact Submodule.zero_mem _
    · rcases eq_or_ne j i with rfl | hji
      · rw [zigzagBasisFun_inr_inr, zigzagVolume_mul_zigzagMk_vertexIdempotent]
        exact Submodule.subset_span
          ⟨.inr (.inr ()), coe_zigzagProjectiveBasisFun_inr_inr k G j ()⟩
      · rw [zigzagBasisFun_inr_inr]
        have hzero : zigzagVolume k G j * zigzagVertexIdempotent k G i = 0 := by
          simpa only [zigzagVertexIdempotent] using
            zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G hji.symm
        rw [hzero]
        exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    simpa only [add_mul] using Submodule.add_mem S hx hy
  · intro c x _ hx
    simpa only [smul_mul_assoc] using S.smul_mem c hx

/-- The vertex, outgoing-arrow and volume family spans `Z e_i`. -/
theorem span_range_zigzagProjectiveBasisFun_eq_top (i : V) :
    Submodule.span k (Set.range (zigzagProjectiveBasisFun k G i)) = ⊤ := by
  let val : zigzagProjective k G i →ₗ[k] nonisolatedZigzagQuotient k G :=
    { toFun := fun x => x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let S : Submodule k (nonisolatedZigzagQuotient k G) :=
    Submodule.span k (Set.range fun b : ZigzagProjectiveBasisIndex G i =>
      (zigzagProjectiveBasisFun k G i b : nonisolatedZigzagQuotient k G))
  have hS : S = LinearMap.range val := by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨b, rfl⟩
      exact ⟨zigzagProjectiveBasisFun k G i b, rfl⟩
    · rintro _ ⟨x, rfl⟩
      -- Expose the local inclusion so the fixed-point membership criterion applies.
      change (x : nonisolatedZigzagQuotient k G) ∈ S
      rw [← (mem_zigzagProjective_iff k G).mp x.2]
      exact mul_zigzagVertexIdempotent_mem_span_range_zigzagProjectiveBasisFun k G i x
  apply Submodule.map_injective_of_injective (f := val) Subtype.val_injective
  rw [Submodule.map_top, ← hS, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The vertex, outgoing-arrow and volume basis of `Z e_i`. -/
noncomputable def zigzagProjectiveBasis (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    Module.Basis (ZigzagProjectiveBasisIndex G i) k (zigzagProjective k G i) :=
  Module.Basis.mk (linearIndependent_zigzagProjectiveBasisFun k G hns i)
    (span_range_zigzagProjectiveBasisFun_eq_top k G i).ge

@[simp]
theorem zigzagProjectiveBasis_apply (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V)
    (b : ZigzagProjectiveBasisIndex G i) :
    zigzagProjectiveBasis k G hns i b = zigzagProjectiveBasisFun k G i b :=
  Module.Basis.mk_apply _ _ _

/-- The dimension of the vertex projective is two plus the degree of its vertex. -/
theorem finrank_zigzagProjective [Fintype V] [DecidableRel G.Adj]
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    Module.finrank k (zigzagProjective k G i) = 2 + G.degree i := by
  classical
  rw [Module.finrank_eq_card_basis (zigzagProjectiveBasis k G hns i)]
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_subtype, G.dart_fst_fiber_card_eq_degree]
  omega

end TauCeti
