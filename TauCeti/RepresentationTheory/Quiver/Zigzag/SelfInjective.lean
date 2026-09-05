/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.SelfInjective
public import TauCeti.Algebra.DualNumber.Trace
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Dimension
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Trace

/-!
# The zigzag algebra is self-injective

The public zigzag algebra of every finite simple graph is a symmetric Frobenius algebra, and hence
is **self-injective**. On a nontrivial connected component, `TauCeti.zigzagTracePairing` is the
perfect associative pairing whose Gram matrix exchanges an idempotent with a volume class and a
dart with its reverse. A singleton component instead carries the dual numbers, with perfect
pairing given by the infinitesimal coefficient of a product. Summing these pairings over the
connected components proves the result for `TauCeti.zigzagAlgebra`, including disconnected graphs
and isolated vertices.

The argument is the general criterion `Function.Bijective.moduleBaer_self`: the trace turns a map
out of a left ideal into a linear functional, which extends to the whole algebra as a vector space
and is then written as pairing against a fixed element, giving the extension Baer's criterion asks
for.

Because the vertex projective `Z e_i` is a retract of the regular module, it inherits injectivity:
over a zigzag algebra the vertex projectives are also the indecomposable injectives. Their
projectivity is `TauCeti.zigzagProjective_projective`, and their indecomposability is
`TauCeti.isIndecomposableModule_zigzagProjective`.

## Main results

* `TauCeti.zigzagAlgebraPairing`: the symmetric perfect associative pairing on the public zigzag
  algebra.
* `TauCeti.zigzagAlgebraPairing_single_nontrivial` and
  `TauCeti.zigzagAlgebraPairing_single_subsingleton`: on the factor of one connected component that
  pairing is `TauCeti.zigzagTracePairing` respectively `TauCeti.dualNumberTracePairing`.
* `TauCeti.moduleBaer_zigzagAlgebra` and `TauCeti.moduleInjective_zigzagAlgebra`: the public
  componentwise zigzag algebra of every finite simple graph is self-injective.
* `TauCeti.moduleInjective_nonisolatedZigzagQuotient`: the relation-quotient presentation for a
  graph without isolated vertices is self-injective.
* `TauCeti.moduleInjective_zigzagProjective`: each vertex projective `Z e_i` is an injective
  module.

## References

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

universe u w

open SimpleGraph

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- The finite indexing type used internally for componentwise pairings. -/
noncomputable local instance zigzagConnectedComponentFintype : Fintype G.ConnectedComponent :=
  Fintype.ofFinite _

/-! ### The componentwise public algebra -/

/-- The perfect Frobenius pairing on one component of the public zigzag algebra. -/
private noncomputable def zigzagComponentPairing (C : G.ConnectedComponent) :
    LinearMap.BilinForm k (zigzagComponentAlgebra k G C) := by
  classical
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    let hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i =>
      exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
    exact (zigzagTracePairing k C.toSimpleGraph hns).compl₁₂
      (zigzagComponentAlgebraEquivNonisolated k G C).toLinearEquiv
      (zigzagComponentAlgebraEquivNonisolated k G C).toLinearEquiv
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    let e := (zigzagComponentAlgebraEquivULiftDualNumber k G C).trans
      (ULift.algEquiv (R := k) (A := DualNumber k))
    exact (dualNumberTracePairing k).compl₁₂ e.toLinearEquiv e.toLinearEquiv

private instance zigzagComponentPairing_isPerfPair (C : G.ConnectedComponent) :
    (zigzagComponentPairing k G C).IsPerfPair := by
  classical
  unfold zigzagComponentPairing
  split <;> infer_instance

private theorem zigzagComponentPairing_apply_nontrivial (C : G.ConnectedComponent)
    [Nontrivial C] (hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j)
    (x y : zigzagComponentAlgebra k G C) :
    zigzagComponentPairing k G C x y =
      zigzagTracePairing k C.toSimpleGraph hns
        (zigzagComponentAlgebraEquivNonisolated k G C x)
        (zigzagComponentAlgebraEquivNonisolated k G C y) := by
  classical
  have hC : Nontrivial C := inferInstance
  simp only [zigzagComponentPairing, hC]
  rfl

private theorem zigzagComponentPairing_apply_subsingleton (C : G.ConnectedComponent)
    [Subsingleton C] (x y : zigzagComponentAlgebra k G C) :
    zigzagComponentPairing k G C x y =
      dualNumberTracePairing k (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down
        (zigzagComponentAlgebraEquivULiftDualNumber k G C y).down := by
  classical
  have hC : ¬ Nontrivial C := fun h => (not_subsingleton_iff_nontrivial.mpr h) inferInstance
  simp only [zigzagComponentPairing, hC]
  rfl

private theorem zigzagComponentPairing_mul_assoc (C : G.ConnectedComponent)
    (x y z : zigzagComponentAlgebra k G C) :
    zigzagComponentPairing k G C (x * y) z = zigzagComponentPairing k G C x (y * z) := by
  classical
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    let hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i =>
      exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
    let e := zigzagComponentAlgebraEquivNonisolated k G C
    simp only [zigzagComponentPairing, hC]
    -- Evaluating the transported pairing is definitionally `compl₁₂_apply`; unfolding the
    -- preceding `by_cases` does not expose that equation to `simp` in this dependent family.
    change zigzagTracePairing k C.toSimpleGraph hns (e (x * y)) (e z) =
      zigzagTracePairing k C.toSimpleGraph hns (e x) (e (y * z))
    -- `e.map_mul` is stated through `e.toMulEquiv`, whereas this goal contains the `AlgEquiv`
    -- function coercion, so `rw [e.map_mul x y]` cannot find the syntactically different term.
    rw [show e (x * y) = e x * e y from e.map_mul x y,
      show e (y * z) = e y * e z from e.map_mul y z]
    exact zigzagTracePairing_mul_assoc k C.toSimpleGraph hns _ _ _
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    let e := (zigzagComponentAlgebraEquivULiftDualNumber k G C).trans
      (ULift.algEquiv (R := k) (A := DualNumber k))
    simp only [zigzagComponentPairing, hC]
    -- As above, this records the definitional evaluation of the transported pairing after the
    -- singleton branch of the dependent `by_cases` has been selected.
    change dualNumberTracePairing k (e (x * y)) (e z) =
      dualNumberTracePairing k (e x) (e (y * z))
    -- The typed equalities bridge the same `e.toMulEquiv` versus `AlgEquiv` coercion mismatch.
    rw [show e (x * y) = e x * e y from e.map_mul x y,
      show e (y * z) = e y * e z from e.map_mul y z]
    exact dualNumberTracePairing_mul_assoc k _ _ _

private theorem zigzagComponentPairing_isSymm (C : G.ConnectedComponent) :
    (zigzagComponentPairing k G C).IsSymm := by
  classical
  constructor
  intro x y
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    let hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j := fun i =>
      exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
    let e := zigzagComponentAlgebraEquivNonisolated k G C
    simp only [zigzagComponentPairing, hC]
    -- Selecting this dependent branch leaves evaluation of the transported pairing definitional.
    change zigzagTracePairing k C.toSimpleGraph hns (e x) (e y) =
      zigzagTracePairing k C.toSimpleGraph hns (e y) (e x)
    exact (zigzagTracePairing_isSymm k C.toSimpleGraph hns).eq _ _
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    let e := (zigzagComponentAlgebraEquivULiftDualNumber k G C).trans
      (ULift.algEquiv (R := k) (A := DualNumber k))
    simp only [zigzagComponentPairing, hC]
    -- The singleton branch likewise reduces the transported pairing only by definitional equality.
    change dualNumberTracePairing k (e x) (e y) = dualNumberTracePairing k (e y) (e x)
    exact (dualNumberTracePairing_isSymm k).eq _ _

/-- The direct-sum Frobenius pairing on the public componentwise zigzag algebra. -/
noncomputable def zigzagAlgebraPairing :
    LinearMap.BilinForm k (zigzagAlgebra k G) := by
  classical
  exact
    { toFun := fun x =>
        ∑ C, (zigzagComponentPairing k G C (zigzagComponentProjection k G C x)).comp
          (zigzagComponentProjection k G C).toLinearMap
      map_add' := fun x y => by
        apply LinearMap.ext
        intro z
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.add_apply]
        simp only [map_add]
        exact Finset.sum_add_distrib
      map_smul' := fun c x => by
        apply LinearMap.ext
        intro z
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply]
        simp only [map_smul, RingHom.id_apply]
        simp only [LinearMap.smul_apply]
        rw [Finset.smul_sum] }

private theorem zigzagAlgebraPairing_apply_components (x y : zigzagAlgebra k G) :
    zigzagAlgebraPairing k G x y = ∑ C, zigzagComponentPairing k G C
      (zigzagComponentProjection k G C x) (zigzagComponentProjection k G C y) := by
  classical
  rw [zigzagAlgebraPairing]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]

open Classical in
private theorem zigzagAlgebraPairing_single_right (x : zigzagAlgebra k G)
    (C : G.ConnectedComponent) (z : zigzagComponentAlgebra k G C) :
    zigzagAlgebraPairing k G x (zigzagAlgebraMk k G (Pi.single C z)) =
      zigzagComponentPairing k G C (zigzagComponentProjection k G C x) z := by
  classical
  rw [zigzagAlgebraPairing_apply_components]
  simp_rw [zigzagComponentProjection_zigzagAlgebraMk]
  simpa only [LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply] using
      LinearMap.lsum_piSingle k (fun D : G.ConnectedComponent =>
        zigzagComponentAlgebra k G D) k
        (fun D => zigzagComponentPairing k G D (zigzagComponentProjection k G D x)) C z

open Classical in
private theorem zigzagAlgebraPairing_single_left (x : zigzagAlgebra k G)
    (C : G.ConnectedComponent) (z : zigzagComponentAlgebra k G C) :
    zigzagAlgebraPairing k G (zigzagAlgebraMk k G (Pi.single C z)) x =
      zigzagComponentPairing k G C z (zigzagComponentProjection k G C x) := by
  classical
  rw [zigzagAlgebraPairing_apply_components]
  simp_rw [zigzagComponentProjection_zigzagAlgebraMk]
  have hsum := LinearMap.lsum_piSingle k (fun D : G.ConnectedComponent =>
    zigzagComponentAlgebra k G D) k
    (fun D => (zigzagComponentPairing k G D).flip
      (zigzagComponentProjection k G D x)) C z
  rw [LinearMap.lsum_apply] at hsum
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] at hsum
  -- The dependent component type is intentionally opaque, so `flip_apply` cannot transport the
  -- heterogeneous `Pi.single` sum by simplification; this conversion states that common type.
  change (∑ D, zigzagComponentPairing k G D
    ((Pi.single C z : ∀ E, zigzagComponentAlgebra k G E) D)
    (zigzagComponentProjection k G D x)) =
      zigzagComponentPairing k G C z (zigzagComponentProjection k G C x) at hsum
  exact hsum

open Classical in
/-- The direct-sum pairing is the sum of its restrictions to the embedded component factors. -/
theorem zigzagAlgebraPairing_apply (x y : zigzagAlgebra k G) :
    zigzagAlgebraPairing k G x y = ∑ C, zigzagAlgebraPairing k G
      (zigzagAlgebraMk k G (Pi.single C (zigzagComponentProjection k G C x)))
      (zigzagAlgebraMk k G (Pi.single C (zigzagComponentProjection k G C y))) := by
  classical
  rw [zigzagAlgebraPairing_apply_components]
  apply Finset.sum_congr rfl
  intro C _
  rw [zigzagAlgebraPairing_single_left, zigzagComponentProjection_zigzagAlgebraMk]
  simp

open Classical in
/-- On a nontrivial component the direct-sum pairing restricted to the embedded factor is the
zigzag trace pairing of that component, transported along
`TauCeti.zigzagComponentAlgebraEquivNonisolated`. -/
theorem zigzagAlgebraPairing_single_nontrivial (C : G.ConnectedComponent) [Nontrivial C]
    (hns : ∀ i : C, ∃ j, C.toSimpleGraph.Adj i j) (x y : zigzagComponentAlgebra k G C) :
    zigzagAlgebraPairing k G (zigzagAlgebraMk k G (Pi.single C x))
        (zigzagAlgebraMk k G (Pi.single C y)) =
      zigzagTracePairing k C.toSimpleGraph hns
        (zigzagComponentAlgebraEquivNonisolated k G C x)
        (zigzagComponentAlgebraEquivNonisolated k G C y) := by
  classical
  rw [zigzagAlgebraPairing_single_left, zigzagComponentProjection_zigzagAlgebraMk,
    Pi.single_eq_same, zigzagComponentPairing_apply_nontrivial k G C hns]

open Classical in
/-- On a singleton component the direct-sum pairing restricted to the embedded factor is the
dual-number trace pairing, transported along
`TauCeti.zigzagComponentAlgebraEquivULiftDualNumber`. -/
theorem zigzagAlgebraPairing_single_subsingleton (C : G.ConnectedComponent) [Subsingleton C]
    (x y : zigzagComponentAlgebra k G C) :
    zigzagAlgebraPairing k G (zigzagAlgebraMk k G (Pi.single C x))
        (zigzagAlgebraMk k G (Pi.single C y)) =
      dualNumberTracePairing k (zigzagComponentAlgebraEquivULiftDualNumber k G C x).down
        (zigzagComponentAlgebraEquivULiftDualNumber k G C y).down := by
  classical
  rw [zigzagAlgebraPairing_single_left, zigzagComponentProjection_zigzagAlgebraMk,
    Pi.single_eq_same, zigzagComponentPairing_apply_subsingleton k G C]

/-- The direct-sum Frobenius pairing on the public zigzag algebra is perfect. -/
instance zigzagAlgebraPairing_isPerfPair : (zigzagAlgebraPairing k G).IsPerfPair := by
  classical
  apply LinearMap.IsPerfPair.of_injective
  · intro x y h
    apply zigzagAlgebra.ext
    intro C
    apply (LinearMap.IsPerfPair.bijective_left (zigzagComponentPairing k G C)).injective
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun h
      (zigzagAlgebraMk k G (Pi.single C z))
    rw [zigzagAlgebraPairing_single_right, zigzagAlgebraPairing_single_right] at hz
    exact hz
  · intro x y h
    apply zigzagAlgebra.ext
    intro C
    apply (LinearMap.IsPerfPair.bijective_right (zigzagComponentPairing k G C)).injective
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun h
      (zigzagAlgebraMk k G (Pi.single C z))
    simp only [LinearMap.flip_apply] at hz
    rw [zigzagAlgebraPairing_single_left, zigzagAlgebraPairing_single_left] at hz
    exact hz

/-- The direct-sum Frobenius pairing on the public zigzag algebra is associative with
multiplication. -/
theorem zigzagAlgebraPairing_mul_assoc (x y z : zigzagAlgebra k G) :
    zigzagAlgebraPairing k G (x * y) z = zigzagAlgebraPairing k G x (y * z) := by
  classical
  rw [zigzagAlgebraPairing_apply_components, zigzagAlgebraPairing_apply_components]
  simp_rw [map_mul]
  exact Finset.sum_congr rfl fun C _ => zigzagComponentPairing_mul_assoc k G C _ _ _

/-- The direct-sum Frobenius pairing on the public zigzag algebra is symmetric. -/
theorem zigzagAlgebraPairing_isSymm : (zigzagAlgebraPairing k G).IsSymm :=
  ⟨fun x y => by
    rw [zigzagAlgebraPairing_apply_components, zigzagAlgebraPairing_apply_components]
    exact Finset.sum_congr rfl fun C _ => (zigzagComponentPairing_isSymm k G C).eq _ _⟩

/-- **The public zigzag algebra of every finite simple graph satisfies Baer's criterion.**
Singleton components contribute dual-number factors, while every nontrivial component uses its
zigzag trace pairing; the sum of these component pairings is perfect and associative. -/
theorem moduleBaer_zigzagAlgebra : Module.Baer (zigzagAlgebra k G) (zigzagAlgebra k G) :=
  (LinearMap.IsPerfPair.bijective_right (zigzagAlgebraPairing k G)).moduleBaer_self
    (zigzagAlgebraPairing_mul_assoc k G)

/-- **The public zigzag algebra of every finite simple graph is self-injective.** -/
theorem moduleInjective_zigzagAlgebra :
    Module.Injective (zigzagAlgebra k G) (zigzagAlgebra k G) :=
  Module.Baer.injective (moduleBaer_zigzagAlgebra k G)

/-! ### The nonisolated relation quotient and its vertex projectives -/

variable (hns : ∀ i : V, ∃ j, G.Adj i j)

include hns

/-- **The zigzag algebra is self-injective**, in Baer's form: every linear map from a left ideal to
the regular module is right multiplication by an element of the algebra. -/
theorem moduleBaer_nonisolatedZigzagQuotient :
    Module.Baer (nonisolatedZigzagQuotient k G) (nonisolatedZigzagQuotient k G) :=
  (LinearMap.IsPerfPair.bijective_right (zigzagTracePairing k G hns)).moduleBaer_self
    (zigzagTracePairing_mul_assoc k G hns)

/-- **The zigzag algebra of a finite simple graph without isolated vertices is self-injective**: its
regular left module is an injective module. This is the module-theoretic content of the symmetric
Frobenius structure carried by the trace pairing. -/
theorem moduleInjective_nonisolatedZigzagQuotient :
    Module.Injective (nonisolatedZigzagQuotient k G) (nonisolatedZigzagQuotient k G) :=
  Module.Baer.injective (moduleBaer_nonisolatedZigzagQuotient k G hns)

/-- **The vertex projectives of a zigzag algebra are injective modules.** The left ideal `Z e_i` is
a retract of the regular module, which is injective. -/
theorem moduleInjective_zigzagProjective (i : V) :
    Module.Injective (nonisolatedZigzagQuotient k G) (zigzagProjective k G i) :=
  Module.Baer.injective
    ((moduleBaer_nonisolatedZigzagQuotient k G hns).of_isIdempotentElem
      (zigzagMk_vertexIdempotent_mul_self k G i) fun _ => mem_zigzagProjective_iff k G)

end TauCeti
