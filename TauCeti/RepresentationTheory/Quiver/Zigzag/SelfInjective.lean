/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.SelfInjective
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

The argument is the general criterion `LinearMap.IsPerfPair.moduleBaer_self`: the trace turns a map
out of a left ideal into a linear functional, which extends to the whole algebra as a vector space
and is then written as pairing against a fixed element, giving the extension Baer's criterion asks
for.

Because the vertex projective `Z e_i` is a retract of the regular module, it inherits injectivity:
over a zigzag algebra the vertex projectives are also the indecomposable injectives. Their
projectivity is `TauCeti.zigzagProjective_projective`, and their indecomposability is
`TauCeti.isIndecomposableModule_zigzagProjective`.

## Main results

* `TauCeti.moduleInjective_zigzagAlgebra`: the public componentwise zigzag algebra of every finite
  simple graph is self-injective.
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

/-! ### The componentwise public algebra -/

/-- The Frobenius pairing on the dual numbers, obtained by taking the infinitesimal coefficient
of a product. -/
private noncomputable def dualNumberTracePairing : LinearMap.BilinForm k (DualNumber k) :=
  { toFun := fun x =>
      { toFun := fun y => x.fst * y.snd + x.snd * y.fst
        map_add' := fun y z => by
          change x.fst * (y.snd + z.snd) + x.snd * (y.fst + z.fst) =
            (x.fst * y.snd + x.snd * y.fst) + (x.fst * z.snd + x.snd * z.fst)
          ring
        map_smul' := fun c y => by
          change x.fst * (c * y.snd) + x.snd * (c * y.fst) =
            c * (x.fst * y.snd + x.snd * y.fst)
          ring }
    map_add' := fun x y => by
      apply LinearMap.ext
      intro z
      change (x.fst + y.fst) * z.snd + (x.snd + y.snd) * z.fst =
        (x.fst * z.snd + x.snd * z.fst) + (y.fst * z.snd + y.snd * z.fst)
      ring
    map_smul' := fun c x => by
      apply LinearMap.ext
      intro y
      change (c * x.fst) * y.snd + (c * x.snd) * y.fst =
        c * (x.fst * y.snd + x.snd * y.fst)
      ring }

private instance dualNumberTracePairing_isPerfPair : (dualNumberTracePairing k).IsPerfPair := by
  have hbij : Function.Bijective (dualNumberTracePairing k) := by
    constructor
    · intro x y h
      apply TrivSqZeroExt.ext
      · have he := LinearMap.congr_fun h DualNumber.eps
        simpa [dualNumberTracePairing] using he
      · have h1 := LinearMap.congr_fun h 1
        simpa [dualNumberTracePairing] using h1
    · intro f
      refine ⟨⟨f DualNumber.eps, f 1⟩, ?_⟩
      apply LinearMap.ext
      intro y
      calc
        dualNumberTracePairing k ⟨f DualNumber.eps, f 1⟩ y =
            y.snd * f DualNumber.eps + y.fst * f 1 := by
          change f DualNumber.eps * y.snd + f 1 * y.fst = _
          ring
        _ = f (y.snd • DualNumber.eps + y.fst • (1 : DualNumber k)) := by
          rw [map_add, map_smul, map_smul]
          ring
        _ = f y := by
          congr 1
          apply TrivSqZeroExt.ext <;> simp
  refine ⟨hbij, ?_⟩
  have hflip : (dualNumberTracePairing k).flip = dualNumberTracePairing k := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change y.fst * x.snd + y.snd * x.fst = x.fst * y.snd + x.snd * y.fst
    ring
  change Function.Bijective ⇑((dualNumberTracePairing k).flip)
  rw [hflip]
  exact hbij

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
    change zigzagTracePairing k C.toSimpleGraph hns (e (x * y)) (e z) =
      zigzagTracePairing k C.toSimpleGraph hns (e x) (e (y * z))
    rw [show e (x * y) = e x * e y from e.map_mul x y,
      show e (y * z) = e y * e z from e.map_mul y z]
    exact zigzagTracePairing_mul_assoc k C.toSimpleGraph hns _ _ _
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    let e := (zigzagComponentAlgebraEquivULiftDualNumber k G C).trans
      (ULift.algEquiv (R := k) (A := DualNumber k))
    simp only [zigzagComponentPairing, hC]
    change dualNumberTracePairing k (e (x * y)) (e z) =
      dualNumberTracePairing k (e x) (e (y * z))
    rw [show e (x * y) = e x * e y from e.map_mul x y,
      show e (y * z) = e y * e z from e.map_mul y z]
    change (e x * e y).fst * (e z).snd + (e x * e y).snd * (e z).fst =
      (e x).fst * (e y * e z).snd + (e x).snd * (e y * e z).fst
    simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul]
    ring

/-- The direct-sum Frobenius pairing on the public componentwise zigzag algebra. -/
private noncomputable def zigzagAlgebraPairing :
    LinearMap.BilinForm k (zigzagAlgebra k G) := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
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

open Classical in
private theorem zigzagAlgebraPairing_single_right (x : zigzagAlgebra k G)
    (C : G.ConnectedComponent) (z : zigzagComponentAlgebra k G C) :
    zigzagAlgebraPairing k G x (zigzagAlgebraMk k G (Pi.single C z)) =
      zigzagComponentPairing k G C (zigzagComponentProjection k G C x) z := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  rw [zigzagAlgebraPairing]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ D, zigzagComponentPairing k G D (zigzagComponentProjection k G D x)
    (zigzagComponentProjection k G D (zigzagAlgebraMk k G (Pi.single C z)))) = _
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
  let _ := Fintype.ofFinite G.ConnectedComponent
  rw [zigzagAlgebraPairing]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ D, zigzagComponentPairing k G D
    (zigzagComponentProjection k G D (zigzagAlgebraMk k G (Pi.single C z)))
    (zigzagComponentProjection k G D x)) = _
  simp_rw [zigzagComponentProjection_zigzagAlgebraMk]
  have hsum := LinearMap.lsum_piSingle k (fun D : G.ConnectedComponent =>
    zigzagComponentAlgebra k G D) k
    (fun D => (zigzagComponentPairing k G D).flip
      (zigzagComponentProjection k G D x)) C z
  rw [LinearMap.lsum_apply] at hsum
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] at hsum
  change (∑ D, zigzagComponentPairing k G D
    ((Pi.single C z : ∀ E, zigzagComponentAlgebra k G E) D)
    (zigzagComponentProjection k G D x)) =
      zigzagComponentPairing k G C z (zigzagComponentProjection k G C x) at hsum
  exact hsum

private instance zigzagAlgebraPairing_isPerfPair : (zigzagAlgebraPairing k G).IsPerfPair := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
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

/-- **The public zigzag algebra of every finite simple graph is self-injective.** Singleton
components contribute dual-number factors, while every nontrivial component uses its zigzag trace
pairing; the sum of these component pairings is perfect and associative. -/
theorem moduleInjective_zigzagAlgebra :
    Module.Injective (zigzagAlgebra k G) (zigzagAlgebra k G) := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  apply (zigzagAlgebraPairing_isPerfPair k G).moduleInjective_self
  intro x y z
  rw [zigzagAlgebraPairing]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ C, zigzagComponentPairing k G C
    (zigzagComponentProjection k G C (x * y)) (zigzagComponentProjection k G C z)) =
    ∑ C, zigzagComponentPairing k G C (zigzagComponentProjection k G C x)
      (zigzagComponentProjection k G C (y * z))
  simp_rw [map_mul]
  exact Finset.sum_congr rfl fun C _ => zigzagComponentPairing_mul_assoc k G C _ _ _

/-! ### The nonisolated relation quotient and its vertex projectives -/

variable (hns : ∀ i : V, ∃ j, G.Adj i j)

include hns

/-- **The zigzag algebra is self-injective**, in Baer's form: every linear map from a left ideal to
the regular module is right multiplication by an element of the algebra. -/
theorem moduleBaer_nonisolatedZigzagQuotient :
    Module.Baer (nonisolatedZigzagQuotient k G) (nonisolatedZigzagQuotient k G) :=
  (zigzagTracePairing_isPerfPair k G hns).moduleBaer_self (zigzagTracePairing_mul_assoc k G hns)

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
