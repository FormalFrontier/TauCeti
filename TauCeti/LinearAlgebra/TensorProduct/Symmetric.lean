/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.Trace.Square

/-!
# Symmetric and antisymmetric tensors in a tensor square

The flip `x ⊗ y ↦ y ⊗ x` is an involution of `M ⊗[R] M`, and the tensors it fixes and the tensors
it negates cut the tensor square into the **symmetric tensors** `TauCeti.symmetricTensors` and the
**antisymmetric tensors** `TauCeti.antisymmetricTensors`. When `2` is invertible they are
complementary, so the tensor square is their internal direct sum; the two submodules are the
concrete models of `Sym²M` and `⋀²M`
*inside* `M ⊗[R] M`, which is what a construction carrying extra structure on the tensor square —
a topology, say — needs, the quotient and subobject constructions `Sym[R]^2 M` and `⋀[R]^2 M`
living outside it.

The point of the file is the trace identity `TauCeti.trace_map_self_comp_comm`: composing
`f ⊗ f` with the flip has trace `tr (f ∘ f)`, because on a basis the diagonal entry of the
composite at `eᵢ ⊗ eⱼ` is `aᵢⱼ aⱼᵢ`, and summing those is
`TauCeti.trace_eq_trace_comp_self_of_toMatrix_diag`, the step shared with the `Fin 2`-indexed
tensor square of `TauCeti/RepresentationTheory/Tensor/Square.lean`. Splitting that trace along the
symmetric and the antisymmetric tensors, where the flip is `+1` and `-1`, gives
`TauCeti.trace_symmetricTensorsRestrict_sub_trace_antisymmetricTensorsRestrict`: the traces of
`f ⊗ f` on the symmetric and on the antisymmetric tensors differ by `tr (f ∘ f)`. That is the
character identity `χ_{Sym²}(g) - χ_{⋀²}(g) = χ(g²)` behind the Frobenius-Schur indicator, read on
the tensor square rather than on the symmetric and exterior powers.

## Main definitions

* `TauCeti.symmetricTensors`: the tensors of `M ⊗[R] M` fixed by the flip.
* `TauCeti.antisymmetricTensors`: the `-1`-eigenspace of the flip.

## Main results

* `TauCeti.isCompl_symmetricTensors_antisymmetricTensors` and
  `TauCeti.isInternal_symmetricTensors_antisymmetricTensors`: with `2` invertible the two
  submodules are complementary, hence an internal direct sum decomposition of the tensor square.
* `TauCeti.trace_map_self_comp_comm`: `tr ((f ⊗ f) ∘ flip) = tr (f ∘ f)`.
* `TauCeti.trace_symmetricTensorsRestrict_sub_trace_antisymmetricTensorsRestrict`: the traces of
  `f ⊗ f` on the symmetric and on the antisymmetric tensors differ by `tr (f ∘ f)`.

## Implementation notes

Neither submodule is a fresh kernel: the symmetric tensors are `LinearMap.eqLocus` of the flip
against the identity and the antisymmetric tensors are `Module.End.eigenspace` of the flip, so
Mathlib's API applies to both unchanged. The membership lemmas below are the only interface the
rest of the development uses, and they present the two submodules symmetrically.

The asymmetry between the two constructions is a matter of scalars, and it is deliberate.
`Module.End.eigenspace` subtracts a scalar from an endomorphism, so it is stated over
`[CommRing R] [AddCommGroup M]`; negation is genuinely needed for the antisymmetric tensors — the
eigenvalue is `-1` — but not for the symmetric ones, and `LinearMap.eqLocus` asks only for
`[CommSemiring R] [AddCommMonoid M]`. So the symmetric half of the API, up to the restriction of
`f ⊗ f`, is available over a commutative semiring, and only the antisymmetric half and the
splitting theorems need a ring. The trace identity uses neither and is stated over
`[CommSemiring K] [AddCommMonoid M]`.
-/

public section

namespace TauCeti

open scoped TensorProduct

section Symmetric

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- **The symmetric tensors** of `M ⊗[R] M`: the tensors the flip `x ⊗ y ↦ y ⊗ x` fixes. -/
def symmetricTensors : Submodule R (M ⊗[R] M) :=
  LinearMap.eqLocus (TensorProduct.comm R M M).toLinearMap LinearMap.id

variable {R M}

/-- A tensor is symmetric exactly when the flip fixes it. -/
@[simp]
theorem mem_symmetricTensors {x : M ⊗[R] M} :
    x ∈ symmetricTensors R M ↔ TensorProduct.comm R M M x = x := by
  rw [symmetricTensors, LinearMap.mem_eqLocus]
  exact Iff.rfl

/-- `f ⊗ f` preserves the symmetric tensors, because it commutes with the flip. -/
theorem map_self_mem_symmetricTensors (f : M →ₗ[R] M) {x : M ⊗[R] M}
    (hx : x ∈ symmetricTensors R M) : TensorProduct.map f f x ∈ symmetricTensors R M := by
  rw [mem_symmetricTensors] at hx ⊢
  rw [← TensorProduct.map_comm, hx]

/-- The restriction of `f ⊗ f` to the symmetric tensors, as an endomorphism. -/
noncomputable def symmetricTensorsRestrict (f : M →ₗ[R] M) :
    symmetricTensors R M →ₗ[R] symmetricTensors R M :=
  (TensorProduct.map f f).restrict fun _ hx ↦ map_self_mem_symmetricTensors f hx

@[simp]
theorem coe_symmetricTensorsRestrict_apply (f : M →ₗ[R] M) (x : symmetricTensors R M) :
    (symmetricTensorsRestrict f x : M ⊗[R] M) = TensorProduct.map f f x :=
  (rfl)

end Symmetric

section Antisymmetric

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- **The antisymmetric tensors** of `M ⊗[R] M`: the `-1`-eigenspace of the flip. -/
def antisymmetricTensors : Submodule R (M ⊗[R] M) :=
  Module.End.eigenspace (TensorProduct.comm R M M).toLinearMap (-1)

variable {R M}

/-- A tensor is antisymmetric exactly when the flip negates it. -/
@[simp]
theorem mem_antisymmetricTensors {x : M ⊗[R] M} :
    x ∈ antisymmetricTensors R M ↔ TensorProduct.comm R M M x = -x := by
  rw [antisymmetricTensors, Module.End.mem_eigenspace_iff, neg_one_smul]
  exact Iff.rfl

/-- `f ⊗ f` preserves the antisymmetric tensors, because it commutes with the flip. -/
theorem map_self_mem_antisymmetricTensors (f : M →ₗ[R] M) {x : M ⊗[R] M}
    (hx : x ∈ antisymmetricTensors R M) : TensorProduct.map f f x ∈ antisymmetricTensors R M := by
  rw [mem_antisymmetricTensors] at hx ⊢
  rw [← TensorProduct.map_comm, hx, map_neg]

/-- The restriction of `f ⊗ f` to the antisymmetric tensors, as an endomorphism. -/
noncomputable def antisymmetricTensorsRestrict (f : M →ₗ[R] M) :
    antisymmetricTensors R M →ₗ[R] antisymmetricTensors R M :=
  (TensorProduct.map f f).restrict fun _ hx ↦ map_self_mem_antisymmetricTensors f hx

@[simp]
theorem coe_antisymmetricTensorsRestrict_apply (f : M →ₗ[R] M) (x : antisymmetricTensors R M) :
    (antisymmetricTensorsRestrict f x : M ⊗[R] M) = TensorProduct.map f f x :=
  (rfl)

variable (R M) in
/-- **The tensor square is the sum of its symmetric and antisymmetric parts**, when `2` is
invertible: a tensor is the sum of `½ (x + flip x)` and `½ (x - flip x)`, and a tensor both
symmetric and antisymmetric is its own negative. -/
theorem isCompl_symmetricTensors_antisymmetricTensors [Invertible (2 : R)] :
    IsCompl (symmetricTensors R M) (antisymmetricTensors R M) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hs ha
    rw [mem_symmetricTensors] at hs
    rw [mem_antisymmetricTensors] at ha
    have h2 : (2 : R) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hs]
      rw [ha, neg_add_cancel]
    calc x = (⅟(2 : R) * 2) • x := by rw [invOf_mul_self, one_smul]
      _ = ⅟(2 : R) • (2 : R) • x := mul_smul _ _ _
      _ = 0 := by rw [h2, smul_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hsum : x = ⅟(2 : R) • (x + TensorProduct.comm R M M x)
        + ⅟(2 : R) • (x - TensorProduct.comm R M M x) := by
      rw [← smul_add]
      have : x + TensorProduct.comm R M M x + (x - TensorProduct.comm R M M x) = (2 : R) • x := by
        rw [two_smul]; abel
      rw [this, smul_smul, invOf_mul_self, one_smul]
    rw [hsum]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · rw [mem_symmetricTensors, map_add, TensorProduct.comm_comm]
      exact add_comm _ _
    · rw [mem_antisymmetricTensors, map_sub, TensorProduct.comm_comm, neg_sub]

variable (R M) in
/-- The symmetric and antisymmetric tensors decompose the tensor square as an internal direct
sum, the form in which traces split along them. -/
theorem isInternal_symmetricTensors_antisymmetricTensors [Invertible (2 : R)] :
    DirectSum.IsInternal
      (fun b : Bool ↦ cond b (symmetricTensors R M) (antisymmetricTensors R M)) := by
  refine (DirectSum.isInternal_submodule_iff_isCompl _ (Bool.noConfusion : (true : Bool) ≠ false)
    ?_).2 (isCompl_symmetricTensors_antisymmetricTensors R M)
  ext b
  cases b <;> simp

end Antisymmetric

section Trace

variable {K M : Type*} [CommSemiring K] [AddCommMonoid M] [Module K M]

/-- **The trace of `f ⊗ f` composed with the flip is the trace of `f ∘ f`.** In a basis the
diagonal entry of the composite at `eᵢ ⊗ eⱼ` is `aᵢⱼ aⱼᵢ`, and summing those over all pairs is the
trace of the square of the matrix of `f`, which is
`TauCeti.trace_eq_trace_comp_self_of_toMatrix_diag`. -/
theorem trace_map_self_comp_comm [Module.Free K M] [Module.Finite K M] (f : M →ₗ[K] M) :
    LinearMap.trace K (M ⊗[K] M)
        (TensorProduct.map f f ∘ₗ (TensorProduct.comm K M M).toLinearMap)
      = LinearMap.trace K M (f ∘ₗ f) := by
  set b := Module.Free.chooseBasis K M
  refine trace_eq_trace_comp_self_of_toMatrix_diag b (b.tensorProduct b) (Equiv.refl _) f _ ?_
  rintro ⟨i, j⟩
  simp [LinearMap.toMatrix_apply, Module.Basis.tensorProduct_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]

end Trace

section TraceSplit

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **The traces of `f ⊗ f` on the symmetric and on the antisymmetric tensors differ by
`tr (f ∘ f)`.** Both traces are read off the same splitting of `M ⊗ M`: composing `f ⊗ f` with the
flip leaves it unchanged on the symmetric part and negates it on the antisymmetric part, so the
trace of that composite — which is `tr (f ∘ f)` — is the difference of the two. -/
theorem trace_symmetricTensorsRestrict_sub_trace_antisymmetricTensorsRestrict
    [Invertible (2 : K)] (f : M →ₗ[K] M) :
    LinearMap.trace K (symmetricTensors K M) (symmetricTensorsRestrict f)
        - LinearMap.trace K (antisymmetricTensors K M) (antisymmetricTensorsRestrict f)
      = LinearMap.trace K M (f ∘ₗ f) := by
  set F := TensorProduct.map f f ∘ₗ (TensorProduct.comm K M M).toLinearMap with hF
  have hmapsPos : ∀ x ∈ symmetricTensors K M, F x ∈ symmetricTensors K M := by
    intro x hx
    rw [hF, LinearMap.comp_apply, LinearEquiv.coe_coe, mem_symmetricTensors.1 hx]
    exact map_self_mem_symmetricTensors f hx
  have hmapsNeg : ∀ x ∈ antisymmetricTensors K M, F x ∈ antisymmetricTensors K M := by
    intro x hx
    rw [hF, LinearMap.comp_apply, LinearEquiv.coe_coe, mem_antisymmetricTensors.1 hx, map_neg]
    exact Submodule.neg_mem _ (map_self_mem_antisymmetricTensors f hx)
  have hmaps : ∀ i : Bool, Set.MapsTo F
      (cond i (symmetricTensors K M) (antisymmetricTensors K M) : Submodule K (M ⊗[K] M))
      (cond i (symmetricTensors K M) (antisymmetricTensors K M) : Submodule K (M ⊗[K] M)) := by
    rintro (_ | _)
    · exact hmapsNeg
    · exact hmapsPos
  -- The two summands of `LinearMap.trace_eq_sum_trace_restrict`, read on the eigenspaces
  -- themselves: the flip is the identity on the symmetric part and negation on the other. Both
  -- restrictions are ascribed to the eigenspace they act on, so that the equations below rewrite
  -- the summands of `htrace` without unfolding the `Bool`-indexed family.
  have hpos : (F.restrict (hmaps true) : symmetricTensors K M →ₗ[K] symmetricTensors K M)
      = symmetricTensorsRestrict f := by
    ext x
    exact congrArg (TensorProduct.map f f) (mem_symmetricTensors.1 x.2)
  have hneg : LinearMap.trace K (antisymmetricTensors K M) (F.restrict (hmaps false))
      = -LinearMap.trace K (antisymmetricTensors K M) (antisymmetricTensorsRestrict f) := by
    have h : (F.restrict (hmaps false) :
        antisymmetricTensors K M →ₗ[K] antisymmetricTensors K M)
          = -antisymmetricTensorsRestrict f := by
      ext x
      exact (congrArg (TensorProduct.map f f) (mem_antisymmetricTensors.1 x.2)).trans
        (map_neg (TensorProduct.map f f) _)
    rw [h]
    exact map_neg (LinearMap.trace K (antisymmetricTensors K M)) _
  have htrace := LinearMap.trace_eq_sum_trace_restrict
    (isInternal_symmetricTensors_antisymmetricTensors K M) hmaps
  rw [Fintype.sum_bool] at htrace
  calc LinearMap.trace K (symmetricTensors K M) (symmetricTensorsRestrict f)
        - LinearMap.trace K (antisymmetricTensors K M) (antisymmetricTensorsRestrict f)
      = LinearMap.trace K (symmetricTensors K M) (F.restrict (hmaps true))
          + LinearMap.trace K (antisymmetricTensors K M) (F.restrict (hmaps false)) := by
        rw [hpos, hneg, ← sub_eq_add_neg]
    _ = LinearMap.trace K (M ⊗[K] M) F := htrace.symm
    _ = LinearMap.trace K M (f ∘ₗ f) := trace_map_self_comp_comm f

end TraceSplit

end TauCeti
