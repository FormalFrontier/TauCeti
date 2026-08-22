/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Symmetric and antisymmetric tensors in a tensor square

The flip `x ⊗ y ↦ y ⊗ x` is an involution of `M ⊗[R] M`, and its two eigenvalues cut the tensor
square into the **symmetric tensors** `TauCeti.symmetricTensors` and the **antisymmetric tensors**
`TauCeti.antisymmetricTensors`. When `2` is invertible they are complementary, so the tensor square
is their internal direct sum; the two submodules are the concrete models of `Sym²M` and `⋀²M`
*inside* `M ⊗[R] M`, which is what a construction carrying extra structure on the tensor square —
a topology, say — needs, the quotient and subobject constructions `Sym[R]^2 M` and `⋀[R]^2 M`
living outside it.

The point of the file is the trace identity `TauCeti.trace_map_self_comp_comm`: composing
`f ⊗ f` with the flip has trace `tr (f ∘ f)`, because on a basis the diagonal entry of the
composite at `eᵢ ⊗ eⱼ` is `aᵢⱼ aⱼᵢ`. Splitting that trace along the eigenspaces of the flip, where
the flip is `+1` and `-1`, gives `TauCeti.trace_restrict_symmetricTensors_sub`: the traces of
`f ⊗ f` on the symmetric and on the antisymmetric tensors differ by `tr (f ∘ f)`. That is the
character identity `χ_{Sym²}(g) - χ_{⋀²}(g) = χ(g²)` behind the Frobenius-Schur indicator, read on
the tensor square rather than on the symmetric and exterior powers.

## Main definitions

* `TauCeti.symmetricTensors`: the `+1`-eigenspace of the flip of `M ⊗[R] M`.
* `TauCeti.antisymmetricTensors`: its `-1`-eigenspace.

## Main results

* `TauCeti.isCompl_symmetricTensors_antisymmetricTensors` and
  `TauCeti.isInternal_symmetricTensors_antisymmetricTensors`: with `2` invertible the two
  submodules are complementary, hence an internal direct sum decomposition of the tensor square.
* `TauCeti.trace_map_self_comp_comm`: `tr ((f ⊗ f) ∘ flip) = tr (f ∘ f)`.
* `TauCeti.trace_restrict_symmetricTensors_sub`: the traces of `f ⊗ f` on the symmetric and on the
  antisymmetric tensors differ by `tr (f ∘ f)`.

## Implementation notes

The two submodules are `Module.End.eigenspace` of the flip, not fresh kernels, so that Mathlib's
eigenspace API applies to them unchanged; the membership lemmas below are the only interface the
rest of the development uses.
-/

public section

namespace TauCeti

open scoped TensorProduct

section Defs

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- **The symmetric tensors** of `M ⊗[R] M`: the `+1`-eigenspace of the flip `x ⊗ y ↦ y ⊗ x`. -/
def symmetricTensors : Submodule R (M ⊗[R] M) :=
  Module.End.eigenspace (TensorProduct.comm R M M).toLinearMap 1

/-- **The antisymmetric tensors** of `M ⊗[R] M`: the `-1`-eigenspace of the flip. -/
def antisymmetricTensors : Submodule R (M ⊗[R] M) :=
  Module.End.eigenspace (TensorProduct.comm R M M).toLinearMap (-1)

variable {R M}

/-- A tensor is symmetric exactly when the flip fixes it. -/
theorem mem_symmetricTensors {x : M ⊗[R] M} :
    x ∈ symmetricTensors R M ↔ TensorProduct.comm R M M x = x := by
  rw [symmetricTensors, Module.End.mem_eigenspace_iff, one_smul]
  exact Iff.rfl

/-- A tensor is antisymmetric exactly when the flip negates it. -/
theorem mem_antisymmetricTensors {x : M ⊗[R] M} :
    x ∈ antisymmetricTensors R M ↔ TensorProduct.comm R M M x = -x := by
  rw [antisymmetricTensors, Module.End.mem_eigenspace_iff, neg_one_smul]
  exact Iff.rfl

/-- `f ⊗ f` preserves the symmetric tensors, because it commutes with the flip. -/
theorem map_self_mem_symmetricTensors (f : M →ₗ[R] M) {x : M ⊗[R] M}
    (hx : x ∈ symmetricTensors R M) : TensorProduct.map f f x ∈ symmetricTensors R M := by
  rw [mem_symmetricTensors] at hx ⊢
  rw [← TensorProduct.map_comm, hx]

/-- `f ⊗ f` preserves the antisymmetric tensors, because it commutes with the flip. -/
theorem map_self_mem_antisymmetricTensors (f : M →ₗ[R] M) {x : M ⊗[R] M}
    (hx : x ∈ antisymmetricTensors R M) : TensorProduct.map f f x ∈ antisymmetricTensors R M := by
  rw [mem_antisymmetricTensors] at hx ⊢
  rw [← TensorProduct.map_comm, hx, map_neg]

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

end Defs

section Trace

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **The trace of `f ⊗ f` composed with the flip is the trace of `f ∘ f`.** In a basis the
diagonal entry of the composite at `eᵢ ⊗ eⱼ` is `aᵢⱼ aⱼᵢ`, and summing those over all pairs is the
trace of the square of the matrix of `f`. -/
theorem trace_map_self_comp_comm (f : M →ₗ[K] M) :
    LinearMap.trace K (M ⊗[K] M)
        (TensorProduct.map f f ∘ₗ (TensorProduct.comm K M M).toLinearMap)
      = LinearMap.trace K M (f ∘ₗ f) := by
  set b := Module.finBasis K M
  set B := b.tensorProduct b with hB
  set A := LinearMap.toMatrix b b f with hA
  have hdiag : ∀ p : Fin (Module.finrank K M) × Fin (Module.finrank K M),
      LinearMap.toMatrix B B
          (TensorProduct.map f f ∘ₗ (TensorProduct.comm K M M).toLinearMap) p p
        = A p.1 p.2 * A p.2 p.1 := by
    rintro ⟨i, j⟩
    rw [LinearMap.toMatrix_apply, hB, Module.Basis.tensorProduct_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, TensorProduct.comm_tmul, TensorProduct.map_tmul,
      Module.Basis.tensorProduct_repr_tmul_apply, hA, LinearMap.toMatrix_apply,
      LinearMap.toMatrix_apply, smul_eq_mul, mul_comm]
  rw [LinearMap.trace_eq_matrix_trace K B, LinearMap.trace_eq_matrix_trace K b,
    LinearMap.toMatrix_comp b b b f f, Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, hdiag, Matrix.mul_apply, ← hA]
  exact Fintype.sum_prod_type _

/-- The restriction of `f ⊗ f` to the symmetric tensors, as an endomorphism. -/
noncomputable def symmetricTensorsRestrict (f : M →ₗ[K] M) :
    symmetricTensors K M →ₗ[K] symmetricTensors K M :=
  (TensorProduct.map f f).restrict fun _ hx ↦ map_self_mem_symmetricTensors f hx

/-- The restriction of `f ⊗ f` to the antisymmetric tensors, as an endomorphism. -/
noncomputable def antisymmetricTensorsRestrict (f : M →ₗ[K] M) :
    antisymmetricTensors K M →ₗ[K] antisymmetricTensors K M :=
  (TensorProduct.map f f).restrict fun _ hx ↦ map_self_mem_antisymmetricTensors f hx

omit [FiniteDimensional K M] in
@[simp]
theorem coe_symmetricTensorsRestrict_apply (f : M →ₗ[K] M) (x : symmetricTensors K M) :
    (symmetricTensorsRestrict f x : M ⊗[K] M) = TensorProduct.map f f x :=
  (rfl)

omit [FiniteDimensional K M] in
@[simp]
theorem coe_antisymmetricTensorsRestrict_apply (f : M →ₗ[K] M) (x : antisymmetricTensors K M) :
    (antisymmetricTensorsRestrict f x : M ⊗[K] M) = TensorProduct.map f f x :=
  (rfl)

/-- **The traces of `f ⊗ f` on the symmetric and on the antisymmetric tensors differ by
`tr (f ∘ f)`.** Both traces are read off the same splitting of `M ⊗ M`: composing `f ⊗ f` with the
flip leaves it unchanged on the symmetric part and negates it on the antisymmetric part, so the
trace of that composite — which is `tr (f ∘ f)` — is the difference of the two. -/
theorem trace_restrict_symmetricTensors_sub [Invertible (2 : K)] (f : M →ₗ[K] M) :
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
  have htrace := LinearMap.trace_eq_sum_trace_restrict
    (isInternal_symmetricTensors_antisymmetricTensors K M) hmaps
  rw [trace_map_self_comp_comm f, Fintype.sum_bool] at htrace
  have hpos : F.restrict hmapsPos = symmetricTensorsRestrict f := by
    ext x
    exact congrArg (TensorProduct.map f f) (mem_symmetricTensors.1 x.2)
  have hneg : F.restrict hmapsNeg = -antisymmetricTensorsRestrict f := by
    ext x
    change TensorProduct.map f f (TensorProduct.comm K M M (x : M ⊗[K] M))
      = -TensorProduct.map f f (x : M ⊗[K] M)
    rw [mem_antisymmetricTensors.1 x.2, map_neg]
  rw [htrace]
  change LinearMap.trace K (symmetricTensors K M) (symmetricTensorsRestrict f)
      - LinearMap.trace K (antisymmetricTensors K M) (antisymmetricTensorsRestrict f)
    = LinearMap.trace K (symmetricTensors K M) (F.restrict hmapsPos)
      + LinearMap.trace K (antisymmetricTensors K M) (F.restrict hmapsNeg)
  rw [hpos, hneg, sub_eq_add_neg]
  congr 1
  exact (map_neg (LinearMap.trace K (antisymmetricTensors K M)) _).symm

end Trace

end TauCeti
