/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Lie.Sl2.Decomposition
import Mathlib.Data.Fin.Rev

/-!
# Symmetry of the weight multiplicities of an `sl₂`-module

Let `(h, e, f)` be an `sl₂` triple acting on a finite-dimensional module. This file proves that
the `μ`- and `-μ`-eigenspaces of the Cartan element `h` have the same dimension. The statement is
made for an arbitrary triple in an arbitrary ambient Lie algebra; only its generated subalgebra acts
in the argument.

The result is the rank-one symmetry needed for Weyl invariance of weight multiplicities. For a root
`α`, restriction to its `sl₂` triple identifies the reflection of a weight `λ` with the opposite
weight on the corresponding `α`-string. Applying the theorem below to every such string gives the
direct rank-one proof required by Layer 2 of the highest-weight roadmap, independently of Weyl's
complete reducibility theorem.

The construction uses `TauCeti.exists_isInternal_isIrreducible` to decompose the module under the
generated `sl₂`. On each irreducible summand,
`TauCeti.basisOfHasPrimitiveVectorWith` is the ladder basis of weights
`n, n - 2, …, -n`. Mathlib's `DirectSum.IsInternal.collectedBasis` joins these into a basis of the
ambient module. Reversing every ladder gives a linear involution that anticommutes with `h`, hence
restricts to an equivalence between the two eigenspaces.

## Main result

* `TauCeti.finrank_eigenspace_toEnd_eq_neg`: the Cartan eigenspaces at `μ` and `-μ` have equal
  dimension.

## References

This is the rank-one input to the "Weyl-invariance of multiplicities, directly from `sl₂`" target
in Layer 2 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

See J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.2.
-/

public section

namespace TauCeti

open LieModule Module

section Generated

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]
variable {h e f : L}

/-- For a triple which generates the ambient Lie algebra, reversing every irreducible ladder
identifies the Cartan eigenspaces of opposite weights. This is kept private because the public
statement below applies to an arbitrary triple by restricting to its generated subalgebra. -/
private theorem nonempty_linearEquiv_eigenspace_neg_of_eq_top (t : IsSl2Triple h e f)
    (htop : t.toLieSubalgebra K = ⊤) (μ : K) :
    Nonempty
      ((toEnd K L M h).eigenspace μ ≃ₗ[K] (toEnd K L M h).eigenspace (-μ)) := by
  classical
  obtain ⟨k, N, hint, hirr⟩ := exists_isInternal_isIrreducible M htop
  have hprimitive : ∀ i, ∃ (m : N i) (n : ℕ), t.HasPrimitiveVectorWith m (n : K) := by
    intro i
    let _ : LieModule.IsIrreducible K L (N i) := hirr i
    let _ : Nontrivial (N i) := LieModule.nontrivial_of_isIrreducible K L (N i)
    exact exists_hasPrimitiveVectorWith (K := K) (N i) t
  choose m n P using hprimitive
  let _ (i : Fin k) :
      LieModule.IsIrreducible K (t.toLieSubalgebra K) (N i) := by
    let _ : LieModule.IsIrreducible K L (N i) := hirr i
    exact isIrreducible_of_eq_top (M := N i) htop
  let b (i : Fin k) : Basis (Fin (n i + 1)) K (N i) := basisOfHasPrimitiveVectorWith (P i)
  let B : Basis (Σ i, Fin (n i + 1)) K M := hint.collectedBasis b
  let σ : Equiv.Perm (Σ i, Fin (n i + 1)) := Equiv.Perm.sigmaCongrRight fun _ ↦ Fin.revPerm
  let r : M ≃ₗ[K] M := B.equiv B σ
  have hweight (i : Fin k) (j : Fin (n i + 1)) :
      ⁅h, B ⟨i, j⟩⁆ = ((n i : K) - 2 * (j : ℕ)) • B ⟨i, j⟩ := by
    have hj := lie_h_basisOfHasPrimitiveVectorWith (P i) j
    simpa only [B, DirectSum.IsInternal.collectedBasis_coe, b, LieSubmodule.coe_bracket,
      LieSubmodule.coe_smul] using congrArg Subtype.val hj
  have hweight_rev (i : Fin k) (j : Fin (n i + 1)) :
      ((n i : K) - 2 * (j.rev : ℕ)) = -((n i : K) - 2 * (j : ℕ)) := by
    have hn : (n i : K) = (j : ℕ) + (j.rev : ℕ) := by
      exact_mod_cast j.add_rev_cast.symm
    rw [hn]
    ring
  have hr_basis (i : Fin k) (j : Fin (n i + 1)) :
      r (B ⟨i, j⟩) = B ⟨i, j.rev⟩ := by
    exact Basis.equiv_apply B ⟨i, j⟩ B σ
  have hanti : ∀ x : M, r ⁅h, x⁆ = -⁅h, r x⁆ := by
    intro x
    have heq :
        (r : M →ₗ[K] M).comp (toEnd K L M h) =
          -(toEnd K L M h).comp (r : M →ₗ[K] M) := by
      apply B.ext
      rintro ⟨i, j⟩
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, toEnd_apply_apply]
      calc
        r ⁅h, B ⟨i, j⟩⁆ = ((n i : K) - 2 * (j : ℕ)) • r (B ⟨i, j⟩) := by
          rw [hweight, map_smul]
        _ = ((n i : K) - 2 * (j : ℕ)) • B ⟨i, j.rev⟩ := by rw [hr_basis]
        _ = -⁅h, B ⟨i, j.rev⟩⁆ := by rw [hweight, hweight_rev, neg_smul, neg_neg]
        _ = -⁅h, r (B ⟨i, j⟩)⁆ := by rw [hr_basis]
    exact DFunLike.congr_fun heq x
  have hr_involutive : Function.Involutive r := by
    intro x
    have hr_symm : r.symm = r := by simp [r, σ]
    simpa only [hr_symm] using r.symm_apply_apply x
  have hr_mem {a : K} {x : M} (hx : x ∈ (toEnd K L M h).eigenspace a) :
      r x ∈ (toEnd K L M h).eigenspace (-a) := by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    simp only [toEnd_apply_apply] at hx ⊢
    have ha := hanti x
    rw [hx, map_smul] at ha
    simpa only [neg_smul, neg_neg] using (congrArg Neg.neg ha).symm
  let rμ : (toEnd K L M h).eigenspace μ →ₗ[K]
      (toEnd K L M h).eigenspace (-μ) := {
    toFun x := ⟨r x, hr_mem x.2⟩
    map_add' x y := Subtype.ext (r.map_add x y)
    map_smul' c x := Subtype.ext (r.map_smul c x) }
  refine ⟨LinearEquiv.ofBijective rμ ⟨?_, ?_⟩⟩
  · intro x y hxy
    apply Subtype.ext
    change (⟨r x, hr_mem x.2⟩ : (toEnd K L M h).eigenspace (-μ)) =
      ⟨r y, hr_mem y.2⟩ at hxy
    have hxy' := congrArg
      (fun z : (toEnd K L M h).eigenspace (-μ) ↦ r.symm (z : M)) hxy
    simpa only [r.symm_apply_apply] using hxy'
  · intro y
    let x : (toEnd K L M h).eigenspace μ :=
      ⟨r y, by simpa only [neg_neg] using hr_mem y.2⟩
    exact ⟨x, Subtype.ext (hr_involutive y)⟩

end Generated

section Arbitrary

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]
variable {h e f : L}

/-- **The weight multiplicities of a finite-dimensional `sl₂`-module are symmetric.** For the
Cartan element `h` of any `sl₂` triple, the eigenspaces of weights `μ` and `-μ` have the same
dimension.

Only the Lie subalgebra generated by the triple is used. Thus the result applies directly to the
triple attached to a root inside a larger semisimple Lie algebra, which is the rank-one input for
Weyl invariance of the ambient module's weight multiplicities. -/
theorem finrank_eigenspace_toEnd_eq_neg (t : IsSl2Triple h e f) (μ : K) :
    finrank K ((toEnd K L M h).eigenspace μ) =
      finrank K ((toEnd K L M h).eigenspace (-μ)) := by
  let h' : t.toLieSubalgebra K := ⟨h, t.h_mem_toLieSubalgebra⟩
  have htoEnd : toEnd K (t.toLieSubalgebra K) M h' = toEnd K L M h := by
    ext x
    rfl
  obtain ⟨φ⟩ := nonempty_linearEquiv_eigenspace_neg_of_eq_top (M := M) t.restrict
    t.restrict_toLieSubalgebra_eq_top μ
  rw [htoEnd] at φ
  exact φ.finrank_eq

end Arbitrary

end TauCeti
