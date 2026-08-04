/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: the types and classes occurring in the exported statements. `Subalgebra.centralizer` and
-- `Subalgebra` come from `Mathlib.Algebra.Algebra.Subalgebra.Basic`, the module structure carrying
-- `Module.End (↥B ⊗[K] Aᵐᵒᵖ) (Bimodule B.val)` from `TauCeti.Algebra.CentralSimple.Bimodule`, and
-- the remaining three from the hypotheses `Algebra.IsCentral`, `IsSimpleRing`, `FiniteDimensional`.
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Defs
public import TauCeti.Algebra.CentralSimple.Bimodule
-- Non-public: used only inside proofs. Simplicity of the tensor product, the endomorphism algebra
-- of a module over a simple Artinian ring, and finiteness of a tensor product supply the three
-- inputs of the two theorems, and no exported statement mentions any of them; the Artinian
-- hypothesis of the first is supplied by finite-dimensionality (`IsArtinianRing.of_finite`); the
-- dimension of a tensor product and the finite-dimensionality of an opposite space are the
-- bookkeeping, and the complex numbers appear only in the worked example.
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.Algebra.CentralSimple.TensorProduct
import TauCeti.RingTheory.Semisimple.EndAlgebra

/-!
# The centralizer of a central simple subalgebra

Let `K` be a field, let `A` be a finite-dimensional **simple** `K`-algebra and let `B ⊆ A` be a
**central simple** `K`-subalgebra. The centralizer theorem says that

  `C = C_A(B) = {c : A | c commutes with every element of B}`

is again a simple `K`-algebra, and that its dimension is the complementary one:

  `finrank K B * finrank K C = finrank K A`.

The proof is the module-theoretic one, and it reuses the bimodule of the Skolem-Noether theorem. The
inclusion `B.val : B →ₐ[K] A` makes `A` a module over `R = B ⊗[K] Aᵐᵒᵖ`
(`TauCeti.Bimodule`), with `b ⊗ₜ op a` acting by `x ↦ b * x * a`. Because `B` is central simple and
`Aᵐᵒᵖ` is simple, `R` is a simple ring (`TauCeti.IsSimpleRing.tensorProduct`), finite-dimensional
over `K`. Now an `R`-linear endomorphism of `A` is in particular linear for the right action of `A`,
hence is multiplication on the left by some `c : A`, and its linearity for the left action of `B` is
exactly the statement that `c` commutes with `B`. So

  `C ≃ₐ[K] End_R A`,

and both conclusions are read off the general facts about the endomorphism algebra of a module over
a simple Artinian algebra proved in `TauCeti/RingTheory/Semisimple/EndAlgebra.lean`: such an algebra
is simple, and `finrank K (End_R A) * finrank K R = (finrank K A)²`. Since
`finrank K R = finrank K B * finrank K A`, dividing by `finrank K A` leaves the dimension formula.

## Main results

* `TauCeti.centralizerAlgEquivEnd`: the identification `C_A(B) ≃ₐ[K] End_{B ⊗[K] Aᵐᵒᵖ} A`, by left
  multiplication. It needs no hypothesis beyond `B` being a subalgebra.
* `TauCeti.centralizer_isSimpleRing`: **the centralizer of a central simple subalgebra is simple.**
* `TauCeti.finrank_mul_finrank_centralizer`: **the centralizer theorem**,
  `finrank K B * finrank K C_A(B) = finrank K A`.

## Implementation notes

`TauCeti.centralizerAlgEquivEnd` is stated for an arbitrary subalgebra `B` of an arbitrary
`K`-algebra `A` over a commutative semiring `K`: neither simplicity nor finite-dimensionality nor
the field structure plays any part in identifying the endomorphism algebra, they enter only when
that algebra is analysed. Keeping the two apart is what makes the identification reusable, for
instance for the double centralizer. The equivalence is characterised on both sides, by
`TauCeti.centralizerAlgEquivEnd_apply` and `TauCeti.centralizerAlgEquivEnd_symm_apply`, and the
algebra homomorphism and bijectivity proof it is assembled from are private to this file.

Centrality is asked of `B` and not of `A`, exactly as in
`TauCeti/Algebra/CentralSimple/SkolemNoether.lean`, and for the same reason: what the proof needs is
that `B ⊗[K] Aᵐᵒᵖ` is simple, which `TauCeti.IsSimpleRing.tensorProduct` gets from `B` central
simple and `A` simple. The roadmap's central simple form is the case `Algebra.IsCentral K A`, which
these statements cover. Centrality of `B` cannot be dropped: for `K = ℝ`, `A = ℂ` and `B = A`, the
centralizer is all of `ℂ`, so `finrank ℝ B * finrank ℝ C = 4 ≠ 2 = finrank ℝ A`; the worked example
at the end of the file records this.

## References

This implements the Layer 5 targets `centralizer_isSimpleRing` and `finrank_mul_finrank_centralizer`
of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12, and P. Gille, T. Szamuely, *Central
Simple Algebras and Galois Cohomology*, Chapter 2.
-/

public section

namespace TauCeti

open Module
open scoped TensorProduct

section Identification

variable {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A] (B : Subalgebra K A)

/-- Left multiplication by an element `c` of the centralizer of `B` in `A`, as an endomorphism of
the `B ⊗[K] Aᵐᵒᵖ`-module `A`.

It is `B ⊗[K] Aᵐᵒᵖ`-linear precisely because `c` commutes with `B`: multiplying by `c` on the left
is unaffected by the right action of `A` for free, and by the left action of `B` exactly when `c`
centralizes `B`. -/
private def centralizerMulLeftEnd (c : Subalgebra.centralizer K (B : Set A)) :
    Module.End (↥B ⊗[K] Aᵐᵒᵖ) (Bimodule B.val) where
  toFun y := Bimodule.of B.val ((c : A) * (Bimodule.of B.val).symm y)
  map_add' y z := by simp [mul_add]
  map_smul' r y := by
    obtain ⟨x, rfl⟩ := (Bimodule.of B.val).surjective y
    -- Left multiplication by `c` commutes with the whole action, checked on pure tensors.
    have key : ∀ r : ↥B ⊗[K] Aᵐᵒᵖ,
        (c : A) * Bimodule.toEnd B.val r x = Bimodule.toEnd B.val r ((c : A) * x) := by
      intro r
      induction r using TensorProduct.induction_on with
      | zero => simp
      | tmul b a =>
          have hc : (c : A) * (b : A) = (b : A) * (c : A) :=
            ((Subalgebra.mem_centralizer_iff K).1 c.2 (b : A) b.2).symm
          simp only [Bimodule.toEnd_tmul_apply, Subalgebra.coe_val, ← mul_assoc, hc]
      | add r s hr hs => simp only [map_add, LinearMap.add_apply, mul_add, hr, hs]
    -- The defining equation of the action turns both sides into `key r`, read through `of`.
    simp only [RingHom.id_apply, Bimodule.smul_def, LinearEquiv.symm_apply_apply]
    exact congrArg (Bimodule.of B.val) (key r)

@[simp]
private theorem centralizerMulLeftEnd_apply (c : Subalgebra.centralizer K (B : Set A)) (x : A) :
    centralizerMulLeftEnd B c (Bimodule.of B.val x) = Bimodule.of B.val ((c : A) * x) := by
  simp [centralizerMulLeftEnd]

/-- Left multiplication, as a `K`-algebra homomorphism from the centralizer of `B` to the
endomorphism algebra of the `B ⊗[K] Aᵐᵒᵖ`-module `A`. -/
private def centralizerAlgHom :
    Subalgebra.centralizer K (B : Set A) →ₐ[K]
      Module.End (↥B ⊗[K] Aᵐᵒᵖ) (Bimodule B.val) where
  toFun := centralizerMulLeftEnd B
  map_one' := by
    ext y
    obtain ⟨x, rfl⟩ := (Bimodule.of B.val).surjective y
    simp
  map_mul' c d := by
    ext y
    obtain ⟨x, rfl⟩ := (Bimodule.of B.val).surjective y
    simp [Module.End.mul_apply, mul_assoc]
  map_zero' := by
    ext y
    obtain ⟨x, rfl⟩ := (Bimodule.of B.val).surjective y
    simp
  map_add' c d := by
    ext y
    obtain ⟨x, rfl⟩ := (Bimodule.of B.val).surjective y
    simp [add_mul]
  commutes' k := by
    ext y
    obtain ⟨x, rfl⟩ := (Bimodule.of B.val).surjective y
    rw [Module.algebraMap_end_apply]
    simpa using congrArg (Bimodule.of B.val) (Algebra.smul_def k x).symm

@[simp]
private theorem centralizerAlgHom_apply (c : Subalgebra.centralizer K (B : Set A)) :
    centralizerAlgHom B c = centralizerMulLeftEnd B c := rfl

/-- **Left multiplication by the centralizer exhausts the `B ⊗[K] Aᵐᵒᵖ`-linear endomorphisms of
`A`, and nothing is lost.** Injectivity is the value at `1`; surjectivity says an endomorphism `φ`
is left multiplication by `c = φ 1`, which centralizes `B` because `φ` is linear for the left
action of `B`. -/
private theorem centralizerAlgHom_bijective : Function.Bijective (centralizerAlgHom B) := by
  refine ⟨fun c d hcd ↦ ?_, fun φ ↦ ?_⟩
  · -- Injectivity: an endomorphism determines its multiplier through its value at `1`.
    refine Subtype.ext ?_
    have h := congrArg (fun φ : Module.End (↥B ⊗[K] Aᵐᵒᵖ) (Bimodule B.val) ↦
      (Bimodule.of B.val).symm (φ (Bimodule.of B.val 1))) hcd
    simpa using h
  · -- Surjectivity: `φ` is left multiplication by `c = φ 1`, which centralizes `B`.
    set c : A := (Bimodule.of B.val).symm (φ (Bimodule.of B.val 1)) with hc
    have hφ1 : φ (Bimodule.of B.val 1) = Bimodule.of B.val c := by rw [hc]; simp
    -- Every element of `A` is `1` moved by the right action, so `φ` is multiplication by `c`.
    have key : ∀ x : A, φ (Bimodule.of B.val x) = Bimodule.of B.val (c * x) := by
      intro x
      have hx : Bimodule.of B.val x
          = ((1 : ↥B) ⊗ₜ MulOpposite.op x : ↥B ⊗[K] Aᵐᵒᵖ) • Bimodule.of B.val 1 := by
        rw [Bimodule.smul_of]; simp
      rw [hx, map_smul, hφ1, Bimodule.smul_of]
      simp
    -- Linearity for the left action of `B` says exactly that `c` centralizes `B`.
    have hcomm : ∀ b ∈ (B : Set A), b * c = c * b := by
      intro b hb
      have hb' : Bimodule.of B.val b
          = ((⟨b, hb⟩ : ↥B) ⊗ₜ (1 : Aᵐᵒᵖ) : ↥B ⊗[K] Aᵐᵒᵖ) • Bimodule.of B.val 1 := by
        rw [Bimodule.smul_of]; simp
      have h := key b
      rw [hb', map_smul, hφ1, Bimodule.smul_of] at h
      simpa using ((Bimodule.of B.val).injective h.symm).symm
    refine ⟨⟨c, (Subalgebra.mem_centralizer_iff K).2 hcomm⟩, ?_⟩
    ext y
    obtain ⟨x, rfl⟩ := (Bimodule.of B.val).surjective y
    simpa using (key x).symm

/-- **The centralizer of a subalgebra `B ⊆ A` is the endomorphism algebra of `A` as a
`B ⊗[K] Aᵐᵒᵖ`-module**, by left multiplication.

No hypothesis on `A` or `B` is needed here; the centralizer theorem below is what happens when the
right-hand side is analysed under the hypotheses that make `B ⊗[K] Aᵐᵒᵖ` simple Artinian. -/
noncomputable def centralizerAlgEquivEnd :
    Subalgebra.centralizer K (B : Set A) ≃ₐ[K]
      Module.End (↥B ⊗[K] Aᵐᵒᵖ) (Bimodule B.val) :=
  AlgEquiv.ofBijective (centralizerAlgHom B) (centralizerAlgHom_bijective B)

/-- The forward direction of `TauCeti.centralizerAlgEquivEnd`: `c` goes to left multiplication
by `c`. -/
@[simp]
theorem centralizerAlgEquivEnd_apply (c : Subalgebra.centralizer K (B : Set A)) (x : A) :
    centralizerAlgEquivEnd B c (Bimodule.of B.val x) = Bimodule.of B.val ((c : A) * x) := by
  simp only [centralizerAlgEquivEnd, AlgEquiv.ofBijective_apply, centralizerAlgHom_apply,
    centralizerMulLeftEnd_apply]

/-- The inverse direction of `TauCeti.centralizerAlgEquivEnd`: an endomorphism is recovered by
evaluating it at `1`. -/
@[simp]
theorem centralizerAlgEquivEnd_symm_apply (φ : Module.End (↥B ⊗[K] Aᵐᵒᵖ) (Bimodule B.val)) :
    ((centralizerAlgEquivEnd B).symm φ : A)
      = (Bimodule.of B.val).symm (φ (Bimodule.of B.val 1)) := by
  conv_rhs => rw [← (centralizerAlgEquivEnd B).apply_symm_apply φ]
  rw [centralizerAlgEquivEnd_apply, LinearEquiv.symm_apply_apply, mul_one]

end Identification

section Centralizer

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [IsSimpleRing A] [FiniteDimensional K A]
  (B : Subalgebra K A) [Algebra.IsCentral K B] [IsSimpleRing B]

/-- **The centralizer of a central simple subalgebra of a simple algebra is a simple ring.** It is
the endomorphism algebra of `A` as a module over the simple Artinian algebra `B ⊗[K] Aᵐᵒᵖ`. -/
theorem centralizer_isSimpleRing :
    IsSimpleRing (Subalgebra.centralizer K (B : Set A)) := by
  have : FiniteDimensional K ↥B :=
    FiniteDimensional.of_injective B.val.toLinearMap Subtype.val_injective
  -- `B ⊗[K] Aᵐᵒᵖ` is simple Artinian, and `A` is finite over it because it is finite over `K`.
  have : IsArtinianRing (↥B ⊗[K] Aᵐᵒᵖ) := IsArtinianRing.of_finite K _
  have : Module.Finite (↥B ⊗[K] Aᵐᵒᵖ) (Bimodule B.val) :=
    Module.Finite.of_restrictScalars_finite K _ _
  exact _root_.IsSimpleRing.of_ringEquiv (centralizerAlgEquivEnd B).symm.toRingEquiv
    (IsSimpleRing.moduleEnd (R := ↥B ⊗[K] Aᵐᵒᵖ) (M := Bimodule B.val))

/-- **The centralizer theorem.** For a central simple `K`-subalgebra `B` of a finite-dimensional
simple `K`-algebra `A`, the dimensions of `B` and of its centralizer are complementary:

  `finrank K B * finrank K C_A(B) = finrank K A`.

The endomorphism algebra of `A` over `R = B ⊗[K] Aᵐᵒᵖ` is the centralizer, and satisfies
`finrank K (End_R A) * finrank K R = (finrank K A)²` with `finrank K R = finrank K B * finrank K A`;
cancelling one factor of `finrank K A`, which is nonzero, gives the formula. -/
theorem finrank_mul_finrank_centralizer :
    finrank K B * finrank K (Subalgebra.centralizer K (B : Set A)) = finrank K A := by
  have : FiniteDimensional K ↥B :=
    FiniteDimensional.of_injective B.val.toLinearMap Subtype.val_injective
  have key := IsSimpleRing.finrank_end_mul_finrank_eq_sq K (R := ↥B ⊗[K] Aᵐᵒᵖ)
    (M := Bimodule B.val)
  rw [(Bimodule.of (B.val)).finrank_eq.symm, Module.finrank_tensorProduct,
    (MulOpposite.opLinearEquiv K (M := A)).finrank_eq.symm,
    ← (centralizerAlgEquivEnd B).toLinearEquiv.finrank_eq] at key
  -- `key : c * (b * a) = a ^ 2`; cancel one factor of `a = finrank K A`.
  have ha : 0 < finrank K A := Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_right ha ?_
  rw [sq] at key
  rw [mul_comm (finrank K B), mul_assoc]
  exact key

end Centralizer

/-! ### Worked example -/

section Example

/-- The centralizer of the whole of `ℂ` in `ℂ` is `ℂ`, since `ℂ` is commutative. -/
private theorem centralizer_top_complex :
    Subalgebra.centralizer ℝ ((⊤ : Subalgebra ℝ ℂ) : Set ℂ) = ⊤ :=
  eq_top_iff.2 fun z _ ↦ (Subalgebra.mem_centralizer_iff ℝ).2 fun w _ ↦ mul_comm w z

/-- The negative control for `TauCeti.finrank_mul_finrank_centralizer`: centrality of the subalgebra
cannot be dropped. Take `K = ℝ` and `A = B = ℂ`, a simple finite-dimensional `ℝ`-algebra which is
**not** central over `ℝ`. Its centralizer is all of `ℂ`, so the two sides of the dimension formula
are `2 * 2` and `2`. -/
example :
    finrank ℝ (⊤ : Subalgebra ℝ ℂ) *
      finrank ℝ (Subalgebra.centralizer ℝ ((⊤ : Subalgebra ℝ ℂ) : Set ℂ)) ≠ finrank ℝ ℂ := by
  have htop : finrank ℝ (⊤ : Subalgebra ℝ ℂ) = 2 := by
    rw [(Subalgebra.topEquiv (R := ℝ) (A := ℂ)).toLinearEquiv.finrank_eq,
      Complex.finrank_real_complex]
  rw [centralizer_top_complex, htop, Complex.finrank_real_complex]
  norm_num

end Example

end TauCeti
