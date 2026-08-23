/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the types and classes occurring in the exported statements. `Subalgebra.centralizer` and
-- `Subalgebra` come from `Mathlib.Algebra.Algebra.Subalgebra.Basic`, the module structure carrying
-- `Module.End (↥B ⊗[K] Aᵐᵒᵖ) (Bimodule B.val)` from `TauCeti.Algebra.CentralSimple.Bimodule`,
-- `TauCeti.Algebra.deg` from `TauCeti.Algebra.CentralSimple.Degree`, and the remaining three from
-- the hypotheses `Algebra.IsCentral`, `IsSimpleRing`, `FiniteDimensional`. The `Degree` import also
-- re-exports `TauCeti.Algebra.CentralSimple.TensorProduct`, and with it
-- `Mathlib.Algebra.Central.Basic` and `Mathlib.RingTheory.SimpleRing.Basic`, which is why none of
-- those three is imported again here.
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Defs
public import TauCeti.Algebra.CentralSimple.Bimodule
public import TauCeti.Algebra.CentralSimple.Degree
-- Non-public: used only inside proofs. The endomorphism algebra of a module over a simple Artinian
-- ring and finiteness of a tensor product supply two of the three inputs of the first two theorems
-- (the third, simplicity of a tensor product, comes with the `Degree` import above), and no
-- exported statement mentions any of them; the Artinian hypothesis of the first is supplied by
-- finite-dimensionality (`IsArtinianRing.of_finite`); the dimension of a tensor product and the
-- finite-dimensionality of an opposite space are the bookkeeping, and the complex numbers appear
-- only in the worked examples. The equality of injectivity and surjectivity in equal finite
-- dimension and the descent of centrality from a tensor product to its factors are the two further
-- tools of the tensor decomposition and the double centralizer. The simplicity of a field is what
-- feeds the subfield case of the dimension count.
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Central.TensorProduct
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.Semisimple.EndAlgebra

/-!
# The centralizer of a central simple subalgebra

Let `K` be a field, let `A` be a finite-dimensional **simple** `K`-algebra and let `B ⊆ A` be a
**central simple** `K`-subalgebra. The centralizer theorem says that

  `C = C_A(B) = {c : A | c commutes with every element of B}`

is again a simple `K`-algebra, and that its dimension is the complementary one:

  `finrank K B * finrank K C = finrank K A`.

The dimension formula is sharpened here to a decomposition: multiplication `B ⊗[K] C → A` is an
algebra isomorphism, because its source is simple, so that the map is injective, and the two sides
have the same dimension. When `A` is moreover **central** simple, the decomposition forces `C` to be
central as well, since a tensor product of algebras over a field is central only if both factors
are; so `C` is central simple in turn, the centralizer theorem applies to it, and comparing the two
dimension formulas gives the **double centralizer** `C_A(C) = B`.

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
* `TauCeti.finrank_mul_finrank_centralizer_of_isField`: the same dimension formula for a
  **subfield** of a central simple algebra, where centrality is asked of the ambient algebra
  instead of the subalgebra.
* `TauCeti.tensorCentralizerAlgEquiv`: **the tensor decomposition** `B ⊗[K] C_A(B) ≃ₐ[K] A`, by
  multiplication.
* `TauCeti.centralizer_isCentral`: **the centralizer of a central simple subalgebra of a central
  simple algebra is central**, so that `C_A(B)` is central simple again.
* `TauCeti.centralizer_centralizer`: **the double centralizer theorem**, `C_A(C_A(B)) = B`.
* `TauCeti.deg_mul_deg_centralizer`: the degree form of the dimension formula,
  `deg K B * deg K C_A(B) = deg K A`.

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

Because simplicity of `B ⊗[K] Aᵐᵒᵖ` is all the dimension formula uses, the count itself is proved
once and separately, in
`TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite`;
`TauCeti.finrank_mul_finrank_centralizer` is the case of it where that simplicity comes from `B`
central simple and `A` simple, and `TauCeti.finrank_mul_finrank_centralizer_of_isField` the case
where it comes instead from `B` a subfield of a central simple `A`.

That last statement asks for `IsField ↥L` and not for the weaker `IsSimpleRing ↥L`, which is all
its proof uses. The restriction is a scope boundary and not a mathematical one: stated for a merely
simple subalgebra it is the centralizer theorem for a non-central simple subalgebra, which the
Layer 5 bullet of the roadmap referenced below defers — "the general form for a merely simple
subalgebra `B` (center `Z(B) ⊋ K`) ... is a **later** target, not this one" — to be taken up
together with the description of the centralizer's centre. Nothing is lost in generality by it:
the count itself is stated at the level its proof works at, and a caller with a merely simple `L`
can use it directly.

Centrality of `A`, on the other hand, is asked only of the last three statements, and there it
cannot be dropped either: for `K = ℝ`, `A = ℂ` and `B = ⊥`, which is central simple, the centralizer
of `B` is all of `ℂ` and so is its centralizer in turn, which is not `⊥`. The second worked example
records this.

`TauCeti.deg_mul_deg_centralizer` is stated here rather than beside the other degree lemmas in
`TauCeti/Algebra/CentralSimple/Degree.lean`, so that the degree file stays free of the centralizer
machinery: it is a statement about a centralizer, whose only degree input is
`TauCeti.Algebra.deg_tensorProduct`.

## References

This implements the Layer 5 targets `centralizer_isSimpleRing`, `finrank_mul_finrank_centralizer`
and `centralizer_centralizer` of the
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
    -- `φ` is multiplication by `c`: this is the shared bimodule-map API at `f = g = B.val`.
    have key : ∀ x : A, φ (Bimodule.of B.val x) = Bimodule.of B.val (c * x) := fun x => by
      simpa [hc] using Bimodule.apply_of (φ := φ) x
    -- Linearity for the left action of `B` says exactly that `c` centralizes `B`.
    have hcomm : ∀ b ∈ (B : Set A), b * c = c * b := fun b hb => by
      simpa [hc] using
        (Bimodule.symm_apply_one_mul_eq_mul_symm_apply_one (φ := φ) ⟨b, hb⟩).symm
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

/-- An element of a subalgebra commutes with an element of its centralizer; this is the hypothesis
under which `Algebra.TensorProduct.lift` builds `TauCeti.tensorCentralizerAlgHom`. -/
private theorem commute_val_centralizer (b : B) (c : Subalgebra.centralizer K (B : Set A)) :
    Commute (B.val b) ((Subalgebra.centralizer K (B : Set A)).val c) :=
  (Subalgebra.mem_centralizer_iff K).1 c.2 (b : A) b.2

/-- **Multiplication `B ⊗[K] C_A(B) → A`**, as a `K`-algebra homomorphism.

An element of the centralizer commutes with every element of `B` by definition, which is exactly the
hypothesis under which the universal property of the tensor product of algebras turns the two
inclusions into a single homomorphism out of the tensor product. Like
`TauCeti.centralizerAlgEquivEnd` it asks nothing of `A` or `B`; it becomes an isomorphism under the
hypotheses of the centralizer theorem (`TauCeti.tensorCentralizerAlgEquiv`). -/
noncomputable def tensorCentralizerAlgHom :
    ↥B ⊗[K] ↥(Subalgebra.centralizer K (B : Set A)) →ₐ[K] A :=
  Algebra.TensorProduct.lift B.val (Subalgebra.centralizer K (B : Set A)).val
    (commute_val_centralizer B)

@[simp]
theorem tensorCentralizerAlgHom_tmul (b : B) (c : Subalgebra.centralizer K (B : Set A)) :
    tensorCentralizerAlgHom B (b ⊗ₜ c) = (b : A) * (c : A) := by
  unfold tensorCentralizerAlgHom
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

end Identification

section DimensionCount

variable {K A : Type*} [Field K] [Ring A] [Nontrivial A] [Algebra K A] [FiniteDimensional K A]
  (B : Subalgebra K A) [IsSimpleRing (↥B ⊗[K] Aᵐᵒᵖ)]

/-- **The dimension count behind the centralizer theorem**, asking only for what it uses: that `A`
is finite-dimensional and nonzero over the field `K` — so that the factor of `finrank K A` cancelled
at the end is nonzero — and that the ring `R = B ⊗[K] Aᵐᵒᵖ` acting on `A` is simple. Then

  `finrank K B * finrank K C_A(B) = finrank K A`.

Simplicity of `R` is the only algebraic hypothesis on `B` and on `A`, and there is more than one way
to supply it: `TauCeti.finrank_mul_finrank_centralizer` has it from `B` central simple and `A`
simple, while `TauCeti.finrank_mul_finrank_centralizer_of_isField` has it from `B` a subfield and
`A` central simple. -/
theorem finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite :
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

end DimensionCount

section Subfield

-- The scoped instances of `IsMulCommutative` are what turn commutativity of the subfield, which is
-- how `IsField` records it, into the `CommRing` structure `isSimpleRing_iff_isField` asks for.
open scoped IsMulCommutative

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **The dimension of the centralizer of a subfield of a central simple algebra is the
complementary one**:

  `finrank K L * finrank K C_A(L) = finrank K A`.

This is `TauCeti.finrank_mul_finrank_centralizer` with the centrality hypothesis moved from the
subalgebra to the ambient algebra. The shared dimension count is
`TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite`, whose one
algebraic hypothesis — that `L ⊗[K] Aᵐᵒᵖ` be simple —
`TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` supplies here from the simplicity of the
field `L` and the central simplicity of `Aᵐᵒᵖ`; `L` itself is not central over `K` unless it is `K`,
so the orientation used by `TauCeti.finrank_mul_finrank_centralizer` does not apply. -/
theorem finrank_mul_finrank_centralizer_of_isField (L : Subalgebra K A) (hL : IsField ↥L) :
    finrank K ↥L * finrank K ↥(Subalgebra.centralizer K (L : Set A)) = finrank K A := by
  have : IsMulCommutative ↥L := ⟨⟨hL.mul_comm⟩⟩
  have : IsSimpleRing ↥L := (isSimpleRing_iff_isField ↥L).2 hL
  exact finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite L

end Subfield

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

This is the dimension count of
`TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite`, whose one
algebraic hypothesis — simplicity of `B ⊗[K] Aᵐᵒᵖ` — `TauCeti.IsSimpleRing.tensorProduct` supplies
from `B` central simple and `Aᵐᵒᵖ` simple. -/
theorem finrank_mul_finrank_centralizer :
    finrank K B * finrank K (Subalgebra.centralizer K (B : Set A)) = finrank K A :=
  finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite B

/-- **`B` and its centralizer generate `A`, freely**: multiplication
`B ⊗[K] C_A(B) → A` is bijective.

The source is a simple ring, being the tensor product of the central simple algebra `B` with the
simple algebra `C_A(B)`, so the homomorphism is injective; the centralizer theorem says the two
sides have the same dimension over `K`, so it is surjective as well.

Only the isomorphism `TauCeti.tensorCentralizerAlgEquiv` assembled from this is exported. -/
private theorem tensorCentralizerAlgHom_bijective :
    Function.Bijective (tensorCentralizerAlgHom B) := by
  have := centralizer_isSimpleRing B
  have hinj : Function.Injective (tensorCentralizerAlgHom B) :=
    (tensorCentralizerAlgHom B : _ →ₐ[K] A).toRingHom.injective
  refine ⟨hinj, ?_⟩
  have hrank : finrank K (↥B ⊗[K] ↥(Subalgebra.centralizer K (B : Set A))) = finrank K A := by
    rw [Module.finrank_tensorProduct]
    exact finrank_mul_finrank_centralizer B
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := (tensorCentralizerAlgHom B).toLinearMap)).1 hinj

/-- **The tensor decomposition along a central simple subalgebra**: for a central simple
`K`-subalgebra `B` of a finite-dimensional simple `K`-algebra `A`,

  `B ⊗[K] C_A(B) ≃ₐ[K] A`,

by multiplication. It is `TauCeti.tensorCentralizerAlgHom`, which a private lemma of this file
shows to be bijective: the source is simple, so the map is injective, and the centralizer theorem
makes the two sides equidimensional, so it is surjective too. -/
noncomputable def tensorCentralizerAlgEquiv :
    ↥B ⊗[K] ↥(Subalgebra.centralizer K (B : Set A)) ≃ₐ[K] A :=
  AlgEquiv.ofBijective (tensorCentralizerAlgHom B) (tensorCentralizerAlgHom_bijective B)

@[simp]
theorem tensorCentralizerAlgEquiv_tmul (b : B) (c : Subalgebra.centralizer K (B : Set A)) :
    tensorCentralizerAlgEquiv B (b ⊗ₜ c) = (b : A) * (c : A) := by
  simp [tensorCentralizerAlgEquiv]

end Centralizer

/-!
### Centrality of the centralizer, and the double centralizer

The three statements below need `A` itself to be **central** simple, and not merely simple. This is
the first point in the file where that is so: the dimension formula and the tensor decomposition
hold over `K` without assuming that `A` is central, but `C_A(C_A(B)) = B` genuinely fails when `A`
has a larger center, as the second worked example at the end of the file records.
-/

section DoubleCentralizer

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A] (B : Subalgebra K A) [Algebra.IsCentral K B] [IsSimpleRing B]

/-- **The centralizer of a central simple subalgebra of a central simple algebra is central.**
Together with `TauCeti.centralizer_isSimpleRing` this says that `C_A(B)` is again central simple, so
that the centralizer theorem may be applied to it in turn.

The proof is the tensor decomposition `B ⊗[K] C_A(B) ≃ₐ[K] A` transported: the tensor product is
central because `A` is, and a tensor product of algebras over a field is central only if each factor
is, provided the other one is nontrivial (`Algebra.IsCentral.right_of_tensor_of_field`); here `B` is
nontrivial because it is simple. -/
theorem centralizer_isCentral :
    Algebra.IsCentral K ↥(Subalgebra.centralizer K (B : Set A)) :=
  have : Algebra.IsCentral K (↥B ⊗[K] ↥(Subalgebra.centralizer K (B : Set A))) :=
    Algebra.IsCentral.of_algEquiv K A _ (tensorCentralizerAlgEquiv B).symm
  Algebra.IsCentral.right_of_tensor_of_field K ↥B _

/-- **The double centralizer theorem for a central simple subalgebra.** For a central simple
`K`-subalgebra `B` of a finite-dimensional central simple `K`-algebra `A`,

  `C_A(C_A(B)) = B`.

One inclusion is formal. For the other, `C = C_A(B)` is itself central simple
(`TauCeti.centralizer_isSimpleRing` and `TauCeti.centralizer_isCentral`), so the centralizer theorem
applies to `C` as well and gives `finrank K C * finrank K C_A(C) = finrank K A`, while for `B` it
gives `finrank K B * finrank K C = finrank K A`. Cancelling `finrank K C`, which is positive, leaves
`finrank K C_A(C) = finrank K B`, and a subalgebra containing `B` with the dimension of `B` is `B`.

The inner centralizer is written as the `Set.centralizer` of `↑B`, which is what
`Subalgebra.coe_centralizer` (a `simp` lemma) turns the coerced subalgebra into, so that the
left-hand side is in simp normal form; `Subalgebra.centralizer_centralizer_centralizer` is stated
the same way. -/
@[simp]
theorem centralizer_centralizer :
    Subalgebra.centralizer K (Set.centralizer (B : Set A)) = B := by
  have := centralizer_isSimpleRing B
  have := centralizer_isCentral B
  have hC : 0 < finrank K ↥(Subalgebra.centralizer K (B : Set A)) := Module.finrank_pos
  have hdim : finrank K B
      = finrank K ↥(Subalgebra.centralizer K
        (Subalgebra.centralizer K (B : Set A) : Set A)) := by
    refine Nat.eq_of_mul_eq_mul_left hC ?_
    rw [finrank_mul_finrank_centralizer (Subalgebra.centralizer K (B : Set A)),
      ← finrank_mul_finrank_centralizer B, mul_comm]
  exact (Subalgebra.eq_of_le_of_finrank_eq (Subalgebra.le_centralizer_centralizer K) hdim).symm

/-- **The degree is multiplicative along a central simple subalgebra**:
`deg K B * deg K C_A(B) = deg K A`.

This is the dimension formula with square roots taken, the degree being the square root of the
dimension (`TauCeti.Algebra.deg_sq`), and it is the shape in which the centralizer theorem is
usually quoted. It is a statement about the degree of `C_A(B)`, so it needs `C_A(B)` to be
central simple, which is `TauCeti.centralizer_isCentral` together with
`TauCeti.centralizer_isSimpleRing`; given that, it is the tensor decomposition read through
`TauCeti.Algebra.deg_tensorProduct`. -/
theorem deg_mul_deg_centralizer :
    Algebra.deg K B * Algebra.deg K ↥(Subalgebra.centralizer K (B : Set A)) = Algebra.deg K A := by
  have := centralizer_isSimpleRing B
  have := centralizer_isCentral B
  have h := Algebra.deg_eq_of_algEquiv (K := K) (tensorCentralizerAlgEquiv B)
  rwa [Algebra.deg_tensorProduct (K := K) (A := ↥B)
    ↥(Subalgebra.centralizer K (B : Set A))] at h

end DoubleCentralizer

/-! ### Worked examples -/

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

/-- The negative control for `TauCeti.centralizer_centralizer`: centrality of the **ambient**
algebra cannot be dropped. Take `K = ℝ` and `A = ℂ` again, and `B = ⊥`, which is central simple,
being `ℝ` itself. Its centralizer is all of `ℂ`, and so is the centralizer of that, not `⊥`. -/
example :
    Subalgebra.centralizer ℝ
        (Subalgebra.centralizer ℝ ((⊥ : Subalgebra ℝ ℂ) : Set ℂ) : Set ℂ)
      ≠ (⊥ : Subalgebra ℝ ℂ) := by
  -- `⊥` consists of scalars, so it lies in the center of `ℂ`, and its centralizer is everything.
  have hbot : Subalgebra.centralizer ℝ ((⊥ : Subalgebra ℝ ℂ) : Set ℂ) = ⊤ :=
    (Subalgebra.centralizer_eq_top_iff_subset ℝ).2 (by simp)
  rw [hbot, centralizer_top_complex]
  intro h
  obtain ⟨r, hr⟩ := Algebra.mem_bot.1 (h ▸ (Algebra.mem_top : Complex.I ∈ (⊤ : Subalgebra ℝ ℂ)))
  simpa using congrArg Complex.im hr

end Example

end TauCeti
