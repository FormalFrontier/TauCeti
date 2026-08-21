/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: exactly the modules supplying types and classes that occur in the statements exported
-- from here. `Mathlib.RingTheory.TensorProduct.Basic` carries `AlgHom`, `AlgEquiv` and
-- `Subalgebra`; the other three carry `Algebra.IsCentral`, `IsSimpleRing` and `FiniteDimensional`.
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
-- Non-public: none of these appears in the type of an exported declaration. The
-- `B ⊗[K] Aᵐᵒᵖ`-module structure on `A`, simplicity of a tensor product, the classification of
-- modules over a simple Artinian algebra and finiteness of a tensor product are used only inside
-- proofs, and the matrix, complex and quaternion modules only by the worked examples at the end.
import Mathlib.Algebra.Central.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.Algebra.Central.Quaternion
import TauCeti.Algebra.CentralSimple.Bimodule
import TauCeti.Algebra.CentralSimple.TensorProduct
import TauCeti.RingTheory.Semisimple.SimpleArtinian

/-!
# The Skolem-Noether theorem

Let `K` be a field, let `A` be a finite-dimensional **simple** `K`-algebra and let `B` be a
finite-dimensional **central simple** `K`-algebra. The Skolem-Noether theorem says that two
`K`-algebra homomorphisms `f g : B →ₐ[K] A` differ by conjugation: there is a unit `u` of `A` with
`g x = u * f x * u⁻¹` for every `x`. Taking `B = A` and `f` the identity, every `K`-algebra
automorphism of a finite-dimensional central simple algebra is inner.

The proof is the classical module-theoretic one. A homomorphism `f : B →ₐ[K] A` makes `A` into a
module over `R = B ⊗[K] Aᵐᵒᵖ`, with `B` acting on the left through `f` and `A` on the right by
multiplication; this is `TauCeti.Bimodule f`. Because `B` is central simple and `Aᵐᵒᵖ` is
simple, `R` is a simple ring (`TauCeti.IsSimpleRing.tensorProduct`), and it is finite-dimensional
over `K`, hence Artinian. The two modules `Bimodule f` and `Bimodule g` are carried by one and the
same `K`-vector space `A`, so they have equal dimension, so they are isomorphic `R`-modules
(`TauCeti.IsSimpleRing.nonempty_linearEquiv_of_finrank_eq`). An `R`-linear isomorphism is in
particular linear for the right action of `A`, hence is multiplication on the left by the unit
`u = φ 1`, and its linearity for the left action of `B` is exactly `u * f x = g x * u`.

## Main results

* `TauCeti.skolemNoether`: **the Skolem-Noether theorem**.
* `TauCeti.exists_unit_conj_of_algEquiv`: every `K`-algebra automorphism of a finite-dimensional
  central simple `K`-algebra is inner.
* `TauCeti.exists_unit_conj_subalgebra_val`: a `K`-algebra homomorphism out of a central simple
  subalgebra `B ⊆ A` is conjugate to the inclusion of `B`. This is the form the centralizer theorem
  consumes.

## Implementation notes

Centrality is asked of the **source** `B`, not of the target `A`: what the proof needs is that
`B ⊗[K] Aᵐᵒᵖ` is simple, and `TauCeti.IsSimpleRing.tensorProduct` gets that from `B` central simple
and `A` simple. So the statement here is slightly stronger than the usual one, which asks `A` to be
central simple as well; the roadmap's central simple form is the case `Algebra.IsCentral K A`, which
the statement covers because a central simple algebra is in particular simple. Finite-dimensionality
of `B` is *not* assumed: the proof does need it, because the classification of modules that supplies
`φ` needs `B ⊗[K] Aᵐᵒᵖ` to be finite-dimensional over `K` and with it Artinian, but it comes for
free from the other hypotheses, since a homomorphism out of the simple ring `B` into the nontrivial
ring `A` is injective and `A` is finite-dimensional.

Centrality of the source really is needed, and not just by this proof: the worked example at the end
of the file exhibits `ℂ` as a simple finite-dimensional `ℝ`-algebra, not central over `ℝ`, whose
complex conjugation is not conjugation by a unit. The classical theorem does hold for a merely
simple `B` provided the ambient `A` is central simple, but that form needs the centralizer theorem
and is a separate, later target; the central simple form pinned here is what the centralizer theorem
itself consumes.

`TauCeti.Bimodule f` is a type synonym for `A` rather than a `Module` instance on `A` itself,
because the whole point is to compare the two different `B ⊗[K] Aᵐᵒᵖ`-module structures coming from
`f` and from `g`; indexing the synonym by the homomorphism keeps both available at once. It lives in
`TauCeti/Algebra/CentralSimple/Bimodule.lean`, which documents the construction; the centralizer
theorem is its second consumer. The statements exported from this file are the three theorems below,
all phrased in `A` and `B` alone.

## References

This implements the Layer 5 target `skolemNoether` of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12, and P. Gille, T. Szamuely, *Central
Simple Algebras and Galois Cohomology*, Chapter 2.
-/

public section

namespace TauCeti

open scoped TensorProduct

section SkolemNoether

variable (K : Type*) {A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- **The Skolem-Noether theorem.** Two `K`-algebra homomorphisms `f g : B →ₐ[K] A` from a
finite-dimensional **central simple** `K`-algebra `B` to a finite-dimensional **simple** `K`-algebra
`A` are conjugate: there is a unit `u` of `A` with `g x = u * f x * u⁻¹` for all `x : B`.

Finite-dimensionality of `B` is not among the hypotheses: it follows from them, because `f` is
injective, `B` being simple and `A` nontrivial. The proof does use it, to make `B ⊗[K] Aᵐᵒᵖ`
Artinian, and with it the classification of modules that produces the conjugating isomorphism. -/
theorem skolemNoether [IsSimpleRing A] [FiniteDimensional K A]
    [Algebra.IsCentral K B] [IsSimpleRing B] (f g : B →ₐ[K] A) :
    ∃ u : Aˣ, ∀ x : B, g x = (u : A) * f x * (↑u⁻¹ : A) := by
  -- `B` is simple and `A` nontrivial, so `f` is injective and `B` inherits finite-dimensionality.
  have hf : Function.Injective f := f.toRingHom.injective
  have : FiniteDimensional K B := FiniteDimensional.of_injective f.toLinearMap hf
  have : FiniteDimensional K Aᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv K)
  have hrank : Module.finrank K (Bimodule f) = Module.finrank K (Bimodule g) :=
    ((Bimodule.of f).symm.trans (Bimodule.of g)).finrank_eq
  obtain ⟨φ⟩ := IsSimpleRing.nonempty_linearEquiv_of_finrank_eq (R := B ⊗[K] Aᵐᵒᵖ) K hrank
  -- The two steps below need only linearity and that `of g 1` is hit, so use `φ` as a linear map.
  set ψ : Bimodule f →ₗ[B ⊗[K] Aᵐᵒᵖ] Bimodule g := φ.toLinearMap with hψ
  have hψsurj : Function.Surjective ψ := by rw [hψ]; simpa using φ.surjective
  obtain ⟨v, huv⟩ := Bimodule.exists_symm_apply_one_mul_eq_one ψ (hψsurj _)
  -- `A` is finite-dimensional over a field, hence Artinian, hence Dedekind-finite
  -- (`IsArtinianRing.of_finite` is a theorem, not an instance, so it is supplied by hand).
  -- A right inverse therefore already presents the conjugator as a unit.
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  set u : A := (Bimodule.of g).symm (ψ (Bimodule.of f 1)) with hu
  -- Name the two coercions of the constructed unit through the stable `Units` API rather than
  -- relying on `Units.mkOfMulEqOne` reducing definitionally.
  have hUval : ((Units.mkOfMulEqOne u v huv : Aˣ) : A) = u := Units.val_mkOfMulEqOne huv
  have hUinv : (↑(Units.mkOfMulEqOne u v huv)⁻¹ : A) = v :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hUval]; exact huv)
  -- Name the conjugation relation at the abstraction boundary, so `u` never has to be unfolded.
  have hb : ∀ b : B, u * f b = g b * u :=
    Bimodule.symm_apply_one_mul_eq_mul_symm_apply_one ψ
  refine ⟨Units.mkOfMulEqOne u v huv, fun x ↦ ?_⟩
  rw [hUval, hUinv, hb x, mul_assoc, huv, mul_one]

/-- **Every automorphism of a central simple algebra is inner.** A `K`-algebra automorphism of a
finite-dimensional central simple `K`-algebra `A` is conjugation by a unit of `A`. -/
theorem exists_unit_conj_of_algEquiv [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (e : A ≃ₐ[K] A) :
    ∃ u : Aˣ, ∀ x : A, e x = (u : A) * x * (↑u⁻¹ : A) :=
  skolemNoether K (AlgHom.id K A) e.toAlgHom

/-- A `K`-algebra homomorphism out of a **central simple** subalgebra `B` of a finite-dimensional
simple `K`-algebra `A` is conjugate to the inclusion of `B`: it extends to an inner automorphism of
`A`. This is the form the centralizer theorem consumes. -/
theorem exists_unit_conj_subalgebra_val [IsSimpleRing A] [FiniteDimensional K A]
    (B : Subalgebra K A) [Algebra.IsCentral K B] [IsSimpleRing B] (f : B →ₐ[K] A) :
    ∃ u : Aˣ, ∀ x : B, f x = (u : A) * (x : A) * (↑u⁻¹ : A) :=
  skolemNoether K B.val f

end SkolemNoether

/-! ### Worked examples -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- **Every automorphism of a matrix algebra is inner.** All three hypotheses of
`TauCeti.exists_unit_conj_of_algEquiv` are found by instance search: `Mₙ(K)` is central over `K`,
simple, and finite-dimensional. -/
example (K : Type*) [Field K] (n : ℕ) [NeZero n]
    (e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    ∃ u : (Matrix (Fin n) (Fin n) K)ˣ, ∀ x, e x =
      (u : Matrix (Fin n) (Fin n) K) * x * (↑u⁻¹ : Matrix (Fin n) (Fin n) K) :=
  exists_unit_conj_of_algEquiv K e

/-- **Skolem-Noether in the small**: every `ℝ`-algebra automorphism of the real quaternions is
inner. Centrality comes from `TauCeti.Quaternion.instIsCentral`, simplicity from `ℍ[ℝ]` being a
division ring. -/
example (e : ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]) :
    ∃ u : ℍ[ℝ]ˣ, ∀ x : ℍ[ℝ], e x = (u : ℍ[ℝ]) * x * (↑u⁻¹ : ℍ[ℝ]) :=
  exists_unit_conj_of_algEquiv ℝ e

/-- The negative control for `TauCeti.skolemNoether`: centrality of the **source** cannot be
dropped. Take `K = ℝ` and `A = B = ℂ`, a simple finite-dimensional `ℝ`-algebra which is not central
over `ℝ`. The identity and complex conjugation are then two `ℝ`-algebra endomorphisms of `ℂ` that
are *not* conjugate, because `ℂ` is commutative, so conjugation by a unit is the identity while
conjugation is not. -/
example : ¬ ∃ u : ℂˣ, ∀ x : ℂ, (starRingEnd ℂ) x = (u : ℂ) * x * (↑u⁻¹ : ℂ) := by
  rintro ⟨u, hu⟩
  have h := hu Complex.I
  rw [mul_comm (u : ℂ) Complex.I, mul_assoc, u.mul_inv, mul_one, Complex.conj_I] at h
  have him : (-1 : ℝ) = 1 := by simpa using congrArg Complex.im h
  norm_num at him

end Examples

end TauCeti
