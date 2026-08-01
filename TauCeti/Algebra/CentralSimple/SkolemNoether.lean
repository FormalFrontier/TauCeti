/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.CentralSimple.TensorProduct
public import TauCeti.RingTheory.Semisimple.SimpleArtinian
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
-- Non-public: none of these appears in the type of an exported declaration. Finiteness of a tensor
-- product, the passage from a finite-dimensional algebra to an Artinian ring, and the `Aᵐᵒᵖ`
-- linear equivalence are used only inside the proof of Skolem-Noether.
import Mathlib.Algebra.Central.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.Algebra.Central.Quaternion

/-!
# The Skolem-Noether theorem

Let `K` be a field, let `A` be a finite-dimensional **simple** `K`-algebra and let `B` be a
finite-dimensional **central simple** `K`-algebra. The Skolem-Noether theorem says that two
`K`-algebra homomorphisms `f g : B →ₐ[K] A` differ by conjugation: there is a unit `u` of `A` with
`g x = u * f x * u⁻¹` for every `x`. Taking `B = A` and `f` the identity, every `K`-algebra
automorphism of a finite-dimensional central simple algebra is inner.

The proof is the classical module-theoretic one. A homomorphism `f : B →ₐ[K] A` makes `A` into a
module over `R = B ⊗[K] Aᵐᵒᵖ`, with `B` acting on the left through `f` and `A` on the right by
multiplication; this is `TauCeti.Bimodule f`. Because `B` is central simple and `Aᵐᵒᵖ` is simple,
`R` is a simple ring (`TauCeti.IsSimpleRing.tensorProduct`), and it is finite-dimensional over `K`,
hence Artinian. The two modules `TauCeti.Bimodule f` and `TauCeti.Bimodule g` are carried by one
and the same `K`-vector space `A`, so they have equal dimension, so they are isomorphic `R`-modules
(`TauCeti.IsSimpleRing.nonempty_linearEquiv_of_finrank_eq`). An `R`-linear isomorphism is in
particular linear for the right action of `A`, hence is multiplication on the left by the unit
`u = φ 1`, and its linearity for the left action of `B` is exactly `u * f x = g x * u`.

## Main results

* `TauCeti.Bimodule`: `A` as a module over `B ⊗[K] Aᵐᵒᵖ` through an algebra homomorphism
  `f : B →ₐ[K] A`, with its basic API (`TauCeti.Bimodule.of`, `TauCeti.Bimodule.smul_of`).
* `TauCeti.skolemNoether`: **the Skolem-Noether theorem**.
* `TauCeti.exists_units_conj_of_algEquiv`: every `K`-algebra automorphism of a finite-dimensional
  central simple `K`-algebra is inner.
* `TauCeti.exists_units_conj_subalgebra_val`: a `K`-algebra homomorphism out of a central simple
  subalgebra `B ⊆ A` is conjugate to the inclusion of `B`. This is the form the centralizer theorem
  consumes.

## Implementation notes

Centrality is asked of the **source** `B`, not of the target `A`: what the proof needs is that
`B ⊗[K] Aᵐᵒᵖ` is simple, and `TauCeti.IsSimpleRing.tensorProduct` gets that from `B` central simple
and `A` simple. So the statement here is slightly stronger than the usual one, which asks `A` to be
central simple as well; the roadmap's central simple form is the case `Algebra.IsCentral K A`, which
the statement covers because a central simple algebra is in particular simple. Finite-dimensionality
of `B` is essential and is carried explicitly: the classification of modules that supplies `φ` needs
`B ⊗[K] Aᵐᵒᵖ` to be Artinian.

Centrality of the source really is needed, and not just by this proof: the worked example at the end
of the file exhibits `ℂ` as a simple finite-dimensional `ℝ`-algebra, not central over `ℝ`, whose
complex conjugation is not conjugation by a unit. The classical theorem does hold for a merely
simple `B` provided the ambient `A` is central simple, but that form needs the centralizer theorem
and is a separate, later target; the central simple form pinned here is what the centralizer theorem
itself consumes.

`TauCeti.Bimodule f` is a type synonym for `A` rather than a `Module` instance on `A` itself,
because the whole point is to compare the two different `B ⊗[K] Aᵐᵒᵖ`-module structures coming from
`f` and from `g`; indexing the synonym by the homomorphism keeps both available at once. Mathlib
takes the same route for `A ⊗[R] Aᵐᵒᵖ` acting on `A` in `Mathlib/Algebra/Azumaya/Defs.lean`, where
`instModuleTensorProductMop` is deliberately not an instance. The action map is built from Mathlib's
`AlgHom.mulLeftRight` by restricting along `f` on the left factor, so the two agree for `f` the
identity of `A`.

## References

This implements the Layer 5 target `skolemNoether` of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12, and P. Gille, T. Szamuely, *Central
Simple Algebras and Galois Cohomology*, Chapter 2.
-/

public section

namespace TauCeti

open scoped TensorProduct

section Construction

variable {K A B : Type*} [CommSemiring K] [Ring A] [Algebra K A] [Semiring B] [Algebra K B]

/-- `A` regarded as a left module over `B ⊗[K] Aᵐᵒᵖ` through an algebra homomorphism
`f : B →ₐ[K] A`: the element `b ⊗ₜ op a` acts by `x ↦ f b * x * a`.

Equivalently this is the `B`-`A`-bimodule `A` obtained by restricting the left action along `f`,
packaged as a left module over `B ⊗[K] Aᵐᵒᵖ` in the usual way. It is a type synonym for `A`
precisely so that the structures coming from two different homomorphisms can be compared. -/
@[expose] def Bimodule (_f : B →ₐ[K] A) : Type _ := A

namespace Bimodule

variable (f : B →ₐ[K] A)

instance : AddCommGroup (Bimodule f) := inferInstanceAs (AddCommGroup A)

instance : Module K (Bimodule f) := inferInstanceAs (Module K A)

/-- The action of `B ⊗[K] Aᵐᵒᵖ` on `A` defining `TauCeti.Bimodule f`, as an algebra homomorphism
into `Module.End K A`. It is Mathlib's `AlgHom.mulLeftRight` restricted along `f` on the left
factor, so for `f = AlgHom.id K A` it is `AlgHom.mulLeftRight K A` itself. -/
noncomputable def toEnd : B ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  (AlgHom.mulLeftRight K A).comp (Algebra.TensorProduct.map f (AlgHom.id K Aᵐᵒᵖ))

@[simp]
theorem toEnd_tmul_apply (b : B) (a : Aᵐᵒᵖ) (x : A) : toEnd f (b ⊗ₜ a) x = f b * x * a.unop := by
  simp [toEnd]

noncomputable instance : Module (B ⊗[K] Aᵐᵒᵖ) (Bimodule f) :=
  Module.compHom (M := A) (toEnd f).toRingHom

instance : IsScalarTower K (B ⊗[K] Aᵐᵒᵖ) (Bimodule f) where
  smul_assoc c r x := by
    change (toEnd f (c • r)) _ = c • (toEnd f r) _
    rw [map_smul]
    rfl

instance [Module.Finite K A] : Module.Finite K (Bimodule f) := inferInstanceAs (Module.Finite K A)

/-- `TauCeti.Bimodule f` is `A` again as a `K`-module: only the `B ⊗[K] Aᵐᵒᵖ`-action is new. -/
def of : A ≃ₗ[K] Bimodule f := LinearEquiv.refl K A

@[simp]
theorem smul_of (b : B) (a : Aᵐᵒᵖ) (x : A) :
    (b ⊗ₜ a : B ⊗[K] Aᵐᵒᵖ) • of f x = of f (f b * x * a.unop) :=
  toEnd_tmul_apply f b a x

@[simp]
theorem symm_smul (b : B) (a : Aᵐᵒᵖ) (y : Bimodule f) :
    (of f).symm ((b ⊗ₜ a : B ⊗[K] Aᵐᵒᵖ) • y) = f b * (of f).symm y * a.unop :=
  toEnd_tmul_apply f b a ((of f).symm y)

end Bimodule

end Construction

section SkolemNoether

variable (K : Type*) {A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- **The Skolem-Noether theorem.** Two `K`-algebra homomorphisms `f g : B →ₐ[K] A` from a
finite-dimensional **central simple** `K`-algebra `B` to a finite-dimensional **simple** `K`-algebra
`A` are conjugate: there is a unit `u` of `A` with `g x = u * f x * u⁻¹` for all `x : B`.

Finite-dimensionality of `B` cannot be dropped; it is what makes `B ⊗[K] Aᵐᵒᵖ` Artinian, and with it
the classification of modules that produces the conjugating isomorphism. -/
theorem skolemNoether [IsSimpleRing A] [FiniteDimensional K A]
    [Algebra.IsCentral K B] [IsSimpleRing B] [FiniteDimensional K B] (f g : B →ₐ[K] A) :
    ∃ u : Aˣ, ∀ x : B, g x = (u : A) * f x * (↑u⁻¹ : A) := by
  have : FiniteDimensional K Aᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv K)
  have : IsArtinianRing (B ⊗[K] Aᵐᵒᵖ) := IsArtinianRing.of_finite K _
  have hrank : Module.finrank K (Bimodule f) = Module.finrank K (Bimodule g) := rfl
  obtain ⟨φ⟩ := IsSimpleRing.nonempty_linearEquiv_of_finrank_eq (R := B ⊗[K] Aᵐᵒᵖ) K hrank
  set u : A := (Bimodule.of g).symm (φ (Bimodule.of f 1)) with hu
  -- Linearity of `φ` for the right action of `A` makes it left multiplication by `u`.
  have key : ∀ a : A, (Bimodule.of g).symm (φ (Bimodule.of f a)) = u * a := by
    intro a
    have ha : Bimodule.of f a = (1 ⊗ₜ MulOpposite.op a : B ⊗[K] Aᵐᵒᵖ) • Bimodule.of f 1 := by
      rw [Bimodule.smul_of]; simp
    rw [ha, map_smul, Bimodule.symm_smul]
    simp [hu]
  have hu' : φ (Bimodule.of f 1) = Bimodule.of g u := by
    have h1 := key 1
    rw [mul_one] at h1
    rw [← h1]
    simp
  -- Surjectivity of `φ` gives a right inverse of `u`; injectivity makes it two-sided.
  obtain ⟨y, hy⟩ := φ.surjective (Bimodule.of g 1)
  set v : A := (Bimodule.of f).symm y with hv
  have huv : u * v = 1 := by
    have h := key v
    rw [hv, LinearEquiv.apply_symm_apply, hy] at h
    simpa using h.symm
  have hinj : ∀ z : A, u * z = 0 → z = 0 := by
    intro z hz
    have h := key z
    rw [hz] at h
    have h' : φ (Bimodule.of f z) = 0 := (Bimodule.of g).symm.map_eq_zero_iff.mp h
    have := φ.injective (h'.trans (map_zero φ).symm)
    simpa using congrArg (Bimodule.of f).symm this
  have hvu : v * u = 1 := by
    refine sub_eq_zero.mp (hinj _ ?_)
    rw [mul_sub, ← mul_assoc, huv, one_mul, mul_one, sub_self]
  -- Linearity of `φ` for the left action of `B` is the conjugation relation.
  have hb : ∀ b : B, u * f b = g b * u := by
    intro b
    have h1 : (b ⊗ₜ (1 : Aᵐᵒᵖ) : B ⊗[K] Aᵐᵒᵖ) • Bimodule.of f 1 = Bimodule.of f (f b) := by
      rw [Bimodule.smul_of]; simp
    calc u * f b = (Bimodule.of g).symm (φ (Bimodule.of f (f b))) := (key (f b)).symm
      _ = (Bimodule.of g).symm (φ ((b ⊗ₜ (1 : Aᵐᵒᵖ) : B ⊗[K] Aᵐᵒᵖ) • Bimodule.of f 1)) := by
            rw [h1]
      _ = (Bimodule.of g).symm ((b ⊗ₜ (1 : Aᵐᵒᵖ) : B ⊗[K] Aᵐᵒᵖ) • φ (Bimodule.of f 1)) := by
            rw [map_smul]
      _ = (Bimodule.of g).symm ((b ⊗ₜ (1 : Aᵐᵒᵖ) : B ⊗[K] Aᵐᵒᵖ) • Bimodule.of g u) := by rw [hu']
      _ = g b * u := by rw [Bimodule.smul_of]; simp
  refine ⟨⟨u, v, huv, hvu⟩, fun x ↦ ?_⟩
  change g x = u * f x * v
  rw [hb x, mul_assoc, huv, mul_one]

/-- **Every automorphism of a central simple algebra is inner.** A `K`-algebra automorphism of a
finite-dimensional central simple `K`-algebra `A` is conjugation by a unit of `A`. -/
theorem exists_units_conj_of_algEquiv [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (e : A ≃ₐ[K] A) :
    ∃ u : Aˣ, ∀ x : A, e x = (u : A) * x * (↑u⁻¹ : A) :=
  skolemNoether K (AlgHom.id K A) e.toAlgHom

/-- A `K`-algebra homomorphism out of a **central simple** subalgebra `B` of a finite-dimensional
simple `K`-algebra `A` is conjugate to the inclusion of `B`: it extends to an inner automorphism of
`A`. This is the form the centralizer theorem consumes. -/
theorem exists_units_conj_subalgebra_val [IsSimpleRing A] [FiniteDimensional K A]
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
`TauCeti.exists_units_conj_of_algEquiv` are found by instance search: `Mₙ(K)` is central over `K`,
simple, and finite-dimensional. -/
example (K : Type*) [Field K] (n : ℕ) [NeZero n]
    (e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    ∃ u : (Matrix (Fin n) (Fin n) K)ˣ, ∀ x, e x =
      (u : Matrix (Fin n) (Fin n) K) * x * (↑u⁻¹ : Matrix (Fin n) (Fin n) K) :=
  exists_units_conj_of_algEquiv K e

/-- **Skolem-Noether in the small**: every `ℝ`-algebra automorphism of the real quaternions is
inner. Centrality comes from `TauCeti.Quaternion.instIsCentral`, simplicity from `ℍ[ℝ]` being a
division ring. -/
example (e : ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]) :
    ∃ u : ℍ[ℝ]ˣ, ∀ x : ℍ[ℝ], e x = (u : ℍ[ℝ]) * x * (↑u⁻¹ : ℍ[ℝ]) :=
  exists_units_conj_of_algEquiv ℝ e

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
