/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: exactly the modules supplying types and classes that occur in the statements exported
-- from here. `Mathlib.RingTheory.TensorProduct.Basic` carries `AlgHom`, `AlgEquiv` and `Subalgebra`
-- (and the algebra structure on `B ⊗[K] Aᵐᵒᵖ` that the private construction below uses); the other
-- three carry `Algebra.IsCentral`, `IsSimpleRing` and `FiniteDimensional`.
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
-- Non-public: none of these appears in the type of an exported declaration. Simplicity of a tensor
-- product, the classification of modules over a simple Artinian algebra, `AlgHom.mulLeftRight`,
-- `Algebra.TensorProduct.map` and finiteness of a tensor product are used only inside proofs, and
-- the matrix, complex and quaternion modules only by the worked examples at the end of the file.
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Central.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.Algebra.Central.Quaternion
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
multiplication; this is the private `Bimodule f` below. Because `B` is central simple and `Aᵐᵒᵖ` is
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

`Bimodule f` is a type synonym for `A` rather than a `Module` instance on `A` itself, because the
whole point is to compare the two different `B ⊗[K] Aᵐᵒᵖ`-module structures coming from `f` and from
`g`; indexing the synonym by the homomorphism keeps both available at once. Mathlib takes the same
route for `A ⊗[R] Aᵐᵒᵖ` acting on `A` in `Mathlib/Algebra/Azumaya/Defs.lean`, where
`instModuleTensorProductMop` is deliberately not an instance. The action map is built from Mathlib's
`AlgHom.mulLeftRight` by restricting along `f` on the left factor, so the two agree for `f` the
identity of `A`.

The whole construction is `private`: it is the mechanism of the proof below and has no consumer
outside this file, so none of it — the synonym, its representation as `A`, the action map, or the
instances — reaches the interface, and no importer can depend on `Bimodule f` being `A`
definitionally. A type synonym cannot be carried by a `Module` instance without unfolding its body,
so making it public would mean exposing that body; the exported statements are the three theorems
below, all phrased in `A` and `B` alone. Should a later file need the bimodule, it can be made
public then, together with an interface that pins down what that file actually uses.

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
precisely so that the structures coming from two different homomorphisms can be compared, and it is
`private` because it is the mechanism of the proof below rather than part of the interface. -/
private def Bimodule (_f : B →ₐ[K] A) : Type _ := A

namespace Bimodule

variable (f : B →ₐ[K] A)

private instance : AddCommGroup (Bimodule f) := inferInstanceAs (AddCommGroup A)

private instance : Module K (Bimodule f) := inferInstanceAs (Module K A)

/-- `Bimodule f` is `A` again as a `K`-module: only the `B ⊗[K] Aᵐᵒᵖ`-action is new. -/
private def of : A ≃ₗ[K] Bimodule f := LinearEquiv.refl K A

/-- The action of `B ⊗[K] Aᵐᵒᵖ` on `A` defining `Bimodule f`, as an algebra homomorphism into
`Module.End K A`. It is Mathlib's `AlgHom.mulLeftRight` restricted along `f` on the left factor, so
for `f = AlgHom.id K A` it is `AlgHom.mulLeftRight K A` itself. -/
private noncomputable def toEnd : B ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  (AlgHom.mulLeftRight K A).comp (Algebra.TensorProduct.map f (AlgHom.id K Aᵐᵒᵖ))

/-- A pure tensor `b ⊗ₜ op a` acts on `x : A` through `toEnd f` by `x ↦ f b * x * a`. -/
@[simp]
private theorem toEnd_tmul_apply (b : B) (a : Aᵐᵒᵖ) (x : A) :
    toEnd f (b ⊗ₜ a) x = f b * x * a.unop := by
  simp [toEnd]

private noncomputable instance : Module (B ⊗[K] Aᵐᵒᵖ) (Bimodule f) :=
  Module.compHom (M := A) (toEnd f).toRingHom

/-- A scalar `r : B ⊗[K] Aᵐᵒᵖ` acts on `Bimodule f` through `toEnd f`. This is the defining equation
of the module structure, and the single place it is unfolded: the scalar tower instance below
rewrites with it instead of reasoning up to definitional equality. -/
private theorem smul_def (r : B ⊗[K] Aᵐᵒᵖ) (x : A) : r • of f x = of f (toEnd f r x) := rfl

private instance : IsScalarTower K (B ⊗[K] Aᵐᵒᵖ) (Bimodule f) where
  smul_assoc c r x := by
    rw [← (of f).apply_symm_apply x, smul_def, smul_def, map_smul (toEnd f),
      LinearMap.smul_apply, map_smul (of f)]

private instance [Module.Finite K A] : Module.Finite K (Bimodule f) :=
  inferInstanceAs (Module.Finite K A)

/-- A pure tensor `b ⊗ₜ op a` acts on `Bimodule f` by `x ↦ f b * x * a`: the left factor acts on the
left through `f`, the right factor on the right by multiplication. -/
@[simp]
private theorem smul_of (b : B) (a : Aᵐᵒᵖ) (x : A) :
    (b ⊗ₜ a : B ⊗[K] Aᵐᵒᵖ) • of f x = of f (f b * x * a.unop) :=
  toEnd_tmul_apply f b a x

/-- `smul_of` read back through `of`: the action of a pure tensor `b ⊗ₜ op a`, transported to `A`,
is `x ↦ f b * x * a`. -/
@[simp]
private theorem symm_smul (b : B) (a : Aᵐᵒᵖ) (y : Bimodule f) :
    (of f).symm ((b ⊗ₜ a : B ⊗[K] Aᵐᵒᵖ) • y) = f b * (of f).symm y * a.unop :=
  toEnd_tmul_apply f b a ((of f).symm y)

end Bimodule

end Construction

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
  rw [Units.inv_mk, Units.val_mk, Units.val_mk, hb x, mul_assoc, huv, mul_one]

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
