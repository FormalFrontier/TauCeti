/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# The tensor product of hom modules is the hom module of the tensor products

Mathlib's `PiTensorProduct.piTensorHomMap` is the canonical comparison map

`⨂ᵢ (Mᵢ →ₗ Nᵢ) → (⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ)`,  `⨂ᵢ fᵢ ↦ ⨂ᵢ mᵢ ↦ ⨂ᵢ fᵢ mᵢ`,

defined for arbitrary families of modules over a commutative semiring. This file proves that it is
**bijective** as soon as the index type is finite and every `Mᵢ` and every `Nᵢ` is finite free, and
packages the result as the linear equivalence `PiTensorProduct.piTensorHomEquiv`.

The proof is the basis computation. If `bᵢ` is a basis of `Mᵢ` indexed by `κᵢ` and `cᵢ` a basis of
`Nᵢ` indexed by `νᵢ`, then `Module.Basis.linearMap` gives the matrix-unit basis of `Mᵢ →ₗ Nᵢ`
indexed by `νᵢ × κᵢ`, and `Module.Basis.piTensorProduct` turns a family of bases into a basis of a
tensor product. The comparison map carries the tensor of the matrix-unit bases to the matrix-unit
basis of `⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ` built from the two tensored bases, along the regrouping
`(∀ i, νᵢ × κᵢ) ≃ (∀ i, νᵢ) × (∀ i, κᵢ)`; a linear map taking a basis bijectively to a basis is an
isomorphism. Finiteness of the index type and of each basis is what gives the two sides matching
bases at all, and it is used nowhere else.

Taking `Nᵢ = Mᵢ` this identifies `End (⨂ᵢ Mᵢ)` with `⨂ᵢ End Mᵢ`, compatibly with composition
(`PiTensorProduct.piTensorHomEquiv_tprod_comp_tprod`). That identification is the shape in which the
commutant computations of Schur-Weyl duality are run: the endomorphisms of a tensor power commuting
with the permutations of the factors are the invariants of the permutation action on the tensor
power of the endomorphism algebra.

## Main definitions

* `PiTensorProduct.piTensorHomEquiv`: the comparison map as a linear equivalence, for a finite
  index type and finite free modules.

## Main results

* `PiTensorProduct.piTensorHomMap_bijective_of_basis`: bijectivity of the comparison map from a
  family of finite bases, the engine of the file.
* `PiTensorProduct.piTensorHomMap_bijective`: bijectivity in the finite free formulation.
* `PiTensorProduct.piTensorHomEquiv_tprod_comp_tprod`: the equivalence turns the factorwise
  composition of two pure tensors of endomorphisms into the composition of their images.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8, "The double centralizer (image-level)". The commutant of the symmetric-group image in
  `End (V^{⊗n})` is computed by transporting it through this isomorphism to the invariants of the
  permutation action on `(End V)^{⊗n}`; the invariants are supplied by
  `TauCeti/RepresentationTheory/Symmetric/TensorAction/Invariants.lean`, which names this
  isomorphism as the comparison it is missing.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix B.1.
-/

public section

open Module

open scoped TensorProduct

namespace PiTensorProduct

universe uι uR uM uN uκ uν

variable {ι : Type uι} {R : Type uR} {M : ι → Type uM} {N : ι → Type uN}
  [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

section Bijective

variable {κ : ι → Type uκ} {ν : ι → Type uν}

/-- Regrouping a family of pairs as a pair of families. This is the reindexing along which the
comparison map matches the matrix-unit basis of `⨂ᵢ (Mᵢ →ₗ Nᵢ)` with that of
`⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ`. -/
private def piProdEquiv : (∀ i, ν i × κ i) ≃ (∀ i, ν i) × (∀ i, κ i) where
  toFun p := (fun i => (p i).1, fun i => (p i).2)
  invFun q i := (q.1 i, q.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite ι] [∀ i, Finite (κ i)] [∀ i, Finite (ν i)]

/-- **The comparison map is bijective**, given a finite basis of every `Mᵢ` and of every `Nᵢ`.

The tensor of the matrix-unit bases of the `Mᵢ →ₗ Nᵢ` is carried to the matrix-unit basis of
`⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ`, up to the regrouping `(∀ i, νᵢ × κᵢ) ≃ (∀ i, νᵢ) × (∀ i, κᵢ)`. -/
theorem piTensorHomMap_bijective_of_basis (b : ∀ i, Basis (κ i) R (M i))
    (c : ∀ i, Basis (ν i) R (N i)) :
    Function.Bijective (piTensorHomMap (R := R) (s := M) (t := N)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : ∀ i, Fintype (κ i) := fun i => Fintype.ofFinite (κ i)
  have : ∀ i, Fintype (ν i) := fun i => Fintype.ofFinite (ν i)
  set B := Basis.piTensorProduct fun i => (b i).linearMap (c i) with hBdef
  set C := (Basis.piTensorProduct b).linearMap (Basis.piTensorProduct c) with hCdef
  -- The comparison map agrees with the basis-indexed equivalence on the basis `B`.
  have hkey : (piTensorHomMap (R := R) (s := M) (t := N)) =
      (B.equiv C piProdEquiv).toLinearMap := by
    refine B.ext fun p => ?_
    refine (Basis.piTensorProduct b).ext fun q => ?_
    -- Both sides send `⨂ᵢ bᵢ (qᵢ)` to `⨂ᵢ cᵢ (pᵢ).1` when `q` matches the source indices of `p`,
    -- and to zero otherwise. The matrix-unit lemma has to fire before the tensored bases are
    -- unfolded, since it matches on a basis vector of the source.
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, hCdef, Basis.linearMap_apply_apply, hBdef]
    simp only [Basis.piTensorProduct_apply, piTensorHomMap_tprod_tprod,
      Basis.linearMap_apply_apply, piProdEquiv, Equiv.coe_fn_mk]
    by_cases hpq : (fun i => (p i).2) = q
    · subst hpq
      simp
    · rw [ite_eq_right hpq]
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hpq
      refine (tprod R).map_coord_zero i₀ ?_
      simp [hi₀]
  rw [hkey]
  exact (B.equiv C piProdEquiv).bijective

end Bijective

section Free

variable [Finite ι] [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
  [∀ i, Module.Free R (N i)] [∀ i, Module.Finite R (N i)]

/-- **The comparison map `⨂ᵢ (Mᵢ →ₗ Nᵢ) → (⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ)` is bijective** over a finite index
type when every `Mᵢ` and every `Nᵢ` is finite free. -/
theorem piTensorHomMap_bijective :
    Function.Bijective (piTensorHomMap (R := R) (s := M) (t := N)) :=
  piTensorHomMap_bijective_of_basis (fun i => Module.Free.chooseBasis R (M i))
    fun i => Module.Free.chooseBasis R (N i)

variable (R M N) in
/-- **The tensor product of the hom modules is the hom module of the tensor products.** The
underlying map is `PiTensorProduct.piTensorHomMap`, so this is a statement about a canonical map
and not about a choice of bases, even though the proof makes one. -/
noncomputable def piTensorHomEquiv :
    (⨂[R] i, M i →ₗ[R] N i) ≃ₗ[R] ((⨂[R] i, M i) →ₗ[R] ⨂[R] i, N i) :=
  LinearEquiv.ofBijective piTensorHomMap piTensorHomMap_bijective

/-- The equivalence acts as the comparison map it is built from. -/
theorem piTensorHomEquiv_apply (x : ⨂[R] i, M i →ₗ[R] N i) :
    piTensorHomEquiv R M N x = piTensorHomMap x :=
  (rfl)

/-- The equivalence and the comparison map have the same underlying function. -/
theorem coe_piTensorHomEquiv :
    ⇑(piTensorHomEquiv R M N) = ⇑(piTensorHomMap (R := R) (s := M) (t := N)) :=
  (rfl)

/-- On a pure tensor of linear maps the equivalence is `PiTensorProduct.map`. -/
@[simp]
theorem piTensorHomEquiv_tprod (f : ∀ i, M i →ₗ[R] N i) :
    piTensorHomEquiv R M N (tprod R f) = map f := by
  rw [piTensorHomEquiv_apply, piTensorHomMap_tprod_eq_map]

/-- The inverse of the equivalence takes the factorwise map back to the pure tensor. -/
@[simp]
theorem piTensorHomEquiv_symm_map (f : ∀ i, M i →ₗ[R] N i) :
    (piTensorHomEquiv R M N).symm (map f) = tprod R f :=
  (LinearEquiv.symm_apply_eq _).mpr (piTensorHomEquiv_tprod f).symm

end Free

section End

variable [Finite ι] [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- **The equivalence is multiplicative on pure tensors of endomorphisms**: composing factorwise
and then comparing is comparing and then composing. This is what makes the identification usable
on the subalgebras of `End (⨂ᵢ Mᵢ)` that Schur-Weyl duality is about. -/
theorem piTensorHomEquiv_tprod_comp_tprod (f g : ∀ i, M i →ₗ[R] M i) :
    piTensorHomEquiv R M M (tprod R fun i => f i ∘ₗ g i) =
      piTensorHomEquiv R M M (tprod R f) ∘ₗ piTensorHomEquiv R M M (tprod R g) := by
  simp [map_comp]

end End

end PiTensorProduct
