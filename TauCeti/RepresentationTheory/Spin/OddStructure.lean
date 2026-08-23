/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.OddSplitting
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.RepresentationTheory.Spin.Structure
-- Non-public: the central idempotents of a simple ring, the simplicity of a matrix algebra, and
-- the finite-dimensional injectivity criterion are all used only inside proofs.
import TauCeti.RingTheory.CentralIdempotent
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The structure theorem for an odd-dimensional Clifford algebra

Over a separably closed field of characteristic not two, the Clifford algebra of a nondegenerate
quadratic form on a space of dimension `2 * l + 1` is a **product of two matrix algebras**,

`CliffordAlgebra Q ≃ₐ[F] M_{2^l}(F) × M_{2^l}(F)`.

Two results already in place bracket this statement, and the file supplies what joins them. The
volume element of an orthogonal basis of odd length is central, odd, and squares to a nonzero
scalar, so after rescaling it splits the algebra as two copies of its even subalgebra
(`CliffordAlgebra.nonempty_algEquiv_even_prod_of_isSepClosed`); and the Fock action of a
polarization is onto the endomorphism algebra of the spinor module `S = ⋀·W`
(`TauCeti.spinAction_surjective`), which in dimension `2 * l + 1` has dimension `2 ^ l`. What was
missing was the identification of the even subalgebra itself with `M_{2^l}(F)`, and that is the
substance here.

The argument avoids reducing an odd-dimensional form to an even-dimensional one. Write
`A = even Q`, so that the splitting is a surjection `A × A ↠ M_{2^l}(F)` obtained by following it
with the Fock action. The image of `(1, 0)` is a central idempotent of a simple ring, hence `0` or
`1` (`TauCeti.centralIdempotents_eq_pair`), and in either case one of the two coordinate maps
`a ↦ φ (a, 0)`, `a ↦ φ (0, a)` is already a surjective algebra map `A →ₐ[F] M_{2^l}(F)`: that is
`TauCeti.exists_algHom_surjective_of_prod` below. A dimension count closes it. The splitting gives
`2 · dim A = dim (CliffordAlgebra Q) = 2 ^ (2 * l + 1)`, so `dim A = 2 ^ l · 2 ^ l` is the dimension
of the target and the surjection is injective as well.

The nondegenerate anisotropic orthogonal basis that the splitting consumes comes from
`QuadraticMap.Nondegenerate.exists_list_pairwise_isOrtho`.

The isomorphisms are not canonical — they depend on a choice of orthogonal basis, of polarization,
and of a basis of the spinor module — so the statements are `Nonempty`, as the even-dimensional
`CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul` is.

## Main results

* `TauCeti.exists_algHom_surjective_of_prod`: a surjection of algebras `A × A ↠ B` onto a simple
  ring restricts to a surjection along one of the two coordinates.
* `CliffordAlgebra.nonempty_algEquiv_even_prod_of_odd_finrank`: over a separably closed field, a
  nondegenerate form of odd dimension splits its Clifford algebra as two copies of the even
  subalgebra.
* `CliffordAlgebra.nonempty_even_algEquiv_matrix_of_finrank_eq_two_mul_add_one`: **the even
  subalgebra is a matrix algebra** `M_{2^l}(F)` in dimension `2 * l + 1`.
* `CliffordAlgebra.nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one`: **the structure
  theorem in odd dimension**, `CliffordAlgebra Q ≃ₐ[F] M_{2^l}(F) × M_{2^l}(F)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Chapter I,
  Theorem 4.3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1, Proposition 20.15
  and the discussion of the odd case following it.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The odd-dimensional case".
-/

public section

open CliffordAlgebra Module QuadraticMap

namespace TauCeti

universe u v

/-! ### A surjection onto a simple ring from a product of two copies of an algebra -/

section ProdSurjection

variable {F A B : Type*} [CommRing F] [Ring A] [Algebra F A] [Ring B] [Algebra F B]

/-- The images of the two coordinate units of `A × A` add up to the unit of `B`. -/
private theorem map_one_zero_add_map_zero_one (φ : (A × A) →ₐ[F] B) :
    φ (1, 0) + φ (0, 1) = 1 := by
  have hone : ((1, 0) + (0, 1) : A × A) = 1 := by simp [Prod.ext_iff]
  rw [← map_add, hone, map_one]

/-- The coordinate map `a ↦ φ (a, 0)` attached to an algebra map out of `A × A`, packaged as an
algebra map once the image of `(1, 0)` is known to be the unit. It is multiplicative and linear for
every `φ`; unitality is exactly the hypothesis. -/
private def prodFirstAlgHom (φ : (A × A) →ₐ[F] B) (hu : φ (1, 0) = 1) : A →ₐ[F] B where
  toFun a := φ (a, 0)
  map_one' := hu
  map_mul' a a' := by rw [← map_mul]; congr 1; simp
  map_zero' := map_zero φ
  map_add' a a' := by rw [← map_add]; congr 1; simp
  commutes' r := by
    have hr : ((algebraMap F A r : A), (0 : A)) = algebraMap F (A × A) r * (1, 0) := by
      simp [Prod.algebraMap_apply]
    rw [hr, map_mul, AlgHom.commutes, hu, mul_one]

/-- The first coordinate map is what its name says: `a ↦ φ (a, 0)`. -/
private theorem prodFirstAlgHom_apply (φ : (A × A) →ₐ[F] B) (hu : φ (1, 0) = 1) (a : A) :
    prodFirstAlgHom φ hu a = φ (a, 0) := (rfl)

/-- If the image of `(1, 0)` is the unit then the first coordinate map is surjective as soon as `φ`
is: the image of `(0, 1)` is then complementary to `1`, so it vanishes, and with it the whole
second coordinate. -/
private theorem prodFirstAlgHom_surjective (φ : (A × A) →ₐ[F] B) (hu : φ (1, 0) = 1)
    (hφ : Function.Surjective φ) : Function.Surjective (prodFirstAlgHom φ hu) := by
  have hw : φ (0, 1) = 0 := by
    have hsum := map_one_zero_add_map_zero_one φ
    rw [hu] at hsum
    simpa using hsum
  intro b
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := hφ b
  refine ⟨a₁, ?_⟩
  have hsplit : ((a₁, a₂) : A × A) = (a₁, 0) + (0, a₂) * (0, 1) := by simp
  rw [prodFirstAlgHom_apply, hsplit, map_add, map_mul, hw, mul_zero, add_zero]

/-- **A surjection onto a simple ring from a product of two copies of an algebra factors through a
coordinate.** The image of `(1, 0)` is a central idempotent of `B`, hence `0` or `1`; whichever it
is, one of the two coordinate maps `a ↦ φ (a, 0)`, `a ↦ φ (0, a)` is an algebra map onto `B`.

This is the step that turns the two-block splitting of an odd-dimensional Clifford algebra into a
statement about a single block. -/
theorem exists_algHom_surjective_of_prod [IsSimpleRing B] (φ : (A × A) →ₐ[F] B)
    (hφ : Function.Surjective φ) : ∃ ψ : A →ₐ[F] B, Function.Surjective ψ := by
  -- The swap of the two factors, used to reduce the second case to the first.
  set swap : (A × A) →ₐ[F] (A × A) := (AlgHom.snd F A A).prod (AlgHom.fst F A A) with hswap
  have hidem : IsIdempotentElem (φ (1, 0)) := by
    have hsq : ((1 : A), (0 : A)) * (1, 0) = (1, 0) := by simp
    calc φ (1, 0) * φ (1, 0) = φ ((1, 0) * (1, 0)) := (map_mul φ _ _).symm
      _ = φ (1, 0) := by rw [hsq]
  have hmem : φ (1, 0) ∈ centralIdempotents B := by
    refine mem_centralIdempotents.mpr ⟨hidem, Subring.mem_center_iff.mpr fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hφ x
    rw [← map_mul, ← map_mul]
    congr 1
    simp [Prod.ext_iff]
  have hpair := centralIdempotents_eq_pair (R := B) ▸ hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
  rcases hpair with h | h
  · -- `φ (1, 0) = 0`, so `φ (0, 1) = 1` and the *second* coordinate is the surjective one.
    have hw : φ (0, 1) = 1 := by
      have hsum := map_one_zero_add_map_zero_one φ
      rwa [h, zero_add] at hsum
    have hswapone : swap (1, 0) = ((0 : A), (1 : A)) := by simp [hswap]
    have hu : (φ.comp swap) (1, 0) = 1 := by
      rw [AlgHom.comp_apply, hswapone, hw]
    refine ⟨prodFirstAlgHom (φ.comp swap) hu, prodFirstAlgHom_surjective _ hu fun b => ?_⟩
    obtain ⟨⟨a₁, a₂⟩, ha⟩ := hφ b
    exact ⟨(a₂, a₁), by simpa [hswap] using ha⟩
  · exact ⟨prodFirstAlgHom φ h, prodFirstAlgHom_surjective φ h hφ⟩

end ProdSurjection

end TauCeti

namespace CliffordAlgebra

open TauCeti

variable {F : Type u} [Field F] [NeZero (2 : F)]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-! ### The two-block splitting in odd dimension -/

/-- **A nondegenerate odd-dimensional Clifford algebra splits into two copies of its even
subalgebra**, over a separably closed field of characteristic not two. An orthogonal basis has no
isotropic member (`QuadraticMap.Nondegenerate.exists_list_pairwise_isOrtho`), so its volume element
is a central odd element with invertible square, which is what
`CliffordAlgebra.nonempty_algEquiv_even_prod_of_isSepClosed` asks for. -/
theorem nonempty_algEquiv_even_prod_of_odd_finrank [IsSepClosed F] (hQ : Q.Nondegenerate)
    (hV : Odd (finrank F V)) :
    Nonempty (CliffordAlgebra Q ≃ₐ[F] (↥(even Q) × ↥(even Q))) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  obtain ⟨l, hl, hlen, hspan, hQl⟩ := hQ.exists_list_pairwise_isOrtho
  exact nonempty_algEquiv_even_prod_of_isSepClosed hl (hlen ▸ hV) hspan hQl

/-- **The even subalgebra is half the Clifford algebra in odd dimension**: the two-block splitting
is an isomorphism onto a product of two copies of it, so its dimension is `2 ^ l · 2 ^ l` when the
quadratic space has dimension `2 * l + 1`. -/
theorem finrank_even_of_finrank_eq_two_mul_add_one [IsSepClosed F] {l : ℕ} (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * l + 1) : finrank F ↥(even Q) = 2 ^ l * 2 ^ l := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  obtain ⟨e⟩ := nonempty_algEquiv_even_prod_of_odd_finrank hQ (hV ▸ ⟨l, by ring⟩)
  have hCl : finrank F (CliffordAlgebra Q) = 2 * (2 ^ l * 2 ^ l) := by
    rw [CliffordAlgebra.finrank_eq_two_pow, hV, pow_succ, two_mul l, pow_add]
    ring
  have hsplit : finrank F (CliffordAlgebra Q) = finrank F ↥(even Q) + finrank F ↥(even Q) := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod]
  omega

/-! ### The structure theorem in odd dimension -/

variable [IsSepClosed F]

/-- **The even subalgebra of an odd-dimensional Clifford algebra is a matrix algebra.** The Fock
action of a polarization is onto the endomorphism algebra of the spinor module, of dimension
`2 ^ l`; composed with the two-block splitting it becomes a surjection from a product of two copies
of `even Q`, which `TauCeti.exists_algHom_surjective_of_prod` turns into a surjection out of a
single copy. Both sides have dimension `2 ^ l · 2 ^ l`, so that surjection is an isomorphism. -/
theorem nonempty_even_algEquiv_matrix_of_finrank_eq_two_mul_add_one {l : ℕ}
    (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * l + 1) :
    Nonempty (↥(even Q) ≃ₐ[F] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  have _ : Nonempty (Fin (2 ^ l)) := ⟨⟨0, Nat.two_pow_pos l⟩⟩
  -- The Fock action of a polarization, read in a basis of the spinor module.
  set P := SpinPolarizationData.ofNondegenerate Q hQ
  have hS : finrank F (ExteriorAlgebra F P.W) = 2 ^ l := by
    rw [TauCeti.ExteriorAlgebra.finrank_eq_two_pow, P.finrank_W_of_finrank_eq_two_mul_add_one hV]
  set toMatrix := Algebra.endAlgEquivMatrix F (ExteriorAlgebra F P.W) hS
  set π : CliffordAlgebra Q →ₐ[F] Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F :=
    (toMatrix : Module.End F (ExteriorAlgebra F P.W) ≃ₐ[F] _).toAlgHom.comp (spinAction Q P)
  have hπsurj : Function.Surjective π :=
    toMatrix.surjective.comp (spinAction_surjective P)
  -- Transport it along the two-block splitting and drop one block.
  obtain ⟨e⟩ := nonempty_algEquiv_even_prod_of_odd_finrank hQ (hV ▸ ⟨l, by ring⟩)
  obtain ⟨ψ, hψ⟩ := exists_algHom_surjective_of_prod (π.comp e.symm.toAlgHom)
    (hπsurj.comp e.symm.surjective)
  -- Equal dimensions upgrade the surjection to an isomorphism.
  have hdim : finrank F ↥(even Q) = finrank F (Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F) := by
    rw [finrank_even_of_finrank_eq_two_mul_add_one hQ hV, Module.finrank_matrix]
    simp
  exact ⟨AlgEquiv.ofBijective ψ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ψ.toLinearMap) hdim).2 hψ,
      hψ⟩⟩

/-- **The structure theorem in odd dimension**: over a separably closed field of characteristic not
two, the Clifford algebra of a nondegenerate quadratic form on a space of dimension `2 * l + 1` is
the product of two copies of the matrix algebra `M_{2^l}(F)`.

This is the odd-dimensional companion of
`CliffordAlgebra.nonempty_algEquiv_matrix_of_finrank_eq_two_mul`, and the two blocks are not an
artefact of the proof: the volume element is central here, so the algebra is not simple, whereas in
even dimension it is (`TauCeti.SpinPolarizationData.isSimpleRing_cliffordAlgebra`). -/
theorem nonempty_algEquiv_matrix_prod_of_finrank_eq_two_mul_add_one {l : ℕ}
    (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * l + 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[F]
      (Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F × Matrix (Fin (2 ^ l)) (Fin (2 ^ l)) F)) := by
  have _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  obtain ⟨e⟩ := nonempty_algEquiv_even_prod_of_odd_finrank hQ (hV ▸ ⟨l, by ring⟩)
  obtain ⟨f⟩ := nonempty_even_algEquiv_matrix_of_finrank_eq_two_mul_add_one hQ hV
  exact ⟨e.trans (f.prodCongr f)⟩

end CliffordAlgebra
