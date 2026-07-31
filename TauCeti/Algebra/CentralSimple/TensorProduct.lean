/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.Central.TensorProduct` is imported publicly, so that importing this module
-- delivers both halves of the closure statement this file advertises: the centrality instance
-- `TauCeti.Algebra.IsCentral.tensorProduct` as well as the simplicity instance proved here.
-- Downstream inference then recognizes `A ⊗[K] B` as central simple from this import alone (the
-- worked examples at the end of the file need Mathlib's matrix instances on top of that, which is
-- why the matrix modules stay non-public). It also re-exports `Mathlib.Algebra.Central.Basic`
-- and `Mathlib.RingTheory.TensorProduct.Basic`, which is why neither is imported again here.
public import TauCeti.Algebra.Central.TensorProduct
public import Mathlib.RingTheory.SimpleRing.Basic
-- Non-public: none of these appears in the type of an exported declaration. `Basis.ofVectorSpace`,
-- the `A`-basis `Algebra.TensorProduct.basis` of `A ⊗[K] B`, flatness and `TwoSidedIdeal.comap` are
-- used only inside proofs (the sole declaration stating a coordinate of that basis is `private`),
-- and the matrix algebras only by the worked examples at the end of the file, so downstream
-- importers of this module do not pay for any of them.
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Central simple algebras are closed under tensor product

Let `K` be a field, let `A` be a central simple `K`-algebra and let `B` be a simple `K`-algebra.
This file proves that `A ⊗[K] B` is again simple. Together with
`TauCeti.Algebra.IsCentral.tensorProduct` of `TauCeti/Algebra/Central/TensorProduct.lean`, which
says that `A ⊗[K] B` is again central as soon as `B` is, this is the statement that central simple
`K`-algebras are closed under `⊗[K]`. That closure is what lets the tensor product descend to a
multiplication on Brauer classes, and it is also the step behind base change: it is used to see
that a central simple algebra stays central simple over an extension field.

Simplicity needs no finite-dimensionality. The argument is the classical minimal-length one, and it
uses only that `A` is simple with centre `K` and that `B` is simple.

## Main results

* `TauCeti.IsSimpleRing.tensorProduct`: `A ⊗[K] B` is simple when `A` is central simple and `B` is
  simple. Only `A` is required to be central; the mirror-image statement, with `B` central and `A`
  merely simple, follows by transporting along `Algebra.TensorProduct.comm`.

This is an instance, and `TauCeti.Algebra.IsCentral.tensorProduct` is re-exported by this module, so
importing this file alone lets typeclass inference recognize `A ⊗[K] B` as a central simple
`K`-algebra whenever `A` and `B` are. With Mathlib's matrix instances that reads
`Mₘ(K) ⊗[K] Mₙ(K)` off with no glue; that is the worked example checked at the end of the file.

## Implementation notes

The minimal-length argument for simplicity is run in the coordinates of
`Algebra.TensorProduct.basis A 𝓑`, the `A`-basis of `A ⊗[K] B` attached to a `K`-basis `𝓑` of `B`.
Reading an element in these coordinates is exactly the classical step "write `x = ∑ aᵢ ⊗ bᵢ` with
the `bᵢ` linearly independent over `K`", with the Finsupp support playing the role of the length of
that expression. Multiplying by `a ⊗ₜ 1` on one side multiplies every coordinate on that same side,
which is what makes the coordinatewise bookkeeping of that argument -- the two-sided ideal of
`i₀`-th coordinates, and the support of an additive commutator -- available. On the left this is
just the generic scalar-action API: `(a ⊗ₜ 1) * x` is the module action `a • x` by Mathlib's
`smul_one_mul` (packaged as the private `tmul_one_mul_eq_smul`), and
`(Algebra.TensorProduct.basis A 𝓑).repr` is `A`-linear. The right-hand
version is a statement in its own right, the private `basis_repr_mul_tmul_one`, and it is where it
matters that the coordinates are taken with respect to a basis of `B` over the *base* field: that
is what lets the scalars pass through `a`.

Simplicity is then the classical minimal-length argument: given a nonzero two-sided ideal
`I`, pick a nonzero `y ∈ I` with as few nonzero coordinates as possible; after rescaling one
coordinate to `1` (which is where simplicity of `A` is used), minimality forces every additive
commutator `(a ⊗ₜ 1) * y - y * (a ⊗ₜ 1)` to vanish, so `y = 1 ⊗ₜ b` by
`TauCeti.Algebra.TensorProduct.forall_commute_tmul_one_iff`; simplicity of `B` then pushes `1`
into `I`.

Both appeals to simplicity in `TauCeti.IsSimpleRing.tensorProduct` are made by exhibiting a
two-sided ideal that is nonzero, hence everything: on the `A` side the `i₀`-th coordinates of the
elements of a two-sided ideal `I` supported in a fixed finite set, built as a `TwoSidedIdeal.mk'`,
and on the `B` side the `c : B` with `1 ⊗ₜ c ∈ I`, which is `I.comap` along
`Algebra.TensorProduct.includeRight`. That is how `1` enters `I`; phrasing the argument this way
avoids ever expanding `1` as an explicit sum `∑ uⱼ a vⱼ`.

## References

This is the simplicity half of the **Tensor product of central simple is central simple** bullet of
Layer 4 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
That bullet also asks for `finrank K (A ⊗ B) = finrank K A * finrank K B`, which needs nothing new
here: it is Mathlib's `Module.finrank_tensorProduct`, applicable to `A ⊗[K] B` as it stands. See
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12, and P. Gille, T. Szamuely, *Central Simple
Algebras and Galois Cohomology*, Chapter 2.
-/

public section

open Module

open scoped TensorProduct

namespace TauCeti

namespace Algebra.TensorProduct

section Coordinates

variable {K A B ι : Type*} [CommSemiring K] [Semiring A] [Semiring B] [Algebra K A]
  [Algebra K B]

/-- Left multiplication by `a ⊗ₜ 1` on `A ⊗[K] B` is the left `A`-module action, the one that
`Algebra.TensorProduct.basis` is a basis for.

This is Mathlib's `smul_one_mul`, available because `Algebra.TensorProduct.isScalarTower_right`
makes `A ⊗[K] B` a scalar tower over `A`; all this adds is the identification of `a • 1` with
`a ⊗ₜ 1`. (`Algebra.smul_def` is not available here: `A` is not assumed commutative, so there is no
`Algebra A (A ⊗[K] B)` instance.)

`private`: it has no use outside the simplicity proof in this file. With it in the simp set, the
coordinates of `(a ⊗ₜ 1) * x` are already normalized by the generic scalar-action lemmas
(`map_smul`, `Finsupp.smul_apply`, `smul_eq_mul`), so no left-handed coordinate lemma is needed. -/
@[simp]
private theorem tmul_one_mul_eq_smul (a : A) (x : A ⊗[K] B) : (a ⊗ₜ[K] (1 : B)) * x = a • x := by
  rw [← smul_one_mul a x, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

variable (𝓑 : Basis ι K B)

/-- Multiplying by `a ⊗ₜ 1` on the right multiplies each coordinate of `x` by `a` on the right.

`private`: like `tmul_one_mul_eq_smul` it serves only the simplicity proof in this file. Unlike the
left-handed statement it is not an instance of the generic scalar-action API, since right
multiplication is not the module action `Algebra.TensorProduct.basis` is a basis for. -/
@[simp]
private theorem basis_repr_mul_tmul_one (a : A) (x : A ⊗[K] B) (j : ι) :
    (Algebra.TensorProduct.basis A 𝓑).repr (x * (a ⊗ₜ[K] (1 : B))) j =
      (Algebra.TensorProduct.basis A 𝓑).repr x j * a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a' b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    rw [mul_assoc, mul_assoc, Algebra.commutes]
  | add x y hx hy => rw [add_mul, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply,
      add_mul]

end Coordinates

end Algebra.TensorProduct

namespace IsSimpleRing

variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

variable (K A B) in
/-- **The tensor product of a central simple `K`-algebra with a simple `K`-algebra is simple.**
Together with `TauCeti.Algebra.IsCentral.tensorProduct` this says that central simple `K`-algebras
are closed under `⊗[K]`.

No finite-dimensionality is needed on either side. -/
instance tensorProduct [Algebra.IsCentral K A] [IsSimpleRing A] [IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  classical
  have : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left K A B
      (FaithfulSMul.algebraMap_injective K B)
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  rw [or_iff_not_imp_left, ← I.one_mem_iff]
  intro hI
  obtain ⟨ι, 𝓑⟩ : Σ ι : Type _, Basis ι K B := ⟨_, Basis.ofVectorSpace K B⟩
  obtain ⟨x, hxI, hx0 : x ≠ 0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  have hex : ∃ n : ℕ, ∃ y ∈ I, y ≠ 0 ∧
      ((Algebra.TensorProduct.basis A 𝓑).repr y).support.card = n := ⟨_, x, hxI, hx0, rfl⟩
  obtain ⟨y₀, hy₀I, hy₀0, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ I,
      ((Algebra.TensorProduct.basis A 𝓑).repr y).support.card < Nat.find hex → y = 0 := by
    intro y hy hlt
    by_contra h0
    exact Nat.find_min hex hlt ⟨y, hy, h0, rfl⟩
  set S := ((Algebra.TensorProduct.basis A 𝓑).repr y₀).support
  obtain ⟨i₀, hi₀⟩ : S.Nonempty := Finsupp.support_nonempty_iff.mpr (by simpa using hy₀0)
  -- The `i₀`-th coordinates of the elements of `I` supported on `S` form a two-sided ideal of `A`.
  set carrier : Set A :=
    {a | ∃ y ∈ I, (∀ j ∉ S, (Algebra.TensorProduct.basis A 𝓑).repr y j = 0) ∧
      (Algebra.TensorProduct.basis A 𝓑).repr y i₀ = a}
  have hzero : (0 : A) ∈ carrier := ⟨0, I.zero_mem, by simp, by simp⟩
  have hadd : ∀ {a a' : A}, a ∈ carrier → a' ∈ carrier → a + a' ∈ carrier := by
    rintro _ _ ⟨y, hy, hys, rfl⟩ ⟨z, hz, hzs, rfl⟩
    exact ⟨y + z, I.add_mem hy hz, fun j hj => by simp [hys j hj, hzs j hj], by simp⟩
  have hneg : ∀ {a : A}, a ∈ carrier → -a ∈ carrier := by
    rintro _ ⟨y, hy, hys, rfl⟩
    exact ⟨-y, I.neg_mem hy, fun j hj => by simp [hys j hj], by simp⟩
  have hmulleft : ∀ {a a' : A}, a' ∈ carrier → a * a' ∈ carrier := by
    rintro a _ ⟨y, hy, hys, rfl⟩
    -- The left-hand coordinates need no lemma of their own: `(a ⊗ₜ 1) * y` is `a • y`, and
    -- `(Algebra.TensorProduct.basis A 𝓑).repr` is `A`-linear, so `simp` does the bookkeeping.
    exact ⟨(a ⊗ₜ[K] (1 : B)) * y, I.mul_mem_left _ _ hy,
      fun j hj => by simp [hys j hj], by simp⟩
  have hmulright : ∀ {a a' : A}, a ∈ carrier → a * a' ∈ carrier := by
    rintro _ a' ⟨y, hy, hys, rfl⟩
    exact ⟨y * (a' ⊗ₜ[K] (1 : B)), I.mul_mem_right _ _ hy,
      fun j hj => by rw [Algebra.TensorProduct.basis_repr_mul_tmul_one, hys j hj, zero_mul],
      Algebra.TensorProduct.basis_repr_mul_tmul_one ..⟩
  obtain ⟨y, hyI, hyS, hy1⟩ : (1 : A) ∈ carrier := by
    have hne : (Algebra.TensorProduct.basis A 𝓑).repr y₀ i₀ ≠ 0 := Finsupp.mem_support_iff.mp hi₀
    have hmem : (Algebra.TensorProduct.basis A 𝓑).repr y₀ i₀ ∈ carrier :=
      ⟨y₀, hy₀I, fun j hj => Finsupp.notMem_support_iff.mp hj, rfl⟩
    have := IsSimpleRing.one_mem_of_ne_zero_mem
      (TwoSidedIdeal.mk' carrier hzero hadd hneg hmulleft hmulright) hne
      ((TwoSidedIdeal.mem_mk' ..).mpr hmem)
    exact (TwoSidedIdeal.mem_mk' ..).mp this
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hy1
    exact zero_ne_one hy1
  -- Every coordinate of `y` commutes with `A`, so `y = 1 ⊗ₜ b`.
  have hcomm : ∀ a : A, Commute (a ⊗ₜ[K] (1 : B)) y := by
    intro a
    have hsupp : ((Algebra.TensorProduct.basis A 𝓑).repr
        ((a ⊗ₜ[K] (1 : B)) * y - y * (a ⊗ₜ[K] (1 : B)))).support ⊆ S.erase i₀ := by
      intro j hj
      rw [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply,
        Algebra.TensorProduct.tmul_one_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.basis_repr_mul_tmul_one] at hj
      refine Finset.mem_erase.mpr ⟨?_, not_imp_comm.mp (fun hjS => ?_) hj⟩
      · rintro rfl
        exact hj (by rw [hy1, mul_one, one_mul, sub_self])
      · rw [hyS j hjS, mul_zero, zero_mul, sub_self]
    have hz : (a ⊗ₜ[K] (1 : B)) * y - y * (a ⊗ₜ[K] (1 : B)) = 0 :=
      hmin _ (I.sub_mem (I.mul_mem_left _ _ hyI) (I.mul_mem_right _ _ hyI))
        (lt_of_le_of_lt (Finset.card_le_card hsupp)
          (hcard ▸ Finset.card_erase_lt_of_mem hi₀))
    exact sub_eq_zero.mp hz
  obtain ⟨b, rfl⟩ := Algebra.TensorProduct.forall_commute_tmul_one_iff.mp hcomm
  have hb : b ≠ 0 := by rintro rfl; exact hy0 (by simp)
  -- The `c : B` with `1 ⊗ₜ c ∈ I` form a two-sided ideal of `B`, namely the preimage of `I` along
  -- `Algebra.TensorProduct.includeRight`; it contains `b ≠ 0`, hence it is everything.
  have honeB : (1 : B) ∈
      I.comap (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B) :=
    IsSimpleRing.one_mem_of_ne_zero_mem _ hb ((TwoSidedIdeal.mem_comap _).mpr (by simpa using hyI))
  rw [TwoSidedIdeal.mem_comap] at honeB
  simpa [Algebra.TensorProduct.one_def] using honeB

end IsSimpleRing

section Examples

variable {K : Type*} [Field K] (m n : ℕ)

example :
    IsSimpleRing
      (Matrix (Fin (m + 1)) (Fin (m + 1)) K ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
  inferInstance

example :
    Algebra.IsCentral K
      (Matrix (Fin (m + 1)) (Fin (m + 1)) K ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
  inferInstance

end Examples

end TauCeti
