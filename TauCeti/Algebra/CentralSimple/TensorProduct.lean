/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Central simple algebras are closed under tensor product

Let `K` be a field, let `A` be a central simple `K`-algebra and let `B` be a simple `K`-algebra.
This file proves that `A ⊗[K] B` is again simple, and that it is again central as soon as `B` is.
Mathlib has the two *converse* centrality statements (`Algebra.IsCentral.left_of_tensor_of_field`
and `Algebra.IsCentral.right_of_tensor_of_field`), but neither the forward centrality statement nor
simplicity, so central simple algebras were not yet known to be closed under `⊗[K]`. That closure
is what lets the tensor product descend to a multiplication on Brauer classes, and it is also the
step behind base change: it is used to see that a central simple algebra stays central simple over
an extension field.

Neither theorem needs finite-dimensionality. The argument is the classical minimal-length one, and
it uses only that `A` is simple with centre `K` and that `B` is simple.

## Main results

* `TauCeti.forall_commute_tmul_one_iff`: for `A` central over `K`, the centralizer of `A ⊗ 1` in
  `A ⊗[K] B` is exactly `1 ⊗ B`. This is the engine of both theorems below.
* `TauCeti.isSimpleRing_tensorProduct`: `A ⊗[K] B` is simple when `A` is central simple and `B` is
  simple. Only `A` is required to be central; the mirror-image statement, with `B` central and `A`
  merely simple, follows by transporting along `Algebra.TensorProduct.comm`.
* `TauCeti.isCentral_tensorProduct`: `A ⊗[K] B` is central when both factors are.

Both are instances, so `Mₘ(K) ⊗[K] Mₙ(K)` is recognized as a central simple `K`-algebra by
typeclass inference; that is the worked example checked at the end of the file.

## Implementation notes

The coordinates used throughout are those of `Algebra.TensorProduct.basis A 𝓑`, the `A`-basis of
`A ⊗[K] B` attached to a `K`-basis `𝓑` of `B`. Reading an element in these coordinates is exactly
the classical step "write `x = ∑ aᵢ ⊗ bᵢ` with the `bᵢ` linearly independent over `K`", with the
Finsupp support playing the role of the length of that expression, and
`TauCeti.basis_repr_tmul_one_mul` and `TauCeti.basis_repr_mul_tmul_one` record that multiplying by
`a ⊗ₜ 1` on one side multiplies every coordinate on that same side.

Both appeals to simplicity in `TauCeti.isSimpleRing_tensorProduct` are made by exhibiting a
`TwoSidedIdeal.mk'`: the `i₀`-th coordinates of the elements of a two-sided ideal `I` supported in a
fixed finite set form a two-sided ideal of `A`, and the `c : B` with `1 ⊗ₜ c ∈ I` form a two-sided
ideal of `B`. Both ideals are nonzero, hence everything, which is how `1` enters `I`; phrasing the
argument this way avoids ever expanding `1` as an explicit sum `∑ uⱼ a vⱼ`.
-/

public section

open Module

open scoped TensorProduct

namespace TauCeti

section Coordinates

variable {K A B ι : Type*} [CommSemiring K] [Semiring A] [Semiring B] [Algebra K A]
  [Algebra K B]

/-- Left multiplication by `a ⊗ₜ 1` on `A ⊗[K] B` is the left `A`-module action, the one that
`Algebra.TensorProduct.basis` is a basis for. -/
theorem tmul_one_mul_eq_smul (a : A) (x : A ⊗[K] B) : (a ⊗ₜ[K] (1 : B)) * x = a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a' b => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp [mul_add, hx, hy]

variable (𝓑 : Basis ι K B)

/-- Multiplying by `a ⊗ₜ 1` on the left multiplies each coordinate of `x` by `a` on the left. -/
theorem basis_repr_tmul_one_mul (a : A) (x : A ⊗[K] B) (j : ι) :
    (Algebra.TensorProduct.basis A 𝓑).repr ((a ⊗ₜ[K] (1 : B)) * x) j =
      a * (Algebra.TensorProduct.basis A 𝓑).repr x j := by
  rw [tmul_one_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Multiplying by `a ⊗ₜ 1` on the right multiplies each coordinate of `x` by `a` on the right.
This is where the coordinates being taken with respect to a basis of `B` over the *base* field
matters: it lets the scalars pass through `a`. -/
theorem basis_repr_mul_tmul_one (a : A) (x : A ⊗[K] B) (j : ι) :
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

/-- An element of `A ⊗[K] B` all of whose coordinates are scalars lies in `1 ⊗ B`. -/
theorem exists_one_tmul_of_repr_mem_range {x : A ⊗[K] B}
    (h : ∀ j, (Algebra.TensorProduct.basis A 𝓑).repr x j ∈ Set.range (algebraMap K A)) :
    ∃ b : B, x = 1 ⊗ₜ[K] b := by
  choose k hk using h
  refine ⟨((Algebra.TensorProduct.basis A 𝓑).repr x).sum fun j _ => k j • 𝓑 j, ?_⟩
  rw [Finsupp.sum, TensorProduct.tmul_sum]
  conv_lhs =>
    rw [← (Algebra.TensorProduct.basis A 𝓑).linearCombination_repr x,
      Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.basis_apply, ← hk j, algebraMap_smul, TensorProduct.tmul_smul]

end Coordinates

section Field

variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

/-- **The centralizer of `A ⊗ 1` in `A ⊗[K] B` is `1 ⊗ B`**, for `A` a central `K`-algebra: an
element of `A ⊗[K] B` commutes with every `a ⊗ₜ 1` exactly when it is of the form `1 ⊗ₜ b`.

Centrality of `A` is what forces the coordinates of such an element to be scalars; without it the
centralizer is `Z(A) ⊗ B` and can be strictly larger. -/
theorem forall_commute_tmul_one_iff [Algebra.IsCentral K A] {x : A ⊗[K] B} :
    (∀ a : A, Commute (a ⊗ₜ[K] (1 : B)) x) ↔ ∃ b : B, x = 1 ⊗ₜ[K] b := by
  refine ⟨fun h => exists_one_tmul_of_repr_mem_range (Basis.ofVectorSpace K B) fun j => ?_, ?_⟩
  · have hmem : (Algebra.TensorProduct.basis A (Basis.ofVectorSpace K B)).repr x j ∈
        Subalgebra.center K A := by
      rw [Subalgebra.mem_center_iff]
      intro a
      have := congrArg
        (fun y => (Algebra.TensorProduct.basis A (Basis.ofVectorSpace K B)).repr y j) (h a).eq
      simpa [basis_repr_tmul_one_mul, basis_repr_mul_tmul_one] using this
    obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff K).mp hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨b, rfl⟩ a
    simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]

variable (K A B) in
/-- **The tensor product of two central `K`-algebras is central.** Mathlib has the two converses
(`Algebra.IsCentral.left_of_tensor_of_field` and `Algebra.IsCentral.right_of_tensor_of_field`);
this is the forward implication. -/
instance isCentral_tensorProduct [Nontrivial A] [Algebra.IsCentral K A] [Algebra.IsCentral K B] :
    Algebra.IsCentral K (A ⊗[K] B) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    obtain ⟨b, rfl⟩ := forall_commute_tmul_one_iff.mp fun a => hx _
    have hbc : b ∈ Subalgebra.center K B := by
      rw [Subalgebra.mem_center_iff]
      intro c
      have h := hx ((1 : A) ⊗ₜ[K] c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h
      exact Algebra.TensorProduct.includeRight_injective
        (FaithfulSMul.algebraMap_injective K A) h
    obtain ⟨k, rfl⟩ := (Algebra.IsCentral.mem_center_iff K).mp hbc
    rw [Algebra.mem_bot]
    exact ⟨k, by simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]⟩

variable (K A B) in
/-- **The tensor product of a central simple `K`-algebra with a simple `K`-algebra is simple.**
Together with `TauCeti.isCentral_tensorProduct` this says that central simple `K`-algebras are
closed under `⊗[K]`.

No finite-dimensionality is needed on either side. Given a nonzero two-sided ideal `I`, pick a
nonzero `y ∈ I` with as few nonzero coordinates as possible with respect to a `K`-basis of `B`;
after rescaling one coordinate to `1` (which is where simplicity of `A` is used), minimality forces
every additive commutator `(a ⊗ₜ 1) * y - y * (a ⊗ₜ 1)` to vanish, so `y = 1 ⊗ₜ b` by
`TauCeti.forall_commute_tmul_one_iff`; simplicity of `B` then pushes `1` into `I`. -/
instance isSimpleRing_tensorProduct [Algebra.IsCentral K A] [IsSimpleRing A] [IsSimpleRing B] :
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
    exact ⟨(a ⊗ₜ[K] (1 : B)) * y, I.mul_mem_left _ _ hy,
      fun j hj => by rw [basis_repr_tmul_one_mul, hys j hj, mul_zero],
      basis_repr_tmul_one_mul ..⟩
  have hmulright : ∀ {a a' : A}, a ∈ carrier → a * a' ∈ carrier := by
    rintro _ a' ⟨y, hy, hys, rfl⟩
    exact ⟨y * (a' ⊗ₜ[K] (1 : B)), I.mul_mem_right _ _ hy,
      fun j hj => by rw [basis_repr_mul_tmul_one, hys j hj, zero_mul],
      basis_repr_mul_tmul_one ..⟩
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
      rw [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply, basis_repr_tmul_one_mul,
        basis_repr_mul_tmul_one] at hj
      refine Finset.mem_erase.mpr ⟨?_, not_imp_comm.mp (fun hjS => ?_) hj⟩
      · rintro rfl
        exact hj (by rw [hy1, mul_one, one_mul, sub_self])
      · rw [hyS j hjS, mul_zero, zero_mul, sub_self]
    have hz : (a ⊗ₜ[K] (1 : B)) * y - y * (a ⊗ₜ[K] (1 : B)) = 0 :=
      hmin _ (I.sub_mem (I.mul_mem_left _ _ hyI) (I.mul_mem_right _ _ hyI))
        (lt_of_le_of_lt (Finset.card_le_card hsupp)
          (hcard ▸ Finset.card_erase_lt_of_mem hi₀))
    exact sub_eq_zero.mp hz
  obtain ⟨b, rfl⟩ := forall_commute_tmul_one_iff.mp hcomm
  have hb : b ≠ 0 := by rintro rfl; exact hy0 (by simp)
  -- The elements `c` of `B` with `1 ⊗ₜ c ∈ I` form a two-sided ideal of `B`, and it is nonzero.
  have hzeroB : (0 : B) ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} := by simp
  have haddB : ∀ {c c' : B}, c ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} →
      c' ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} → c + c' ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} := by
    intro c c' hc hc'
    simpa [TensorProduct.tmul_add] using I.add_mem hc hc'
  have hnegB : ∀ {c : B}, c ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} →
      -c ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} := by
    intro c hc
    simpa [TensorProduct.tmul_neg] using I.neg_mem hc
  have hmulleftB : ∀ {c c' : B}, c' ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} →
      c * c' ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} := by
    intro c c' hc'
    simpa [Algebra.TensorProduct.tmul_mul_tmul] using I.mul_mem_left ((1 : A) ⊗ₜ[K] c) _ hc'
  have hmulrightB : ∀ {c c' : B}, c ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} →
      c * c' ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} := by
    intro c c' hc
    simpa [Algebra.TensorProduct.tmul_mul_tmul] using I.mul_mem_right _ ((1 : A) ⊗ₜ[K] c') hc
  have honeB : (1 : B) ∈ {c : B | (1 : A) ⊗ₜ[K] c ∈ I} :=
    (TwoSidedIdeal.mem_mk' ..).mp <| IsSimpleRing.one_mem_of_ne_zero_mem
      (TwoSidedIdeal.mk' _ hzeroB haddB hnegB hmulleftB hmulrightB) hb
      ((TwoSidedIdeal.mem_mk' ..).mpr hyI)
  simpa [Algebra.TensorProduct.one_def] using honeB

end Field

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
