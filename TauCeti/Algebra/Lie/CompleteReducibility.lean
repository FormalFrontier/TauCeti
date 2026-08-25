/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projection
-- Non-public: these lemmas appear only inside proofs, never in the type of an exported declaration.
import TauCeti.Algebra.Lie.Submodule.Atom
import TauCeti.Algebra.Lie.Submodule.Finrank

public section

/-!
# Complete reducibility from a single irreducible input

Weyl's complete reducibility theorem and its `sl₂` rank-one case share one and the same argument.
Only a single step of that argument is representation-theoretic; everything else is formal, and this
file isolates the formal part so that it is proved once.

The input is `TauCeti.HasInvariantOutsideIrreducible K L`: whenever `L` carries a
finite-dimensional module `M` into a proper **irreducible** Lie submodule `N` and acts nontrivially
somewhere on `M`, the module `M` has a nonzero `L`-invariant vector outside `N`. In practice this is
supplied by a Casimir operator, which is injective on a nontrivial irreducible while its range lies
in `N`, so it cannot be injective on `M`; its kernel is then the invariant vector. That is the only
place where the base field, the Lie algebra, and the choice of Casimir enter.

From that input alone this file derives, over an arbitrary field:

* the same conclusion with **no irreducibility hypothesis** on `N`
  (`TauCeti.HasInvariantOutsideIrreducible.exists_invariant_notMem`), by an induction on
  `finrank K M` that peels a nonzero proper `W ≤ N` off, first in the quotient `M ⧸ W` and then in
  the span `W + K v₀`;
* an `L`-equivariant projection of `M` onto an arbitrary nonzero Lie submodule
  (`TauCeti.HasInvariantOutsideIrreducible.exists_equivariant_projection`), by running the previous
  step inside the endomorphism module `M →ₗ[K] M`;
* **complete reducibility** (`TauCeti.HasInvariantOutsideIrreducible.exists_isCompl`): every Lie
  submodule of a finite-dimensional module has a complement.

## The two endomorphism submodules

The reduction to the irreducible input runs inside `M →ₗ[K] M` and turns on the pair of Lie
submodules `TauCeti.homVanishingOn N ≤ TauCeti.homScalarOn N`: endomorphisms carrying `M` into `N`
and acting on `N` by a scalar, respectively by the scalar `0`. Bracketing an element of `L` with an
element of `homScalarOn N` lands in `homVanishingOn N`
(`TauCeti.lie_mem_comap_homVanishingOn`), so `L` carries `homScalarOn N` into
`homVanishingOn N`, which is proper as soon as `N ≠ ⊥` because a linear projection onto `N` acts
there by the scalar `1`. An invariant vector outside it is, after rescaling, an equivariant
projection, and its kernel is the complement.

## Main definitions

* `TauCeti.homScalarOn` and `TauCeti.homVanishingOn`: the two Lie submodules of `M →ₗ[K] M` above.
* `TauCeti.HasInvariantOutsideIrreducible`: the irreducible input described above.

## Main results

* `TauCeti.exists_isCompl_of_equivariant_projection`: a Lie submodule admitting an `L`-equivariant
  projection is a direct summand. This needs no finiteness and no field, only a commutative ring.
* `TauCeti.HasInvariantOutsideIrreducible.exists_invariant_notMem`: the irreducibility hypothesis
  may be dropped.
* `TauCeti.HasInvariantOutsideIrreducible.exists_equivariant_projection`: every nonzero Lie
  submodule of a finite-dimensional module admits an `L`-equivariant projection.
* `TauCeti.HasInvariantOutsideIrreducible.exists_isCompl`: **complete reducibility.**

## Roadmap

Layer 5 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` proves Weyl's theorem
for a semisimple Lie algebra through the Casimir element of `U(L)`, using the formal reduction
isolated here. The current `TauCeti/Algebra/Lie/Sl2/CompleteReducibility.lean` also instantiates
this reduction using the concrete Casimir operator of an `sl₂` triple; this differs from the
independent weight-string / primitive-vector route prescribed for Layer 0 of the roadmap.

## References

* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972],
  §6.2 and §6.3.
-/

namespace TauCeti

open LieModule Module

universe v

/-! ### Endomorphisms acting on a submodule by a scalar -/

section Hom

variable {K : Type*} [CommRing K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- The endomorphisms of `M` carrying `M` into `N` and acting on `N` by a scalar. It is a Lie
submodule of `M →ₗ[K] M` because bracketing with an element of `L` kills `N`. -/
def homScalarOn (N : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] M) where
  carrier := {φ | (∀ m, φ m ∈ N) ∧ ∃ c : K, ∀ n ∈ N, φ n = c • n}
  zero_mem' := ⟨fun m ↦ by simp, 0, fun n _ ↦ by simp⟩
  add_mem' := by
    rintro φ ψ ⟨hφ, c, hc⟩ ⟨hψ, c', hc'⟩
    exact ⟨fun m ↦ N.add_mem (hφ m) (hψ m), c + c',
      fun n hn ↦ by simp [hc n hn, hc' n hn, add_smul]⟩
  smul_mem' := by
    rintro a φ ⟨hφ, c, hc⟩
    exact ⟨fun m ↦ N.smul_mem a (hφ m), a * c, fun n hn ↦ by simp [hc n hn, mul_smul]⟩
  lie_mem := by
    rintro x φ ⟨hφ, c, hc⟩
    refine ⟨fun m ↦ ?_, 0, fun n hn ↦ ?_⟩
    · rw [LieHom.lie_apply]
      exact N.sub_mem (N.lie_mem (hφ m)) (hφ _)
    · rw [LieHom.lie_apply, hc n hn, hc _ (N.lie_mem hn), lie_smul, sub_self, zero_smul]

/-- The endomorphisms of `M` carrying `M` into `N` and killing `N`, a Lie submodule of
`TauCeti.homScalarOn` that misses every projection onto a nonzero `N`. -/
def homVanishingOn (N : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] M) where
  carrier := {φ | (∀ m, φ m ∈ N) ∧ ∀ n ∈ N, φ n = 0}
  zero_mem' := ⟨fun m ↦ by simp, fun n _ ↦ by simp⟩
  add_mem' := by
    rintro φ ψ ⟨hφ, hc⟩ ⟨hψ, hc'⟩
    exact ⟨fun m ↦ N.add_mem (hφ m) (hψ m), fun n hn ↦ by simp [hc n hn, hc' n hn]⟩
  smul_mem' := by
    rintro a φ ⟨hφ, hc⟩
    exact ⟨fun m ↦ N.smul_mem a (hφ m), fun n hn ↦ by simp [hc n hn]⟩
  lie_mem := by
    rintro x φ ⟨hφ, hc⟩
    refine ⟨fun m ↦ ?_, fun n hn ↦ ?_⟩
    · rw [LieHom.lie_apply]
      exact N.sub_mem (N.lie_mem (hφ m)) (hφ _)
    · rw [LieHom.lie_apply, hc n hn, hc _ (N.lie_mem hn), lie_zero, sub_zero]

/-- Membership in `TauCeti.homScalarOn`: land in `N`, and act on `N` by one scalar. -/
@[simp]
theorem mem_homScalarOn {N : LieSubmodule K L M} {φ : M →ₗ[K] M} :
    φ ∈ homScalarOn N ↔ (∀ m, φ m ∈ N) ∧ ∃ c : K, ∀ n ∈ N, φ n = c • n := (Iff.rfl)

/-- Membership in `TauCeti.homVanishingOn`: land in `N`, and vanish on `N`. -/
@[simp]
theorem mem_homVanishingOn {N : LieSubmodule K L M} {φ : M →ₗ[K] M} :
    φ ∈ homVanishingOn N ↔ (∀ m, φ m ∈ N) ∧ ∀ n ∈ N, φ n = 0 := (Iff.rfl)

/-- Vanishing on `N` is acting on `N` by the scalar `0`. -/
theorem homVanishingOn_le_homScalarOn (N : LieSubmodule K L M) :
    homVanishingOn (L := L) N ≤ homScalarOn N := by
  rintro φ ⟨hφ, hc⟩
  exact mem_homScalarOn.2 ⟨hφ, 0, fun n hn ↦ by rw [hc n hn, zero_smul]⟩

/-- **Bracketing an endomorphism acting scalarly on `N` with an element of `L` produces one
vanishing on `N`.** The bracket again lands in `N` and vanishes there. -/
theorem lie_mem_comap_homVanishingOn (N : LieSubmodule K L M) (x : L)
    (ψ : homScalarOn (L := L) N) :
    ⁅x, ψ⁆ ∈ (homVanishingOn N).comap (homScalarOn N).incl := by
  obtain ⟨hψ, c, hc⟩ := mem_homScalarOn.1 ψ.2
  simp only [LieSubmodule.mem_comap, LieSubmodule.incl_apply, LieSubmodule.coe_bracket]
  refine mem_homVanishingOn.2 ⟨fun m ↦ ?_, fun n hn ↦ ?_⟩
  · rw [LieHom.lie_apply]
    exact N.sub_mem (N.lie_mem (hψ m)) (hψ _)
  · rw [LieHom.lie_apply, hc n hn, hc _ (N.lie_mem hn), lie_smul, sub_self]

end Hom

/-! ### An equivariant projection splits off its image -/

section Projection

variable {K : Type*} [CommRing K]
variable {L : Type*} [LieRing L]
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M]

/-- **A Lie submodule admitting an equivariant projection is a direct summand.** If an
`L`-equivariant linear endomorphism of `M` takes values in `N` and restricts to the identity on `N`,
then `N` has a complement, namely the kernel of that endomorphism. -/
theorem exists_isCompl_of_equivariant_projection {N : LieSubmodule K L M} {ψ : M →ₗ[K] M}
    (hψmem : ∀ m, ψ m ∈ N) (hψid : ∀ n ∈ N, ψ n = n)
    (hψlie : ∀ (x : L) (m : M), ψ ⁅x, m⁆ = ⁅x, ψ m⁆) :
    ∃ N' : LieSubmodule K L M, IsCompl N N' := by
  -- `ψ` corestricted to `N` is a Lie module hom, and a projection in Mathlib's sense.
  let g : M →ₗ⁅K,L⁆ M := { __ := ψ, map_lie' := fun {x m} ↦ hψlie x m }
  let f : M →ₗ⁅K,L⁆ N := LieModuleHom.codRestrict N g hψmem
  refine ⟨f.ker, ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule, LieModuleHom.ker_toSubmodule]
  exact LinearMap.isCompl_of_proj fun n ↦ Subtype.ext (hψid n n.2)

end Projection

/-! ### The irreducible input, and the induction that removes irreducibility -/

section Invariant

variable {K : Type*} [Field K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]

variable (K L) in
/-- **The one representation-theoretic input of complete reducibility.** Whenever `L` carries a
finite-dimensional module `M` into a proper *irreducible* Lie submodule `N`, and acts nontrivially
somewhere on `M`, the module `M` has a nonzero `L`-invariant vector outside `N`.

A Casimir operator supplies this: it commutes with the action, its range lies in `N` because `L`
carries `M` into `N`, and it is injective on a nontrivial irreducible `N`, so it fails to be
surjective and hence, in finite dimension, fails to be injective; any nonzero kernel vector is
invariant and outside `N`.

`TauCeti.HasInvariantOutsideIrreducible.exists_isCompl` turns this into complete reducibility. -/
@[expose]
def HasInvariantOutsideIrreducible : Prop :=
  ∀ {M : Type v} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M],
    ∀ [FiniteDimensional K M] (N : LieSubmodule K L M), N ≠ ⊤ →
      (∀ (x : L) (m : M), ⁅x, m⁆ ∈ N) → (∃ (x : L) (m : M), ⁅x, m⁆ ≠ 0) →
      LieModule.IsIrreducible K L N → ∃ w : M, w ∉ N ∧ ∀ x : L, ⁅x, w⁆ = 0

/-- The inductive hypothesis of `TauCeti.HasInvariantOutsideIrreducible.exists_invariant_notMem`:
the conclusion for every module of dimension at most `d`. The induction changes the module, so the
bound has to be carried explicitly. -/
private def InvariantBelow (K : Type*) [Field K] (L : Type*) [LieRing L] [LieAlgebra K L]
    (d : ℕ) : Prop :=
  ∀ {M : Type v} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M],
    ∀ [FiniteDimensional K M] (N : LieSubmodule K L M), finrank K M ≤ d → N ≠ ⊤ →
      (∀ (x : L) (m : M), ⁅x, m⁆ ∈ N) → ∃ w : M, w ∉ N ∧ ∀ x : L, ⁅x, w⁆ = 0

/-- **In `M ⧸ W` the inductive hypothesis produces a vector outside `N` whose brackets land in
`W`.** This is the first half of the reducible step: the quotient by a nonzero `W ≤ N` is smaller,
so the induction applies to it, and pulling the resulting vector back along `W`-cosets turns
invariance in the quotient into `⁅L, v₀⁆ ⊆ W` upstairs. -/
private theorem exists_notMem_forall_lie_mem_of_le {d : ℕ} (ih : InvariantBelow.{v} K L d)
    {M : Type v} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    {N W : LieSubmodule K L M} [FiniteDimensional K (M ⧸ W)] (hquot : finrank K (M ⧸ W) ≤ d)
    (hN : N ≠ ⊤) (htriv : ∀ (x : L) (m : M), ⁅x, m⁆ ∈ N) (hWle : W ≤ N) :
    ∃ v₀ : M, v₀ ∉ N ∧ ∀ x : L, ⁅x, v₀⁆ ∈ W := by
  have hNq : N.map (LieSubmodule.Quotient.mk' W) ≠ ⊤ := by
    intro hcon
    refine hN ((LieSubmodule.toSubmodule_inj _ _).1 ?_)
    have hmap : Submodule.map (W : Submodule K M).mkQ (N : Submodule K M) = ⊤ := by
      have := congrArg LieSubmodule.toSubmodule hcon
      rwa [LieSubmodule.toSubmodule_map, LieSubmodule.top_toSubmodule] at this
    have hWN := (Submodule.map_mkQ_eq_top _ _).1 hmap
    rwa [sup_eq_right.2 ((LieSubmodule.toSubmodule_le_toSubmodule _ _).2 hWle)] at hWN
  obtain ⟨w, hwmem, hwinv⟩ := ih (N.map (LieSubmodule.Quotient.mk' W)) hquot hNq
    (by
      intro x q
      induction q using Quotient.inductionOn' with
      | h m => exact ⟨⁅x, m⁆, htriv x m, rfl⟩)
  obtain ⟨v₀, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W w
  refine ⟨v₀, fun hc ↦ hwmem ⟨v₀, hc, rfl⟩, fun x ↦ ?_⟩
  rw [← LieSubmodule.Quotient.mk_eq_zero]
  simpa using hwinv x

/-- **The span of a Lie submodule and one extra vector is carried into that submodule**, provided
every bracket of the extra vector already lies in it. -/
private theorem lie_mem_of_mem_sup_span_singleton {M : Type v} [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] {W : LieSubmodule K L M} {v₀ : M}
    (hv₀W : ∀ x : L, ⁅x, v₀⁆ ∈ W) (x : L) {m : M}
    (hm : m ∈ (W : Submodule K M) ⊔ Submodule.span K {v₀}) : ⁅x, m⁆ ∈ W := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rw [lie_add, lie_smul]
  exact W.add_mem (W.lie_mem hy) (W.smul_mem c (hv₀W x))

/-- **A vector of `W + K v₀` lying outside `W` lies outside `N`**, when `W ≤ N` and `v₀ ∉ N`. -/
private theorem notMem_of_mem_sup_span_singleton {M : Type v} [AddCommGroup M] [Module K M]
    {N W : Submodule K M} {v₀ p : M} (hWle : W ≤ N) (hv₀N : v₀ ∉ N)
    (hp : p ∈ W ⊔ Submodule.span K {v₀}) (hpW : p ∉ W) : p ∉ N := by
  intro hcon
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hp
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rcases eq_or_ne c 0 with rfl | hc0
  · exact hpW (by simpa [← hyz] using hy)
  · refine hv₀N ?_
    have hcv : c • v₀ ∈ N := by
      have hsub : c • v₀ = p - y := by rw [← hyz]; abel
      rw [hsub]
      exact N.sub_mem hcon (hWle hy)
    simpa [hc0] using N.smul_mem c⁻¹ hcv

/-- **A vector outside `N` whose brackets land in `W` upgrades to a genuinely invariant one.** This
is the second half of the reducible step. The span `W + K v₀` is carried into `W` by `L`, so it is a
Lie submodule; it has dimension at most `finrank W + 1`, so the induction applies to it with `W`
pulled back inside, and the vector it returns is invariant in `M` and still outside `N`. -/
private theorem exists_invariant_notMem_of_forall_lie_mem {d : ℕ} (ih : InvariantBelow.{v} K L d)
    {M : Type v} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    {N W : LieSubmodule K L M} [FiniteDimensional K W] {v₀ : M} (hWrank : finrank K W + 1 ≤ d)
    (hWle : W ≤ N) (hv₀N : v₀ ∉ N) (hv₀W : ∀ x : L, ⁅x, v₀⁆ ∈ W) :
    ∃ w : M, w ∉ N ∧ ∀ x : L, ⁅x, w⁆ = 0 := by
  let P : LieSubmodule K L M :=
    { __ := (W : Submodule K M) ⊔ Submodule.span K {v₀}
      lie_mem := fun {x m} hm ↦
        Submodule.mem_sup_left (lie_mem_of_mem_sup_span_singleton hv₀W _ hm) }
  have hPmem : ∀ m : M, m ∈ P ↔ m ∈ (W : Submodule K M) ⊔ Submodule.span K {v₀} :=
    fun _ ↦ Iff.rfl
  have hv₀P : v₀ ∈ P :=
    (hPmem _).2 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
  have hPrank : finrank K P ≤ d := by
    have hne : v₀ ≠ 0 := fun hc ↦ hv₀N (hc ▸ N.zero_mem)
    have hle := Submodule.finrank_add_le_finrank_add_finrank
      (W : Submodule K M) (Submodule.span K {v₀})
    rw [finrank_span_singleton hne] at hle
    have hP : finrank K (((W : Submodule K M) ⊔ Submodule.span K {v₀} :
        Submodule K M) : Type _) = finrank K P := by
      simpa only [P] using finrank_toSubmodule P
    have hw : finrank K ((W : Submodule K M) : Type _) = finrank K W :=
      finrank_toSubmodule W
    omega
  have : FiniteDimensional K P :=
    Submodule.finiteDimensional_sup (W : Submodule K M) (Submodule.span K {v₀})
  have hWcomap : W.comap P.incl ≠ ⊤ := by
    rw [Ne, LieSubmodule.comap_incl_eq_top]
    exact fun hc ↦ hv₀N (hWle (hc hv₀P))
  obtain ⟨p, hpmem, hpinv⟩ := ih (W.comap P.incl) hPrank hWcomap
    (fun x q ↦ lie_mem_of_mem_sup_span_singleton hv₀W x ((hPmem _).1 q.2))
  refine ⟨(p : M), notMem_of_mem_sup_span_singleton hWle hv₀N ((hPmem _).1 p.2) hpmem,
    fun x ↦ ?_⟩
  simpa only [LieSubmodule.coe_bracket, ZeroMemClass.coe_zero] using
    congrArg Subtype.val (hpinv x)

/-- **The reducible step.** If the proper submodule `N` admits a Lie submodule `W` that is neither
`⊥` nor `N`, then `M` has an invariant vector outside `N`.

The irreducible input is not used here; it enters only on the irreducible branch. -/
private theorem exists_invariant_notMem_of_ne_bot_of_ne_of_le {d : ℕ}
    (ih : InvariantBelow.{v} K L d)
    {M : Type v} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [FiniteDimensional K M] {N W : LieSubmodule K L M} (hrank : finrank K M ≤ d + 1)
    (hN : N ≠ ⊤) (htriv : ∀ (x : L) (m : M), ⁅x, m⁆ ∈ N) (hWbot : W ≠ ⊥) (hWN : W ≠ N)
    (hWle : W ≤ N) : ∃ w : M, w ∉ N ∧ ∀ x : L, ⁅x, w⁆ = 0 := by
  -- The inductive hypothesis is used twice: on the quotient `M ⧸ W`, which is strictly smaller
  -- because `W` is nonzero, to get a vector outside `N` whose brackets land in `W`; and then,
  -- through `exists_invariant_notMem_of_forall_lie_mem`, on `W + K v₀`.
  have hNlt : finrank K N < finrank K M := Submodule.finrank_lt (fun hc ↦ hN
    ((LieSubmodule.toSubmodule_inj _ _).1 (by rw [hc, LieSubmodule.top_toSubmodule])))
  have hWnt : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot K L _).2 hWbot
  have hWpos : 0 < finrank K W := finrank_pos_iff.2 hWnt
  have hWsub : (W : Submodule K M) < (N : Submodule K M) :=
    lt_of_le_of_ne ((LieSubmodule.toSubmodule_le_toSubmodule _ _).2 hWle)
      (fun hc ↦ hWN ((LieSubmodule.toSubmodule_inj _ _).1 hc))
  have hWlt : finrank K W < finrank K N := Submodule.finrank_lt_finrank_of_lt hWsub
  have hquot : finrank K (M ⧸ W) ≤ d := by
    -- There is no cross-type conversion here to justify. Mathlib *defines* the Lie-submodule
    -- quotient to be the submodule quotient, `HasQuotient M (LieSubmodule R L M)` being
    -- `⟨fun N => M ⧸ N.toSubmodule⟩` in `Mathlib/Algebra/Lie/Quotient.lean`, and `↥W` carries the
    -- submodule's own carrier. So the submodule rank identity *is* the identity for `M ⧸ W`;
    -- ascribing the type is what states it in that form.
    have hadd : finrank K (M ⧸ W) + finrank K W = finrank K M :=
      Submodule.finrank_quotient_add_finrank (W : Submodule K M)
    omega
  obtain ⟨v₀, hv₀N, hv₀W⟩ := exists_notMem_forall_lie_mem_of_le ih hquot hN htriv hWle
  exact exists_invariant_notMem_of_forall_lie_mem ih (by omega) hWle hv₀N hv₀W

/-- The inductive form of
`TauCeti.HasInvariantOutsideIrreducible.exists_invariant_notMem`, with the dimension of the ambient
module bounded by an explicit `d`, since the induction changes the module. -/
private theorem invariantBelow (h : HasInvariantOutsideIrreducible.{v} K L) (d : ℕ) :
    InvariantBelow.{v} K L d := by
  induction d with
  | zero =>
    intro M _ _ _ _ _ N hrank hN _
    refine absurd ((LieSubmodule.toSubmodule_inj _ _).1 ?_) hN
    rw [LieSubmodule.top_toSubmodule]
    refine Submodule.eq_top_of_finrank_eq ?_
    have := Submodule.finrank_le (N : Submodule K M)
    omega
  | succ d ih =>
    intro M _ _ _ _ _ N hrank hN htriv
    obtain ⟨u, hu⟩ : ∃ u : M, u ∉ N := by
      by_contra hcon
      push Not at hcon
      exact hN (eq_top_iff.2 fun w _ ↦ hcon w)
    by_cases hact : ∀ (x : L) (m : M), ⁅x, m⁆ = 0
    · exact ⟨u, hu, fun x ↦ hact x u⟩
    push Not at hact
    have hNbot : N ≠ ⊥ := by
      rintro rfl
      obtain ⟨x, m, hm⟩ := hact
      exact hm (by simpa using htriv x m)
    by_cases hred : ∃ W : LieSubmodule K L M, W ≠ ⊥ ∧ W ≠ N ∧ W ≤ N
    · -- `N` is reducible: pass to `M ⧸ W`, then to the submodule `W + K v₀`.
      obtain ⟨W, hWbot, hWN, hWle⟩ := hred
      exact exists_invariant_notMem_of_ne_bot_of_ne_of_le ih hrank hN htriv hWbot hWN hWle
    · -- `N` is irreducible: it is an atom, and the input supplies the invariant vector.
      push Not at hred
      have hatom : IsAtom N := ⟨hNbot, fun W hW ↦ by
        by_contra hb
        exact hred W hb hW.ne hW.le⟩
      exact h N hN htriv hact ((isIrreducible_iff_isAtom N).2 hatom)

variable {M : Type v} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- **An invariant vector outside a proper submodule, with no irreducibility hypothesis.** If `L`
carries a finite-dimensional module `M` into a proper Lie submodule `N`, then `M` has an invariant
vector outside `N`.

This is the load-bearing half of complete reducibility: applied inside the endomorphism module
`M →ₗ[K] M` it produces the equivariant projection onto an arbitrary submodule. -/
theorem HasInvariantOutsideIrreducible.exists_invariant_notMem
    (h : HasInvariantOutsideIrreducible.{v} K L) [FiniteDimensional K M]
    (N : LieSubmodule K L M) (hN : N ≠ ⊤) (htriv : ∀ (x : L) (m : M), ⁅x, m⁆ ∈ N) :
    ∃ w : M, w ∉ N ∧ ∀ x : L, ⁅x, w⁆ = 0 :=
  invariantBelow h (finrank K M) N le_rfl hN htriv

/-- **A nonzero Lie submodule admits an `L`-equivariant projection onto it.** There is a linear
endomorphism of `M` taking values in `N`, restricting to the identity on `N`, and commuting with the
action of `L`. -/
theorem HasInvariantOutsideIrreducible.exists_equivariant_projection
    (h : HasInvariantOutsideIrreducible.{v} K L) [FiniteDimensional K M]
    {N : LieSubmodule K L M} (hNbot : N ≠ ⊥) :
    ∃ ψ : M →ₗ[K] M, (∀ m, ψ m ∈ N) ∧ (∀ n ∈ N, ψ n = n) ∧
      ∀ (x : L) (m : M), ψ ⁅x, m⁆ = ⁅x, ψ m⁆ := by
  -- Run the previous step inside `M →ₗ[K] M`: a linear projection onto `N` acts on `N` by the
  -- scalar `1` but does not vanish on `N`, so `homVanishingOn N` is proper inside `homScalarOn N`.
  -- The invariant element returned outside it is equivariant and acts on `N` by a nonzero scalar,
  -- so rescaling turns it into a projection.
  obtain ⟨n₀, hn₀, hn₀0⟩ : ∃ n : M, n ∈ N ∧ n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hNbot ((LieSubmodule.eq_bot_iff _).2 hcon)
  -- A linear projection of `M` onto `N`, not yet equivariant.
  obtain ⟨π, hπmem, hπid⟩ : ∃ π : M →ₗ[K] M, (∀ m, π m ∈ N) ∧ ∀ n ∈ N, π n = n := by
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (N : Submodule K M)
    exact ⟨(N : Submodule K M).projection Q hQ, fun m ↦ Submodule.projection_apply_mem hQ m,
      fun n hn ↦ Submodule.projection_apply_of_mem_left hQ hn⟩
  have hπscal : π ∈ homScalarOn (L := L) N :=
    mem_homScalarOn.2 ⟨hπmem, 1, fun n hn ↦ by rw [hπid n hn, one_smul]⟩
  have hproper : (homVanishingOn N).comap (homScalarOn (L := L) N).incl ≠ ⊤ := by
    rw [Ne, LieSubmodule.comap_incl_eq_top]
    intro hcon
    exact hn₀0 ((hπid n₀ hn₀).symm.trans ((mem_homVanishingOn.1 (hcon hπscal)).2 n₀ hn₀))
  obtain ⟨φ, hφmem, hφinv⟩ :=
    h.exists_invariant_notMem ((homVanishingOn N).comap (homScalarOn (L := L) N).incl) hproper
      (lie_mem_comap_homVanishingOn N)
  rw [LieSubmodule.mem_comap, LieSubmodule.incl_apply] at hφmem
  obtain ⟨hφN, c, hc⟩ := mem_homScalarOn.1 φ.2
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hφmem (mem_homVanishingOn.2 ⟨hφN, fun n hn ↦ by rw [hc n hn, zero_smul]⟩)
  refine ⟨c⁻¹ • (φ : M →ₗ[K] M), fun m ↦ N.smul_mem _ (hφN m), fun n hn ↦ ?_, fun x m ↦ ?_⟩
  · simp [hc n hn, smul_smul, inv_mul_cancel₀ hc0]
  · have hzero : ⁅x, (φ : M →ₗ[K] M)⁆ = 0 := by
      simpa only [LieSubmodule.coe_bracket, ZeroMemClass.coe_zero] using
        congrArg Subtype.val (hφinv x)
    have happ := congrArg (fun g : M →ₗ[K] M ↦ g m) hzero
    simp only [LieHom.lie_apply, LinearMap.zero_apply, sub_eq_zero] at happ
    simp [← happ]

/-- **Complete reducibility.** Every Lie submodule of a finite-dimensional module has a complement,
so the module is a direct sum of irreducibles. -/
theorem HasInvariantOutsideIrreducible.exists_isCompl
    (h : HasInvariantOutsideIrreducible.{v} K L) [FiniteDimensional K M]
    (N : LieSubmodule K L M) : ∃ N' : LieSubmodule K L M, IsCompl N N' := by
  rcases eq_or_ne N ⊥ with rfl | hNbot
  · exact ⟨⊤, isCompl_bot_top⟩
  obtain ⟨ψ, hψmem, hψid, hψlie⟩ := h.exists_equivariant_projection hNbot
  exact exists_isCompl_of_equivariant_projection hψmem hψid hψlie

end Invariant

end TauCeti
