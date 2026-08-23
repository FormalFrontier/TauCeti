/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Induction
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive

/-!
# The fixed subcomodule

Let `C` be a coalgebra with a distinguished element `1`, and let `M` be a right `C`-comodule. The
vectors `v` with `coact v = v ⊗ 1` form a submodule, and it is a subcomodule because its own
coaction already lands in it. For the comodule attached to a representation of an affine group
this is the submodule of vectors the group fixes.

Complete reducibility turns a supply of fixed vectors into fixedness of the whole comodule: if
every nonzero subcomodule of `M` contains a nonzero fixed vector and every subcomodule of `M`
has a subcomodule complement, then a complement of the fixed subcomodule can contain no nonzero
fixed vector, hence is zero, hence the fixed subcomodule is everything.

That is the mechanism behind the Layer 6 comparison in the ReductiveGroups roadmap between
reductive and linearly reductive groups: Kolchin's theorem supplies the fixed vectors for a
unipotent group and linear reductivity supplies the complements, so a linearly reductive
unipotent group acts trivially on every representation.

## Main declarations

* `TauCeti.Comodule.fixedSubcomodule`: the subcomodule of vectors with coaction `v ↦ v ⊗ 1`.
* `TauCeti.Comodule.hasNonzeroFixedVector_iff_fixedSubcomodule_ne_bot`: a comodule has a nonzero
  fixed vector exactly when its fixed subcomodule is nonzero.
* `TauCeti.Comodule.fixedSubcomodule_eq_top_of_isCompletelyReducible`: a completely reducible
  comodule all of whose nonzero subcomodules contain nonzero fixed vectors is fixed.
* `TauCeti.Comodule.coact_eq_tmul_one_of_isCompletelyReducible`: the same conclusion read off
  vectorwise.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

section Defs

variable (R : Type u) (C : Type v) (M : Type w)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] [One C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The subcomodule of vectors fixed by the coaction: those `v` with `coact v = v ⊗ 1`.

For the comodule of a representation of an affine group this is the submodule of invariants. -/
def fixedSubcomodule : Subcomodule R C M where
  carrier :=
    LinearMap.eqLocus (coact (R := R) (C := C) (M := M)) ((TensorProduct.mk R M C).flip 1)
  coact_mem' := by
    intro m hm
    have hm' : coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) := hm
    exact ⟨(⟨m, hm⟩ : LinearMap.eqLocus (coact (R := R) (C := C) (M := M))
        ((TensorProduct.mk R M C).flip 1)) ⊗ₜ[R] (1 : C), by simpa using hm'.symm⟩

variable {R C M}

@[simp]
theorem mem_fixedSubcomodule {m : M} :
    m ∈ fixedSubcomodule R C M ↔ coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  Iff.rfl

theorem fixedSubcomodule_eq_top_iff :
    fixedSubcomodule R C M = ⊤ ↔
      ∀ m : M, coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  ⟨fun h m ↦ mem_fixedSubcomodule.mp (h ▸ Subcomodule.mem_top m),
    fun h ↦ Subcomodule.ext fun m ↦ by simp [h m]⟩

end Defs

section Field

variable {k : Type u} {C : Type v} {M : Type w}
variable [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C] [One C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- A comodule has a nonzero fixed vector exactly when its fixed subcomodule is nonzero. -/
theorem hasNonzeroFixedVector_iff_fixedSubcomodule_ne_bot :
    HasNonzeroFixedVector k C M ↔ fixedSubcomodule k C M ≠ ⊥ := by
  rw [hasNonzeroFixedVector_iff, Subcomodule.ne_bot_iff]
  exact ⟨fun ⟨v, hv, hvc⟩ ↦ ⟨v, mem_fixedSubcomodule.mpr hvc, hv⟩,
    fun ⟨v, hvm, hv⟩ ↦ ⟨v, hv, mem_fixedSubcomodule.mp hvm⟩⟩

/-- If `M` is completely reducible and every nonzero subcomodule of `M` contains a nonzero fixed
vector, then every vector of `M` is fixed.

A subcomodule complement of the fixed subcomodule meets it trivially, so it contains no nonzero
fixed vector and is therefore zero. -/
theorem fixedSubcomodule_eq_top_of_isCompletelyReducible
    (hcr : IsCompletelyReducible k C M)
    (hfix : ∀ N : Subcomodule k C M, N ≠ ⊥ →
      ∃ v ∈ N, v ≠ 0 ∧ coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] (1 : C)) :
    fixedSubcomodule k C M = ⊤ := by
  obtain ⟨Q, hQ⟩ := isCompletelyReducible_iff.mp hcr (fixedSubcomodule k C M)
  have hQbot : Q = ⊥ := by
    by_contra hne
    obtain ⟨v, hvQ, hv0, hvc⟩ := hfix Q hne
    have hmem : v ∈ (fixedSubcomodule k C M).toSubmodule ⊓ Q.toSubmodule :=
      ⟨mem_fixedSubcomodule.mpr hvc, hvQ⟩
    rw [hQ.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hv0 hmem
  have hsup := hQ.sup_eq_top
  rw [hQbot, Subcomodule.bot_toSubmodule, sup_bot_eq] at hsup
  exact Subcomodule.toSubmodule_eq_top.mp hsup

/-- The vectorwise form of `TauCeti.Comodule.fixedSubcomodule_eq_top_of_isCompletelyReducible`. -/
theorem coact_eq_tmul_one_of_isCompletelyReducible
    (hcr : IsCompletelyReducible k C M)
    (hfix : ∀ N : Subcomodule k C M, N ≠ ⊥ →
      ∃ v ∈ N, v ≠ 0 ∧ coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] (1 : C))
    (m : M) : coact (R := k) (C := C) (M := M) m = m ⊗ₜ[k] (1 : C) :=
  fixedSubcomodule_eq_top_iff.mp
    (fixedSubcomodule_eq_top_of_isCompletelyReducible hcr hfix) m

end Field

end TauCeti.Comodule
