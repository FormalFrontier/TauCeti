/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

public section

/-!
# The central weight of an irreducible Lie module

A central element `z` of a Lie algebra `L` acts on any `L`-module `M` by a morphism of `L`-modules,
because `⁅x, ⁅z, m⁆⁆ = ⁅⁅x, z⁆, m⁆ + ⁅z, ⁅x, m⁆⁆` and the first summand vanishes. When `M` is a
finite-dimensional irreducible module over an algebraically closed field, Schur's lemma turns that
morphism into a scalar, and the scalar depends linearly on `z`: the **central weight** of `M`, an
element of `Module.Dual K (LieAlgebra.center K L)`.

Unlike the weights of a Cartan subalgebra on a finite-dimensional module over a semisimple Lie
algebra, the central weight carries **no integrality constraint**: it is recorded here as a plain
element of `Module.Dual K (LieAlgebra.center K L)`, with no lattice condition attached. For
`gl n K`, whose centre is the scalar matrices
(`TauCeti.center_matrix_toSubmodule_eq_span_one`), the central weight is the scalar by which the
identity matrix acts, and for `n > 0` in characteristic zero that scalar is an arbitrary element of
`K`: twisting a module by the character `(c / n) • Matrix.trace` shifts it by `c`, so none of the
integrality that the general linear *group* imposes on the central characters of its representations
survives here. That twist needs `n` invertible; when the characteristic divides `n` the identity
matrix lies in `⁅gl n K, gl n K⁆ = sl n K` and the scalars that occur can be constrained, so what is
claimed in general is only the absence of a lattice condition, not that every scalar occurs.

Algebraic closedness is essential and not a convenience: over `ℝ` the one-dimensional abelian Lie
algebra acting on `ℝ²` by the rotation generator is irreducible, is its own centre, and no scalar
describes its action.

## Main definitions

* `TauCeti.centralEnd`: the action of a central element on an `L`-module, as a morphism of
  `L`-modules.
* `TauCeti.centralWeight`: the central weight of a finite-dimensional irreducible module over an
  algebraically closed field, a linear functional on `LieAlgebra.center K L`.

## Main results

* `TauCeti.exists_forall_apply_eq_smul` is **Schur's lemma** for Lie modules: over an algebraically
  closed field, a morphism of a finite-dimensional irreducible `L`-module to itself is a scalar. Its
  companion `TauCeti.eq_of_forall_lie_eq_smul` says that the scalar describing the action of a
  single element of `L` on a nontrivial module is unique, which is what makes `centralWeight`
  well defined and linear.
* `TauCeti.exists_centralWeight_of_isIrreducible` is the existential form the roadmap pins.
* `TauCeti.lie_eq_centralWeight_smul` and `TauCeti.toEnd_eq_centralWeight_smul` are the defining
  property of the central weight, and `TauCeti.centralWeight_eq_of_forall_lie_eq_smul` its
  characterization.
* `TauCeti.centralWeight_eq_of_lieModuleEquiv`: the central weight is an isomorphism invariant.
* `TauCeti.isIrreducible_of_sup_center_eq_top`: a Lie subalgebra whose sum with the centre is all of
  `L` already acts irreducibly. This is the mechanism by which a reductive Lie algebra hands its
  irreducibles down to its derived ideal, the centre contributing only the scalars recorded by
  `centralWeight`.

## Implementation notes

Schur's lemma is proved through `LieModuleHom.ker`: `f - c • LieModuleHom.id` is again a morphism of
`L`-modules, so its kernel is a Lie submodule, and it is nonzero because `c` was chosen to be an
eigenvalue of the underlying linear map. That is why the ambient hypotheses are
`FiniteDimensional K M` and `IsAlgClosed K`, exactly the hypotheses of
`Module.End.exists_eigenvalue`.

`TauCeti.eq_of_forall_lie_eq_smul` is stated over an arbitrary field with a `Nontrivial M`
hypothesis rather than an irreducibility one, since uniqueness of the scalar needs nothing else.

## References

This is the "irreducibles of a reductive algebra" item of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: *"Over algebraically closed `K`
the centre acts on a finite-dimensional irreducible by a **central weight**, a functional on the
centre with **no integrality constraint**"*, the target named there
`exists_centralWeight_of_isIrreducible`, together with the API that makes the functional a named
object rather than an existential.
-/

namespace TauCeti

open LieAlgebra LieModule

universe u v w x

/-! ### Uniqueness of the scalar by which an element acts -/

section Uniqueness

variable {K : Type u} [Field K] {L : Type v} [LieRing L]
variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]

/-- **The scalar by which an element of `L` acts is unique.** On a nontrivial module two scalars
that both describe the action of `x` agree; no irreducibility is needed. -/
theorem eq_of_forall_lie_eq_smul [Nontrivial M] {x : L} {c d : K}
    (hc : ∀ m : M, ⁅x, m⁆ = c • m) (hd : ∀ m : M, ⁅x, m⁆ = d • m) : c = d := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have h : (c - d) • m = 0 := by rw [sub_smul, ← hc m, ← hd m, sub_self]
  rcases smul_eq_zero.1 h with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' hm

end Uniqueness

/-! ### Schur's lemma for Lie modules -/

section Schur

variable (K : Type u) [Field K] [IsAlgClosed K] (L : Type v) [LieRing L] [LieAlgebra K L]
variable (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [FiniteDimensional K M] [LieModule.IsIrreducible K L M]

/-- **Schur's lemma for Lie modules.** Over an algebraically closed field, a morphism of a
finite-dimensional irreducible `L`-module to itself is multiplication by a scalar: an eigenvalue
exists, and the corresponding eigenspace is a nonzero Lie submodule, hence everything. -/
theorem exists_forall_apply_eq_smul (f : M →ₗ⁅K,L⁆ M) : ∃ c : K, ∀ m : M, f m = c • m := by
  have _i : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f : M →ₗ[K] M)
  obtain ⟨m₀, hm₀mem, hm₀⟩ := hc.exists_hasEigenvector
  refine ⟨c, fun m ↦ ?_⟩
  have hmem : ∀ y : M, y ∈ (f - c • (LieModuleHom.id : M →ₗ⁅K,L⁆ M)).ker ↔ f y = c • y := by
    intro y
    rw [LieModuleHom.mem_ker, LieModuleHom.sub_apply, LieModuleHom.smul_apply,
      LieModuleHom.id_apply, sub_eq_zero]
  have htop : (f - c • (LieModuleHom.id : M →ₗ⁅K,L⁆ M)).ker = ⊤ := by
    refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun hbot ↦ hm₀ ?_
    have hm₀' := (hmem m₀).2 (Module.End.mem_eigenspace_iff.1 hm₀mem)
    rwa [hbot, LieSubmodule.mem_bot] at hm₀'
  exact (hmem m).1 (htop ▸ LieSubmodule.mem_top m)

end Schur

/-! ### The action of a central element -/

section CentralEnd

variable (K : Type u) [Field K] (L : Type v) [LieRing L] [LieAlgebra K L]
variable (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- **The action of a central element, as a morphism of `L`-modules.** The Leibniz rule
`⁅x, ⁅z, m⁆⁆ = ⁅⁅x, z⁆, m⁆ + ⁅z, ⁅x, m⁆⁆` has vanishing first summand exactly because `z` is
central, so `⁅z, -⁆` commutes with the action of every element of `L`. -/
def centralEnd (z : LieAlgebra.center K L) : M →ₗ⁅K,L⁆ M where
  toFun m := ⁅(z : L), m⁆
  map_add' := lie_add (z : L)
  map_smul' t m := lie_smul t (z : L) m
  map_lie' {x m} := by
    have hz : ⁅x, (z : L)⁆ = 0 := (LieModule.mem_maxTrivSubmodule K L L (z : L)).1 z.2 x
    rw [leibniz_lie x (z : L) m, hz, zero_lie, zero_add]

@[simp]
theorem centralEnd_apply (z : LieAlgebra.center K L) (m : M) :
    centralEnd K L M z m = ⁅(z : L), m⁆ :=
  (rfl)

end CentralEnd

/-! ### The central weight -/

section CentralWeight

variable (K : Type u) [Field K] [IsAlgClosed K] (L : Type v) [LieRing L] [LieAlgebra K L]
variable (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [FiniteDimensional K M] [LieModule.IsIrreducible K L M]

/-- **A central element acts by a scalar** on a finite-dimensional irreducible module over an
algebraically closed field: `TauCeti.exists_forall_apply_eq_smul` applied to
`TauCeti.centralEnd`. -/
theorem exists_forall_lie_eq_smul (z : LieAlgebra.center K L) :
    ∃ c : K, ∀ m : M, ⁅(z : L), m⁆ = c • m := by
  obtain ⟨c, hc⟩ := exists_forall_apply_eq_smul K L M (centralEnd K L M z)
  exact ⟨c, fun m ↦ by simpa using hc m⟩

/-- **The central weight** of a finite-dimensional irreducible module over an algebraically closed
field: the linear functional on `LieAlgebra.center K L` recording the scalar by which each central
element acts. -/
noncomputable def centralWeight : Module.Dual K (LieAlgebra.center K L) where
  toFun z := (exists_forall_lie_eq_smul K L M z).choose
  map_add' z w := by
    have _i : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
    refine eq_of_forall_lie_eq_smul (exists_forall_lie_eq_smul K L M (z + w)).choose_spec
      fun m ↦ ?_
    have hz := (exists_forall_lie_eq_smul K L M z).choose_spec m
    have hw := (exists_forall_lie_eq_smul K L M w).choose_spec m
    have hcoe : ((z + w : LieAlgebra.center K L) : L) = (z : L) + (w : L) := rfl
    rw [hcoe, add_lie, hz, hw, add_smul]
  map_smul' t z := by
    have _i : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
    refine eq_of_forall_lie_eq_smul (exists_forall_lie_eq_smul K L M (t • z)).choose_spec
      fun m ↦ ?_
    have hz := (exists_forall_lie_eq_smul K L M z).choose_spec m
    have hcoe : ((t • z : LieAlgebra.center K L) : L) = t • (z : L) := rfl
    rw [hcoe, smul_lie, hz, smul_smul, RingHom.id_apply, smul_eq_mul]

/-- **The defining property of the central weight**: a central element acts by the scalar the
weight assigns to it. -/
theorem lie_eq_centralWeight_smul (z : LieAlgebra.center K L) (m : M) :
    ⁅(z : L), m⁆ = centralWeight K L M z • m :=
  (exists_forall_lie_eq_smul K L M z).choose_spec m

/-- **The central weight is characterized by its defining property**: any scalar describing the
action of a central element is its value. -/
theorem centralWeight_eq_of_forall_lie_eq_smul {z : LieAlgebra.center K L} {c : K}
    (h : ∀ m : M, ⁅(z : L), m⁆ = c • m) : centralWeight K L M z = c :=
  have _i : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
  eq_of_forall_lie_eq_smul (lie_eq_centralWeight_smul K L M z) h

/-- The central weight, read as a statement about the representation `LieModule.toEnd`: a central
element acts by a scalar multiple of the identity. -/
theorem toEnd_eq_centralWeight_smul (z : LieAlgebra.center K L) :
    LieModule.toEnd K L M (z : L) = centralWeight K L M z • LinearMap.id := by
  ext m
  simpa using lie_eq_centralWeight_smul K L M z m

/-- A central element is in the kernel of the representation exactly when the central weight
vanishes on it. -/
theorem centralWeight_eq_zero_iff (z : LieAlgebra.center K L) :
    centralWeight K L M z = 0 ↔ (z : L) ∈ LieModule.ker K L M := by
  rw [LieModule.mem_ker]
  refine ⟨fun h m ↦ ?_, fun h ↦ centralWeight_eq_of_forall_lie_eq_smul K L M fun m ↦ ?_⟩
  · rw [lie_eq_centralWeight_smul K L M z m, h, zero_smul]
  · rw [h m, zero_smul]

/-- **The centre acts by a central weight**, in existential form: there is a linear functional on
`LieAlgebra.center K L` by which every central element acts. This is the form the roadmap pins; the
named witness is `TauCeti.centralWeight`. The roadmap signature also carries `[CharZero K]` and
`[FiniteDimensional K L]`, neither of which the statement needs. -/
theorem exists_centralWeight_of_isIrreducible :
    ∃ xi : Module.Dual K (LieAlgebra.center K L),
      ∀ (z : LieAlgebra.center K L) (m : M), ⁅(z : L), m⁆ = xi z • m :=
  ⟨centralWeight K L M, lie_eq_centralWeight_smul K L M⟩

/-- **Every `K`-submodule of `M` is stable under the centre.** The centre acts by scalars, and a
submodule is stable under scalars; irreducibility of `M` puts no constraint on the submodules of the
underlying vector space. -/
theorem lie_mem_of_mem_center (z : LieAlgebra.center K L) {N : Submodule K M} {m : M}
    (hm : m ∈ N) : ⁅(z : L), m⁆ ∈ N := by
  rw [lie_eq_centralWeight_smul K L M z m]
  exact N.smul_mem _ hm

end CentralWeight

/-! ### Invariance and descent to a subalgebra -/

section Transfer

variable (K : Type u) [Field K] [IsAlgClosed K] (L : Type v) [LieRing L] [LieAlgebra K L]
variable (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable (N : Type x) [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
variable [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
variable [FiniteDimensional K N] [LieModule.IsIrreducible K L N]

/-- **The central weight is an isomorphism invariant.** Equivalent irreducible modules have the same
central weight, so the weight is an invariant of the isomorphism class and can be used to separate
irreducibles. -/
theorem centralWeight_eq_of_lieModuleEquiv (e : M ≃ₗ⁅K,L⁆ N) :
    centralWeight K L N = centralWeight K L M := by
  ext z
  refine centralWeight_eq_of_forall_lie_eq_smul K L N fun n ↦ ?_
  have key : ⁅(z : L), e (e.symm n)⁆ = e ⁅(z : L), e.symm n⁆ :=
    (e.toLieModuleHom.map_lie (z : L) (e.symm n)).symm
  rw [← e.apply_symm_apply n, key, lie_eq_centralWeight_smul K L M z, map_smul]

end Transfer

section Descent

variable (K : Type u) [Field K] [IsAlgClosed K] (L : Type v) [LieRing L] [LieAlgebra K L]
variable (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [FiniteDimensional K M] [LieModule.IsIrreducible K L M]

/-- **Irreducibility descends to a subalgebra complementing the centre.** If `L' ⊔ center K L` is
all of `L` as a subspace, then a submodule for `L'` is already a submodule for `L`, because the
missing central directions act by scalars (`TauCeti.lie_mem_of_mem_center`). Applied to the derived
ideal of a reductive Lie algebra, this is the statement that an irreducible module over a reductive
algebra stays irreducible over its semisimple part, the centre contributing only the scalars
recorded by `TauCeti.centralWeight`. -/
theorem isIrreducible_of_sup_center_eq_top (L' : LieSubalgebra K L)
    (h : L'.toSubmodule ⊔ (LieAlgebra.center K L).toSubmodule = ⊤) :
    LieModule.IsIrreducible K L' M := by
  have _i : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
  refine LieModule.IsIrreducible.mk fun P hP ↦ ?_
  have hx : ∀ x : L, ∃ y ∈ L'.toSubmodule, ∃ z ∈ (LieAlgebra.center K L).toSubmodule,
      y + z = x := fun x ↦ Submodule.mem_sup.1 (by rw [h]; exact Submodule.mem_top)
  let P' : LieSubmodule K L M :=
    { __ := P.toSubmodule
      lie_mem := fun {x m} hm ↦ by
        obtain ⟨y, hy, z, hz, rfl⟩ := hx x
        rw [add_lie]
        refine P.toSubmodule.add_mem ?_ (lie_mem_of_mem_center K L M ⟨z, hz⟩ hm)
        simpa using P.lie_mem (x := (⟨y, hy⟩ : L')) hm }
  refine (LieSubmodule.toSubmodule_eq_top P).1 ?_
  rcases IsSimpleOrder.eq_bot_or_eq_top P' with hbot | htop
  · exact absurd ((LieSubmodule.toSubmodule_eq_bot P).1 (congrArg LieSubmodule.toSubmodule hbot)) hP
  · exact congrArg LieSubmodule.toSubmodule htop

end Descent

end TauCeti
