/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.RingTheory.Semisimple.Schur
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# The multiplicity of a simple module, as the dimension of a hom space

Let `A` be an algebra over an algebraically closed field `k` and let `S` be a simple `A`-module,
finite-dimensional over `k`.  If a module `M` is written as a finite direct sum of simple
modules, the number of summands isomorphic to `S` is the **multiplicity** of `S` in `M`.  Written
that way the multiplicity refers to a chosen decomposition; this file identifies it with the
manifestly choice-free number

`Module.finrank k (S →ₗ[A] M)`,

so that the multiplicity is an invariant of `M` and needs no decomposition to be defined.

The proof is Schur's lemma plus additivity.  A hom space out of `S` into a finite product splits
as the product of the hom spaces into the factors, and each factor contributes `1` or `0`
according as it is or is not isomorphic to `S`.  Those two values are the dimension forms of
Schur's lemma, `TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv` and
`TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv`, proved in
`TauCeti/RingTheory/Semisimple/Schur.lean` alongside the transport of a hom space along an
isomorphism of its target, `TauCeti.homCongrRight`.

The multiplicity results are stated for a `k`-algebra `A` and `A`-modules that are `k`-modules
compatibly, which is the generality the group-representation application needs: for `A = k[G]`
the hom space is the space of intertwiners. The reconstruction result from simple-module classes
needs only a semisimple ring, while reconstruction from hom-space dimensions returns to the
finite-dimensional `k`-algebra setting.

## Main results

* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`: **the multiplicity theorem.**  If
  `M ≃ₗ[A] ∀ i, N i` with every `N i` simple, then `finrank k (S →ₗ[A] M)` is the number of
  indices `i` with `N i ≅ S`.
* `TauCeti.natCard_eq_natCard_of_linearEquiv_pi`: consequently equivalent finite products of
  simple modules have the same number of factors isomorphic to `S`; applied to two decompositions
  of one module, this says that the multiplicity is well defined.
* `TauCeti.nonempty_linearEquiv_pi_of_natCard_eq`: conversely, two finite products of simple
  modules are linearly equivalent when their numbers of factors in every simple-module class
  agree.
* `TauCeti.nonempty_linearEquiv_of_finrank_linearMap_eq`: finite modules over a finite-dimensional
  semisimple algebra are linearly equivalent when every simple left ideal has the same hom-space
  dimension into them.
* `TauCeti.finrank_linearMap_pos_iff_exists_nonempty_linearEquiv`: the multiplicity is positive
  exactly when `S` occurs among the factors, so the hom space detects the constituents.
* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi_const`: the isotypic case, where `M` is
  a power of `S` itself and the multiplicity is the number of copies.
* `TauCeti.nonempty_linearEquiv_isotypicComponent`: **the isotypic component is the power of its
  type with exponent the multiplicity**, `isotypicComponent A M S ≃ₗ[A] Fin m → S` for
  `m = finrank k (S →ₗ[A] M)`, and
  `TauCeti.finrank_isotypicComponent`: consequently `dim (isotypicComponent A M S) = m · dim S`.
* `TauCeti.finrank_linearMap_pos_of_ne_bot`: for a finite-dimensional `M`, the hom space out of
  any nonzero submodule is positive-dimensional.  This asks for neither simplicity nor an
  algebraically closed field, so it lives apart from the results above.

## The isotypic component

Mathlib's `isotypicComponent A M S` is the sum of the submodules of `M` isomorphic to `S`, and
`IsIsotypicOfType.linearEquiv_fun` writes it as a finite power of `S` once `S` is simple and `M` is
finite-dimensional.  What the multiplicity theorem adds is the value of the exponent: every
`A`-linear map out of `S` lands in the isotypic component
(`TauCeti.apply_mem_isotypicComponent`), so `M` and its component have the same hom space out of
`S`, and the count above identifies the exponent with `finrank k (S →ₗ[A] M)`.  This is the
decomposition-free description of the component that a multiplicity computation needs.

## Implementation notes

The index set of a decomposition is counted with `Nat.card` of a subtype rather than with a
`Finset.filter`, so that no `DecidablePred` instance enters the statements; the proofs introduce
classical decidability and a `Fintype` structure locally.

The ring-general reconstruction theorem counts factors by `simpleModuleClass`; the hom-space
reconstruction theorem converts those class fibres to the `Nonempty (S ≃ₗ[A] N i)` convention of
the multiplicity theorem using `simpleModuleClass_eq_mk_iff`.

Simplicity of `S` and finite dimensionality of `S` over `k` are standing hypotheses, but nothing
is assumed about `M`: the multiplicity theorem takes the decomposition of `M` as data, and the
existence of a decomposition is the separate semisimplicity input.

## References

This builds the multiplicity half of the isotypic-decomposition API that Layer 5 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` lists as a prerequisite of
Clifford theory: "its **isotypic components** and their **multiplicities**, with multiplicity
equal to `finrank` of the relevant `Hom` space".  It is also the counted form of the isotypic
decomposition asked for in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md`.

See C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
§25, or J.-P. Serre, *Linear Representations of Finite Groups*, §2.
-/

public section

namespace TauCeti

/-! ### The multiplicity of a simple module in a finite direct sum -/

section Multiplicity

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)]
  [∀ i, Module A (N i)] [∀ i, IsScalarTower k A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- **The multiplicity theorem for a product of simple modules.**  The dimension of the space of
`A`-linear maps from a simple module `S` into a finite product of simple modules counts the
factors isomorphic to `S`. -/
theorem finrank_linearMap_pi_eq_natCard :
    Module.finrank k (S →ₗ[A] ∀ i, N i) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : Module.finrank k (S →ₗ[A] ∀ i, N i) = ∑ i, Module.finrank k (S →ₗ[A] N i) := by
    rw [← (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k).finrank_eq]
    exact Module.finrank_pi_fintype k
  have hval : ∀ i, Module.finrank k (S →ₗ[A] N i)
      = if Nonempty (S ≃ₗ[A] N i) then 1 else 0 := by
    intro i
    split_ifs with h
    · exact finrank_linearMap_eq_one_of_nonempty_linearEquiv h.some
    · exact finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (not_nonempty_iff.mp h)
  rw [hpi, Finset.sum_congr rfl fun i _ ↦ hval i, Finset.sum_boole, Nat.cast_id,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **The multiplicity theorem.**  If `M` decomposes as a finite direct sum of simple modules
`N i`, then the dimension of the space of `A`-linear maps from a simple module `S` into `M` is
the number of factors isomorphic to `S`.

Only the right-hand side mentions the decomposition, so this is the statement that the
multiplicity of `S` in `M` is an invariant of `M`; see
`TauCeti.natCard_eq_natCard_of_linearEquiv_pi`. -/
theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    Module.finrank k (S →ₗ[A] M) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  rw [← finrank_linearMap_pi_eq_natCard (k := k) (S := S) (N := N),
    ← (homCongrRight k (S := S) e).finrank_eq]

/-- A module with a finite decomposition into simple modules has a finite-dimensional space of
maps from a finite-dimensional simple module into it. -/
theorem finiteDimensional_linearMap_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    FiniteDimensional k (S →ₗ[A] M) := by
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : FiniteDimensional k (S →ₗ[A] ∀ i, N i) :=
    Module.Finite.equiv (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k)
  exact Module.Finite.equiv (homCongrRight k (S := S) e).symm

/-- **A hom space detects a constituent.**  There is a nonzero `A`-linear map from the simple
module `S` into `M` exactly when `S` occurs among the simple factors of `M`. -/
theorem finrank_linearMap_pos_iff_exists_nonempty_linearEquiv {M : Type*} [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    0 < Module.finrank k (S →ₗ[A] M) ↔ ∃ i, Nonempty (S ≃ₗ[A] N i) := by
  rw [finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) e, Nat.card_pos_iff,
    nonempty_subtype]
  exact and_iff_left inferInstance

/-- **The multiplicity is well defined.**  Equivalent finite products of simple modules have the
same number of factors isomorphic to a given simple module.

For two decompositions `e : M ≃ₗ[A] ∀ i, N i` and `f : M ≃ₗ[A] ∀ j, P j` of one module, apply
this to `e.symm.trans f` to see that the multiplicity of `S` in `M` does not depend on the
decomposition.

This is the Jordan-Hölder invariance of the multiplicity, obtained from the multiplicity theorem
rather than from a refinement argument: both counts compute the same dimension. -/
theorem natCard_eq_natCard_of_linearEquiv_pi {κ : Type*} [Finite κ] {P : κ → Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module k (P j)] [∀ j, Module A (P j)]
    [∀ j, IsScalarTower k A (P j)] [∀ j, IsSimpleModule A (P j)]
    (e : (∀ i, N i) ≃ₗ[A] ∀ j, P j) :
    Nat.card {i // Nonempty (S ≃ₗ[A] N i)} = Nat.card {j // Nonempty (S ≃ₗ[A] P j)} := by
  rw [← finrank_linearMap_pi_eq_natCard (k := k) (S := S) (N := N),
    finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) e]

end Multiplicity

/-! ### Reconstructing a finite sum from its multiplicities -/

section Reconstruction

variable {R : Type*} [Ring R] [IsSemisimpleRing R]
variable {ι κ : Type*} [Finite ι] [Finite κ]
variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, IsSimpleModule R (N i)]
variable {P : κ → Type*} [∀ j, AddCommGroup (P j)] [∀ j, Module R (P j)]
  [∀ j, IsSimpleModule R (P j)]

/-- **Finite sums of simple modules are determined by their multiplicities.** If two finite
families contain equally many modules in every simple-module isomorphism class, their products are
linearly equivalent. -/
theorem nonempty_linearEquiv_pi_of_natCard_eq
    (h : ∀ c : SimpleSubmoduleClasses R R,
      Nat.card {i // simpleModuleClass R (N i) = c} =
        Nat.card {j // simpleModuleClass R (P j) = c}) :
    Nonempty ((∀ i, N i) ≃ₗ[R] ∀ j, P j) := by
  have efiber : ∀ c, {i // simpleModuleClass R (N i) = c} ≃
      {j // simpleModuleClass R (P j) = c} := fun c ↦ (Finite.card_eq.mp (h c)).some
  let σ : ι ≃ κ := Equiv.ofFiberEquiv efiber
  have hclass (i : ι) : simpleModuleClass R (N i) = simpleModuleClass R (P (σ i)) :=
    (Equiv.ofFiberEquiv_map efiber i).symm
  have hiso (i : ι) : Nonempty (N i ≃ₗ[R] P (σ i)) :=
    simpleModuleClass_eq_iff.mp (hclass i)
  exact ⟨(LinearEquiv.piCongrRight fun i ↦ (hiso i).some).trans
    (LinearEquiv.piCongrLeft R P σ)⟩

end Reconstruction

/-! ### Reconstructing finite modules from hom-space dimensions -/

section ReconstructionFromHom

variable {k A M P : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsSemisimpleRing A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [Module.Finite A M]
variable [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P] [Module.Finite A P]

/-- **Finite modules over a semisimple algebra are determined by their simple multiplicities.**
If every simple left ideal has hom spaces of the same dimension into `M` and `P`, then `M` and
`P` are linearly equivalent. -/
theorem nonempty_linearEquiv_of_finrank_linearMap_eq
    (h : ∀ (S : Submodule A A) [IsSimpleModule A S],
      Module.finrank k (S →ₗ[A] M) = Module.finrank k (S →ₗ[A] P)) :
    Nonempty (M ≃ₗ[A] P) := by
  obtain ⟨n, SM, eM, hSM⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A M
  obtain ⟨m, SP, eP, hSP⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A P
  let _ (i : Fin n) : IsSimpleModule A (SM i) := hSM i
  let _ (i : Fin m) : IsSimpleModule A (SP i) := hSP i
  let epM : M ≃ₗ[A] ∀ i, SM i := eM.trans DFinsupp.linearEquivFunOnFintype
  let epP : P ≃ₗ[A] ∀ i, SP i := eP.trans DFinsupp.linearEquivFunOnFintype
  have hfiber : ∀ c,
      Nat.card {i // simpleModuleClass A (SM i) = c} =
        Nat.card {j // simpleModuleClass A (SP j) = c} := by
    intro c
    induction c using SimpleSubmoduleClasses.ind with
    | mk S hS =>
      let _ : IsSimpleModule A S := hS
      let _ : Module.Finite k S :=
        Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
      have hpredM (i : Fin n) : simpleModuleClass A (SM i) =
          SimpleSubmoduleClasses.mk S ↔ Nonempty (S ≃ₗ[A] SM i) := by
        rw [simpleModuleClass_eq_mk_iff]
        exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩
      have hpredP (i : Fin m) : simpleModuleClass A (SP i) =
          SimpleSubmoduleClasses.mk S ↔ Nonempty (S ≃ₗ[A] SP i) := by
        rw [simpleModuleClass_eq_mk_iff]
        exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩
      calc
        Nat.card {i // simpleModuleClass A (SM i) = SimpleSubmoduleClasses.mk S} =
            Nat.card {i // Nonempty (S ≃ₗ[A] SM i)} :=
          Nat.card_congr (Equiv.subtypeEquivRight hpredM)
        _ = Nat.card {i // Nonempty (S ≃ₗ[A] SP i)} := by
          rw [← finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) epM,
            h S, finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) epP]
        _ = Nat.card {i // simpleModuleClass A (SP i) = SimpleSubmoduleClasses.mk S} :=
          Nat.card_congr (Equiv.subtypeEquivRight hpredP).symm
  exact ⟨epM |>.trans (nonempty_linearEquiv_pi_of_natCard_eq hfiber).some |>.trans epP.symm⟩

end ReconstructionFromHom

/-! ### The isotypic case -/

section Isotypic

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]

/-- **The multiplicity of `S` in a power of `S`.**  If `M` is a finite power of the simple module
`S`, the dimension of the space of `A`-linear maps `S → M` is the number of copies.

This is the form Clifford theory uses: an isotypic component of a restriction is a power of a
single constituent, and its multiplicity is read off as a dimension. -/
theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi_const {ι : Type*} [Finite ι] {M : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] (ι → S)) :
    Module.finrank k (S →ₗ[A] M) = Nat.card ι := by
  rw [finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) (N := fun _ : ι ↦ S) e]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ ⟨LinearEquiv.refl A S⟩)

end Isotypic

/-! ### The isotypic component -/

section IsotypicComponent

variable {k A M S : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]

omit [IsSimpleModule A S] in
/-- **A module is its own isotypic component**: the sum of the submodules of `S` isomorphic to `S`
is all of `S`, the top submodule being one of them. -/
@[simp]
theorem isotypicComponent_self_eq_top : isotypicComponent A S S = ⊤ :=
  eq_top_iff.mpr <| (Submodule.le_isotypicComponent ⊤).trans_eq
    Submodule.topEquiv.isotypicComponent_eq

/-- **A map out of a simple module takes its values in the isotypic component of that type.**  So
the hom space out of `S` sees only the `S`-isotypic component of its target, which is what makes
the multiplicity of `S` in `M` a statement about that component alone. -/
theorem apply_mem_isotypicComponent (f : S →ₗ[A] M) (s : S) :
    f s ∈ isotypicComponent A M S := by
  have h := LinearMap.le_comap_isotypicComponent (M := S) (N := M) S f
  rw [isotypicComponent_self_eq_top] at h
  exact h Submodule.mem_top

/-- Corestriction to the isotypic component, an equivalence of hom spaces out of `S`.  It is the
reason the multiplicity of `S` in `M` and in its `S`-isotypic component agree. -/
private noncomputable def linearMapIsotypicComponentEquiv :
    (S →ₗ[A] isotypicComponent A M S) ≃ₗ[k] (S →ₗ[A] M) where
  toFun g := (isotypicComponent A M S).subtype ∘ₗ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f.codRestrict _ (apply_mem_isotypicComponent f)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Module k S] [IsScalarTower k A S] in
/-- **The multiplicity of `S` in `M` is its multiplicity in the `S`-isotypic component**, every
map out of `S` landing there. -/
@[simp]
theorem finrank_linearMap_isotypicComponent :
    Module.finrank k (S →ₗ[A] isotypicComponent A M S) = Module.finrank k (S →ₗ[A] M) :=
  (linearMapIsotypicComponentEquiv (k := k)).finrank_eq

variable [IsAlgClosed k] [FiniteDimensional k S] [FiniteDimensional k M]

/-- **The isotypic component is the power of its type with exponent the multiplicity.**  Mathlib's
`IsIsotypicOfType.linearEquiv_fun` writes the component as a finite power of `S`; what is proved
here is that the exponent is the multiplicity `finrank k (S →ₗ[A] M)`, which is the form that
identifies it without reference to the decomposition. -/
theorem nonempty_linearEquiv_isotypicComponent :
    Nonempty (isotypicComponent A M S ≃ₗ[A] (Fin (Module.finrank k (S →ₗ[A] M)) → S)) := by
  have : Module.Finite k ↥(isotypicComponent A M S) :=
    .of_injective ((isotypicComponent A M S).subtype.restrictScalars k) Subtype.val_injective
  have : Module.Finite A ↥(isotypicComponent A M S) :=
    Module.Finite.of_restrictScalars_finite k A _
  obtain ⟨n, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent A M S).linearEquiv_fun
  have hn : Module.finrank k (S →ₗ[A] M) = n := by
    rw [← finrank_linearMap_isotypicComponent (k := k),
      finrank_linearMap_eq_natCard_of_linearEquiv_pi_const (k := k) e]
    simp
  rw [hn]
  exact ⟨e⟩

/-- **The dimension of an isotypic component is the multiplicity times the dimension of its
type.**  This is the counted form of the isotypic decomposition: the `S`-isotypic component of `M`
is `S^{⊕ m}` with `m` the multiplicity `finrank k (S →ₗ[A] M)`. -/
theorem finrank_isotypicComponent :
    Module.finrank k ↥(isotypicComponent A M S)
      = Module.finrank k (S →ₗ[A] M) * Module.finrank k S := by
  obtain ⟨e⟩ := nonempty_linearEquiv_isotypicComponent (k := k) (A := A) (M := M) (S := S)
  rw [(e.restrictScalars k).finrank_eq]
  simp [Module.finrank_pi_fintype]

end IsotypicComponent

/-! ### Positivity for an arbitrary nonzero submodule -/

section Positivity

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
  [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]

/-- **A nonzero submodule has a positive-dimensional hom space.**  The inclusion of a nonzero
`A`-submodule `S` of `M` is a nonzero element of `S →ₗ[A] M`, and that hom space is
finite-dimensional over `k` because `S` and `M` are.  For a simple `S` over a splitting field this
is the statement that a constituent occurs with positive multiplicity.

`A` is a ring rather than a semiring because the finite-dimensionality of the hom space is
`LinearMap.finiteDimensional'`, which needs one; over a semiring `↥S` carries no `AddCommGroup`
instance and `Module.Finite.linearMap` does not apply. -/
theorem finrank_linearMap_pos_of_ne_bot {S : Submodule A M} (hS : S ≠ ⊥) :
    0 < Module.finrank k (S →ₗ[A] M) := by
  have : Module.Finite k ↥S :=
    .of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  obtain ⟨v, hv, hv0⟩ := S.ne_bot_iff.mp hS
  have : Nontrivial (S →ₗ[A] M) :=
    ⟨S.subtype, 0, fun hzero => hv0 (by simpa using DFunLike.congr_fun hzero ⟨v, hv⟩)⟩
  exact Module.finrank_pos

end Positivity

end TauCeti
