/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Order.SupClosed
public import TauCeti.Algebra.Coalgebra.Subcomodule.Lattice

/-!
# Finite subcomodules

This file proves that, when the coalgebra is free as a module over a commutative
semiring, every element of a right comodule is contained in a finitely generated
subcomodule. It also packages the order-theoretic consequences: finite subcomodules
form a nonempty directed family, finite subsets and finitely generated submodules
are contained in one finite subcomodule, and the supremum and literal union of the
finite subcomodules are the whole comodule. Over a field these become statements
about finite-dimensional subcomodules through the same generic API.

For the elementwise result, the carrier is the span of the finitely many coefficients
occurring when the element's coaction is expanded in a basis of the coalgebra. The
counit shows that the original element lies in this span, and coordinate slices of
coassociativity show that the span is stable under the coaction.

No flatness or noetherian hypothesis is needed.

## Main declarations

* `TauCeti.Subcomodule.exists_finite_subcomodule_mem`: every element belongs to a
  subcomodule whose underlying module is finite.
* `TauCeti.Subcomodule.directedOn_finiteSubcomodules`: finite subcomodules form a
  directed family.
* `TauCeti.Subcomodule.sSup_finiteSubcomodules_eq_top`: for a free coefficient coalgebra,
  the finite subcomodules have supremum `⊤`.

## References

The directed-union theorem sequence from `finiteSubcomodules_nonempty` through
`iUnion_finiteSubcomodules_eq_univ_of_exists_mem` is adapted from the corresponding
subcoalgebra development in `TauCeti.Algebra.Coalgebra.Subcoalgebra.Finite`.

See Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace Subcomodule

section General

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

private theorem coeff_rTensor_coact
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R C) (x : M ⊗[R] C) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b
        ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C x) i =
      Comodule.coact (R := R) (C := C) (M := M)
        (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp
  | add x y hx hy => simp [hx, hy]

omit [Coalgebra R C] [Comodule R C M] in
private theorem coeff_assoc_symm_tmul
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R C)
    (m : M) (x : C ⊗[R] C) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b
        ((TensorProduct.assoc R M C C).symm (m ⊗ₜ[R] x)) i =
      m ⊗ₜ[R]
        TensorProduct.rid R C ((b.coord i).lTensor C x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c d => simp
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hx, hy]

/-- **Coassociativity, read off in a basis.** The coaction of a single coefficient of `coact m`
again lands in `N ⊗[R] C`, provided `N` contains every coefficient.

The submodule is otherwise arbitrary: containing the coefficients is the only property used, so
nothing here is special to their span. -/
private theorem coact_coeff_mem_range_map_subtype
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R C) (m : M) {N : Submodule R M}
    (hN : ∀ j, TensorProduct.equivFinsuppOfBasisRight b
      (Comodule.coact (R := R) (C := C) (M := M) m) j ∈ N) (i : ι) :
    Comodule.coact (R := R) (C := C) (M := M)
        (TensorProduct.equivFinsuppOfBasisRight b
          (Comodule.coact (R := R) (C := C) (M := M) m) i) ∈
      LinearMap.range (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C)) := by
  have hcoassoc :
      (Comodule.coact (R := R) (C := C) (M := M)).rTensor C
          (Comodule.coact (R := R) (C := C) (M := M) m) =
        (TensorProduct.assoc R M C C).symm
          (Coalgebra.comul.lTensor M
            (Comodule.coact (R := R) (C := C) (M := M) m)) := by
    apply (TensorProduct.assoc R M C C).injective
    simp
  have hcoeff := congrArg
    (fun x : (M ⊗[R] C) ⊗[R] C =>
      TensorProduct.equivFinsuppOfBasisRight b x i) hcoassoc
  rw [coeff_rTensor_coact] at hcoeff
  rw [hcoeff]
  rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply
    (Comodule.coact (R := R) (C := C) (M := M) m)]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  simp only [Finsupp.sum, map_sum]
  rw [Finsupp.finsetSum_apply]
  apply Submodule.sum_mem
  intro j _
  refine ⟨(⟨_, hN j⟩ : N) ⊗ₜ[R]
    TensorProduct.rid R C
      ((b.coord i).lTensor C (Coalgebra.comul (b j))), ?_⟩
  simp [coeff_assoc_symm_tmul]

/-- **The counit identity, read off in a basis.** Applying the counit to `coact m` recovers `m` as
a combination of its coefficients, so `m` lies in any submodule containing them all. -/
private theorem mem_of_forall_coeff_mem
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R C) (m : M) {N : Submodule R M}
    (hN : ∀ j, TensorProduct.equivFinsuppOfBasisRight b
      (Comodule.coact (R := R) (C := C) (M := M) m) j ∈ N) : m ∈ N := by
  have hcounit := Comodule.lTensor_counit_coact (R := R) (C := C) (M := M) m
  rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply
    (Comodule.coact (R := R) (C := C) (M := M) m)] at hcounit
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at hcounit
  apply_fun TensorProduct.rid R M at hcounit
  simp only [Finsupp.sum, map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
    one_smul] at hcounit
  rw [← hcounit]
  exact Submodule.sum_mem N fun i _ => N.smul_mem _ (hN i)

/-- If a coalgebra is free as a module over a commutative semiring, every element
of a right comodule belongs to a subcomodule that is finitely generated as a
module. -/
theorem exists_finite_subcomodule_mem [Module.Free R C] (m : M) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N := by
  classical
  let b := Module.Free.chooseBasis R C
  let a := TensorProduct.equivFinsuppOfBasisRight b
    (Comodule.coact (R := R) (C := C) (M := M) m)
  let N := Submodule.span R (Set.range a)
  have ha_mem (i : Module.Free.ChooseBasisIndex R C) : a i ∈ N :=
    Submodule.subset_span (Set.mem_range_self i)
  have hstable :
      ∀ n ∈ N,
        Comodule.coact (R := R) (C := C) (M := M) n ∈
          LinearMap.range
            (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C)) := by
    intro n hn
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hn
    · rintro _ ⟨i, rfl⟩
      exact coact_coeff_mem_range_map_subtype b m ha_mem i
    · intro x y _ _ hx hy
      simpa only [map_add] using (LinearMap.range
        (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C))).add_mem hx hy
    · intro r x _ hx
      simpa only [map_smul] using (LinearMap.range
        (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C))).smul_mem r hx
  refine ⟨ofSubmodule (R := R) (C := C) (M := M) N hstable, ?_, ?_⟩
  · have hSN : (ofSubmodule (R := R) (C := C) (M := M) N hstable).toSubmodule = N := by
      rw [toSubmodule_carrier]
      exact ofSubmodule_carrier N hstable
    rw [hSN]
    exact Module.Finite.span_of_finite R a.finite_range
  · exact mem_ofSubmodule.mpr (mem_of_forall_coeff_mem b m ha_mem)

/-- The set of subcomodules that are finitely generated as `R`-modules. -/
def finiteSubcomodules : Set (Subcomodule R C M) :=
  {N | Module.Finite R N.toSubmodule}

@[simp]
theorem mem_finiteSubcomodules {N : Subcomodule R C M} :
    N ∈ finiteSubcomodules (R := R) (C := C) (M := M) ↔
      Module.Finite R N.toSubmodule :=
  Iff.rfl

/-- The zero subcomodule makes the family of finite subcomodules nonempty. -/
theorem finiteSubcomodules_nonempty :
    (finiteSubcomodules (R := R) (C := C) (M := M)).Nonempty := by
  refine ⟨⊥, ?_⟩
  rw [mem_finiteSubcomodules]
  exact Module.Finite.bot R M

/-- Finite subcomodules are closed under binary joins. -/
theorem supClosed_finiteSubcomodules :
    SupClosed (finiteSubcomodules (R := R) (C := C) (M := M)) := by
  intro N hN P hP
  rw [mem_finiteSubcomodules] at hN hP ⊢
  letI : Module.Finite R N.toSubmodule := hN
  letI : Module.Finite R P.toSubmodule := hP
  exact sup_finite N P

/-- Finite subcomodules form a directed family under inclusion. -/
theorem directedOn_finiteSubcomodules :
    DirectedOn (· ≤ ·) (finiteSubcomodules (R := R) (C := C) (M := M)) :=
  supClosed_finiteSubcomodules.directedOn

/-- The carrier of the supremum of all finite subcomodules is their literal union. -/
@[simp]
theorem coe_sSup_finiteSubcomodules :
    ((sSup (finiteSubcomodules (R := R) (C := C) (M := M)) :
        Subcomodule R C M) : Set M) =
      ⋃ N : finiteSubcomodules (R := R) (C := C) (M := M), (N.1 : Set M) :=
  coe_sSup_of_directedOn finiteSubcomodules_nonempty directedOn_finiteSubcomodules

/-- Membership in the supremum of all finite subcomodules means membership in one finite
subcomodule. -/
@[simp]
theorem mem_sSup_finiteSubcomodules {m : M} :
    m ∈ sSup (finiteSubcomodules (R := R) (C := C) (M := M)) ↔
      ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N := by
  simpa only [mem_finiteSubcomodules] using
    (mem_sSup_of_directedOn finiteSubcomodules_nonempty directedOn_finiteSubcomodules (m := m))

/-- If every element lies in a finite subcomodule, then every finite set lies in one finite
subcomodule. -/
theorem exists_finite_subcomodule_of_setFinite_of_exists_mem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    {s : Set M} (hs : s.Finite) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ s ⊆ N := by
  classical
  obtain ⟨N, hNfinite, hsN⟩ :=
    DirectedOn.exists_mem_subset_of_finset_subset_biUnion
      (f := fun N : Subcomodule R C M => (N : Set M))
      finiteSubcomodules_nonempty directedOn_finiteSubcomodules
      (s := hs.toFinset) (by
        intro m _
        obtain ⟨N, hNfinite, hmN⟩ := hM m
        exact Set.mem_iUnion₂_of_mem
          (mem_finiteSubcomodules.mpr hNfinite) hmN)
  exact ⟨N, mem_finiteSubcomodules.mp hNfinite, by
    simpa only [hs.coe_toFinset] using hsN⟩

/-- If every element lies in a finite subcomodule, then every finitely generated submodule lies
in one finite subcomodule. -/
theorem exists_finite_subcomodule_of_fg_of_exists_mem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    (P : Submodule R M) (hP : P.FG) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ P ≤ N.toSubmodule := by
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hP
  obtain ⟨N, hNfinite, hsN⟩ :=
    exists_finite_subcomodule_of_setFinite_of_exists_mem hM hs
  refine ⟨N, hNfinite, ?_⟩
  rw [← hspan]
  exact Submodule.span_le.2 hsN

/-- If every element lies in a finite subcomodule, then the supremum of all finite
subcomodules is the whole comodule. -/
theorem sSup_finiteSubcomodules_eq_top_of_exists_mem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N) :
    sSup (finiteSubcomodules (R := R) (C := C) (M := M)) = ⊤ := by
  apply top_unique
  intro m _
  exact mem_sSup_finiteSubcomodules.2 (hM m)

/-- If every element lies in a finite subcomodule, then the union of all finite subcomodules is
the whole carrier. -/
theorem iUnion_finiteSubcomodules_eq_univ_of_exists_mem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N) :
    (⋃ N : finiteSubcomodules (R := R) (C := C) (M := M), (N.1 : Set M)) =
      Set.univ := by
  rw [← coe_sSup_finiteSubcomodules, sSup_finiteSubcomodules_eq_top_of_exists_mem hM]
  rfl

/-- If the coefficient coalgebra is free, every finite set lies in a finite subcomodule. -/
theorem exists_finite_subcomodule_of_setFinite [Module.Free R C]
    {s : Set M} (hs : s.Finite) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ s ⊆ N :=
  exists_finite_subcomodule_of_setFinite_of_exists_mem exists_finite_subcomodule_mem hs

/-- If the coefficient coalgebra is free, every finitely generated submodule lies in a finite
subcomodule. -/
theorem exists_finite_subcomodule_of_fg [Module.Free R C]
    (P : Submodule R M) (hP : P.FG) :
    ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ P ≤ N.toSubmodule :=
  exists_finite_subcomodule_of_fg_of_exists_mem exists_finite_subcomodule_mem P hP

/-- If the coefficient coalgebra is free, the finite subcomodules have supremum `⊤`. -/
@[simp]
theorem sSup_finiteSubcomodules_eq_top [Module.Free R C] :
    sSup (finiteSubcomodules (R := R) (C := C) (M := M)) = ⊤ :=
  sSup_finiteSubcomodules_eq_top_of_exists_mem exists_finite_subcomodule_mem

/-- If the coefficient coalgebra is free, the union of the finite subcomodules is the whole
carrier. -/
@[simp]
theorem iUnion_finiteSubcomodules_eq_univ [Module.Free R C] :
    (⋃ (N : Subcomodule R C M) (_ : Module.Finite R N.toSubmodule), (N : Set M)) =
      Set.univ := by
  simpa only [Set.iUnion_coe_set, mem_finiteSubcomodules] using
    iUnion_finiteSubcomodules_eq_univ_of_exists_mem exists_finite_subcomodule_mem

end General

end Subcomodule

end TauCeti
