/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Finite subcoalgebras and directed unions

This file proves the elementwise fundamental theorem of coalgebras over a principal ideal
domain: if the coalgebra is free as a module, then each of its elements belongs to a finite
subcoalgebra. Over a field the freeness hypothesis is automatic, so every coalgebra element
belongs to a finite-dimensional subcoalgebra.

Over a commutative semiring, the module-finite subcoalgebras are nonempty and directed under
finite joins. An abstract elementwise covering hypothesis therefore upgrades to containment of
finite subsets and finitely generated submodules, and identifies the coalgebra as both the
supremum and the literal union of its module-finite subcoalgebras. Applying the elementwise
theorems gives these conclusions over a principal ideal domain and over a field.

The finite regular subcomodule containing the element need not itself be a subcoalgebra. Instead,
we equip its subtype with the induced comodule structure and take its matrix-coefficient
subcoalgebra. The counit matrix coefficient recovers the original element.

## Main declarations

* `TauCeti.Subcoalgebra.exists_finite_subcoalgebra_mem`: the PID result for a coalgebra that is
  free as a module.
* `TauCeti.Subcoalgebra.exists_finiteDimensional_subcoalgebra_mem`: the field specialization.
* `TauCeti.Subcoalgebra.directedOn_finiteSubcoalgebras`: module-finite subcoalgebras are directed.
* `TauCeti.Subcoalgebra.exists_finite_subcoalgebra_of_setFinite`: every finite subset is contained
  in a module-finite subcoalgebra under the PID hypotheses.
* `TauCeti.Subcoalgebra.sSup_finiteSubcoalgebras_eq_top`: a PID/free coalgebra is the supremum of
  its module-finite subcoalgebras.
* `TauCeti.Subcoalgebra.sSup_finiteDimensional_subcoalgebras_eq_top`: a coalgebra over a field is
  the supremum of its finite-dimensional subcoalgebras.

## References

See Sweedler, *Hopf Algebras*, Chapter 2; Milne, *Algebraic Groups*, Proposition 4.7 and
Section 9d; and Hazewinkel, "Cofree coalgebras and multivariable recursiveness", Theorem 8.4.
-/

public section

namespace TauCeti

universe u v

namespace Subcoalgebra

variable {R : Type u} {C : Type v}

/-- The set of subcoalgebras that are finitely generated as `R`-modules. -/
def finiteSubcoalgebras (R : Type u) (C : Type v) [CommSemiring R] [AddCommMonoid C]
    [Module R C] [Coalgebra R C] : Set (Subcoalgebra R C) :=
  {D | Module.Finite R D.toSubmodule}

section DirectedUnions

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- A subcoalgebra belongs to `finiteSubcoalgebras` exactly when its underlying module is
finite. -/
@[simp]
theorem mem_finiteSubcoalgebras {D : Subcoalgebra R C} :
    D ∈ finiteSubcoalgebras R C ↔ Module.Finite R D.toSubmodule :=
  Iff.rfl

/-- The family of module-finite subcoalgebras is nonempty. -/
theorem nonempty_finiteSubcoalgebras : (finiteSubcoalgebras R C).Nonempty := by
  refine ⟨⊥, ?_⟩
  rw [mem_finiteSubcoalgebras, bot_toSubmodule]
  infer_instance

/-- The join of two module-finite subcoalgebras is module-finite. -/
theorem sup_mem_finiteSubcoalgebras {D E : Subcoalgebra R C}
    (hD : D ∈ finiteSubcoalgebras R C) (hE : E ∈ finiteSubcoalgebras R C) :
    D ⊔ E ∈ finiteSubcoalgebras R C := by
  rw [mem_finiteSubcoalgebras] at hD hE ⊢
  letI : Module.Finite R D.toSubmodule := hD
  letI : Module.Finite R E.toSubmodule := hE
  exact sup_finite D E

/-- The family of module-finite subcoalgebras is directed under inclusion. -/
theorem directedOn_finiteSubcoalgebras :
    DirectedOn (· ≤ ·) (finiteSubcoalgebras R C) := by
  apply SupClosed.directedOn
  intro D hD E hE
  exact sup_mem_finiteSubcoalgebras hD hE

/-- Membership in the supremum of the module-finite subcoalgebras is membership in one such
subcoalgebra. -/
@[simp]
theorem mem_sSup_finiteSubcoalgebras {c : C} :
    c ∈ sSup (finiteSubcoalgebras R C) ↔
      ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ c ∈ D := by
  simpa only [mem_finiteSubcoalgebras] using
    mem_sSup_of_directedOn nonempty_finiteSubcoalgebras directedOn_finiteSubcoalgebras

/-- The carrier of the supremum of the module-finite subcoalgebras is their literal union. -/
theorem coe_sSup_finiteSubcoalgebras :
    (↑(sSup (finiteSubcoalgebras R C)) : Set C) =
      ⋃ D ∈ finiteSubcoalgebras R C, (D : Set C) :=
  coe_sSup_of_directedOn nonempty_finiteSubcoalgebras directedOn_finiteSubcoalgebras

/-- If every element is contained in a module-finite subcoalgebra, then every finite subset is
contained in one module-finite subcoalgebra. -/
theorem exists_finite_subcoalgebra_of_setFinite_of_exists_mem
    (hcover : ∀ c : C,
      ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ c ∈ D)
    (s : Set C) (hs : s.Finite) :
    ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ s ⊆ D := by
  classical
  obtain ⟨D, hDfinite, hsD⟩ :=
    DirectedOn.exists_mem_subset_of_finset_subset_biUnion
      (f := fun D : Subcoalgebra R C => (D : Set C))
      nonempty_finiteSubcoalgebras directedOn_finiteSubcoalgebras
      (s := hs.toFinset) (by
        intro c _
        obtain ⟨D, hDfinite, hcD⟩ := hcover c
        exact Set.mem_iUnion₂_of_mem
          (mem_finiteSubcoalgebras.mpr hDfinite) hcD)
  exact ⟨D, mem_finiteSubcoalgebras.mp hDfinite, by
    simpa only [hs.coe_toFinset] using hsD⟩

/-- If every element is contained in a module-finite subcoalgebra, then every module-finite
submodule is contained in one module-finite subcoalgebra. -/
theorem exists_finite_subcoalgebra_of_finite_submodule_of_exists_mem
    (hcover : ∀ c : C,
      ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ c ∈ D)
    (M : Submodule R C) [Module.Finite R M] :
    ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ M ≤ D.toSubmodule := by
  obtain ⟨s, hsfinite, hspan⟩ :=
    Submodule.fg_def.mp (Module.Finite.iff_fg.mp (inferInstance : Module.Finite R M))
  obtain ⟨D, hDfinite, hsD⟩ :=
    exists_finite_subcoalgebra_of_setFinite_of_exists_mem hcover s hsfinite
  refine ⟨D, hDfinite, ?_⟩
  rw [← hspan, Submodule.span_le]
  exact hsD

/-- If every element is contained in a module-finite subcoalgebra, then the supremum of all
module-finite subcoalgebras is the whole coalgebra. -/
theorem sSup_finiteSubcoalgebras_eq_top_of_exists_mem
    (hcover : ∀ c : C,
      ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ c ∈ D) :
    sSup (finiteSubcoalgebras R C) = ⊤ := by
  apply top_unique
  intro c _
  exact mem_sSup_finiteSubcoalgebras.mpr (hcover c)

/-- If every element is contained in a module-finite subcoalgebra, then the literal union of
all module-finite subcoalgebras is the whole carrier. -/
theorem iUnion_finiteSubcoalgebras_eq_univ_of_exists_mem
    (hcover : ∀ c : C,
      ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ c ∈ D) :
    (⋃ D ∈ finiteSubcoalgebras R C, (D : Set C)) = Set.univ := by
  rw [← coe_sSup_finiteSubcoalgebras,
    sSup_finiteSubcoalgebras_eq_top_of_exists_mem hcover]
  ext c
  simp

end DirectedUnions

/-- If `C` is a coalgebra that is free as a module over a commutative principal ideal domain,
then every element of `C` belongs to a subcoalgebra that is finite as a module. -/
theorem exists_finite_subcoalgebra_mem [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Free R C] (c : C) :
    ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ c ∈ D := by
  letI : Module.Flat R C := Module.Flat.of_free
  obtain ⟨N, hNfinite, hcN⟩ :=
    Subcomodule.exists_finite_subcomodule_mem (R := R) (C := C) (M := C) c
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  letI : Module.Finite R N := hNfinite
  letI : Module.IsTorsionFree R N :=
    N.toSubmodule.instIsTorsionFree
  letI : Module.Free R N :=
    Module.free_of_finite_type_torsion_free' (R := R) (M := N)
  let D := Comodule.matrixCoefficientSubcoalgebra (R := R) (C := C) (M := N)
  refine ⟨D, inferInstance, ?_⟩
  let n : N := ⟨c, hcN⟩
  have hn := Comodule.matrixCoefficient_mem_subcoalgebra (R := R) (C := C) (M := N)
    ((Coalgebra.counit (R := R) (A := C)).comp (Subcomodule.subtype N).toLinearMap) n
  have hcoeff :
      Comodule.matrixCoefficient (R := R) (C := C)
          ((Coalgebra.counit (R := R) (A := C)).comp
            (Subcomodule.subtype N).toLinearMap) n = c := by
    rw [← Comodule.matrixCoefficient_map (R := R) (C := C)
      (Subcomodule.subtype N) (Coalgebra.counit (R := R) (A := C)) n]
    simp [n]
  rw [hcoeff] at hn
  exact hn

/-- Every finite subset of a coalgebra that is free over a commutative principal ideal domain
is contained in a module-finite subcoalgebra. -/
theorem exists_finite_subcoalgebra_of_setFinite [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Free R C]
    (s : Set C) (hs : s.Finite) :
    ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ s ⊆ D :=
  exists_finite_subcoalgebra_of_setFinite_of_exists_mem
    (fun c => exists_finite_subcoalgebra_mem (R := R) (C := C) c) s hs

/-- Every module-finite submodule of a coalgebra that is free over a commutative principal ideal
domain is contained in a module-finite subcoalgebra. -/
theorem exists_finite_subcoalgebra_of_finite_submodule [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Free R C]
    (M : Submodule R C) [Module.Finite R M] :
    ∃ D : Subcoalgebra R C, Module.Finite R D.toSubmodule ∧ M ≤ D.toSubmodule :=
  exists_finite_subcoalgebra_of_finite_submodule_of_exists_mem
    (fun c => exists_finite_subcoalgebra_mem (R := R) (C := C) c) M

/-- A coalgebra that is free over a commutative principal ideal domain is the supremum of its
module-finite subcoalgebras. -/
theorem sSup_finiteSubcoalgebras_eq_top [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Free R C] :
    sSup (finiteSubcoalgebras R C) = ⊤ :=
  sSup_finiteSubcoalgebras_eq_top_of_exists_mem
    fun c => exists_finite_subcoalgebra_mem (R := R) (C := C) c

/-- A coalgebra that is free over a commutative principal ideal domain is the literal union of
its module-finite subcoalgebras. -/
theorem iUnion_finiteSubcoalgebras_eq_univ [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Free R C] :
    (⋃ D ∈ finiteSubcoalgebras R C, (D : Set C)) = Set.univ :=
  iUnion_finiteSubcoalgebras_eq_univ_of_exists_mem
    fun c => exists_finite_subcoalgebra_mem (R := R) (C := C) c

/-- Every element of a coalgebra over a field belongs to a finite-dimensional subcoalgebra. -/
theorem exists_finiteDimensional_subcoalgebra_mem {k : Type u} [Field k]
    [AddCommGroup C] [Module k C] [Coalgebra k C] (c : C) :
    ∃ D : Subcoalgebra k C, FiniteDimensional k D.toSubmodule ∧ c ∈ D :=
  exists_finite_subcoalgebra_mem (R := k) (C := C) c

/-- Every finite subset of a coalgebra over a field is contained in a finite-dimensional
subcoalgebra. -/
theorem exists_finiteDimensional_subcoalgebra_of_setFinite {k : Type u} [Field k]
    [AddCommGroup C] [Module k C] [Coalgebra k C] (s : Set C) (hs : s.Finite) :
    ∃ D : Subcoalgebra k C, FiniteDimensional k D.toSubmodule ∧ s ⊆ D :=
  exists_finite_subcoalgebra_of_setFinite_of_exists_mem
    (fun c => exists_finiteDimensional_subcoalgebra_mem (k := k) (C := C) c) s hs

/-- Every finite-dimensional subspace of a coalgebra over a field is contained in a
finite-dimensional subcoalgebra. -/
theorem exists_finiteDimensional_subcoalgebra_of_finiteDimensional_submodule
    {k : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
    (M : Submodule k C) [FiniteDimensional k M] :
    ∃ D : Subcoalgebra k C, FiniteDimensional k D.toSubmodule ∧ M ≤ D.toSubmodule :=
  exists_finite_subcoalgebra_of_finite_submodule_of_exists_mem
    (fun c => exists_finiteDimensional_subcoalgebra_mem (k := k) (C := C) c) M

/-- Every coalgebra over a field is the supremum of its finite-dimensional subcoalgebras. -/
theorem sSup_finiteDimensional_subcoalgebras_eq_top {k : Type u} [Field k]
    [AddCommGroup C] [Module k C] [Coalgebra k C] :
    sSup {D : Subcoalgebra k C | FiniteDimensional k D.toSubmodule} = ⊤ := by
  simpa only [finiteSubcoalgebras, FiniteDimensional] using
    sSup_finiteSubcoalgebras_eq_top (R := k) (C := C)

/-- Every coalgebra over a field is the literal union of its finite-dimensional
subcoalgebras. -/
theorem iUnion_finiteDimensional_subcoalgebras_eq_univ {k : Type u} [Field k]
    [AddCommGroup C] [Module k C] [Coalgebra k C] :
    (⋃ (D : Subcoalgebra k C) (_ : FiniteDimensional k D.toSubmodule), (D : Set C)) =
      Set.univ := by
  simpa only [finiteSubcoalgebras, FiniteDimensional, Set.mem_ofPred_eq] using
    iUnion_finiteSubcoalgebras_eq_univ (R := k) (C := C)

end Subcoalgebra

end TauCeti
