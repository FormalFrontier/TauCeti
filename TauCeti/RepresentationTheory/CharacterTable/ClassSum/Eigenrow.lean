/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.MultiplicationMatrix
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Common eigenrows of the class-multiplication matrices

For a finite group `G` the class sums `K_C` are a `k`-basis of the centre `Z(k[G])`
(`TauCeti.classSumBasis`), and the class-multiplication matrices `Mᵢ`
(`TauCeti.classMultMatrix`) record multiplication by `K_{Cᵢ}` in that basis. This file identifies
the **normalized** common **left** eigenvectors of the family `{Mᵢ}` — those taking the value `1` at
the class of `1` — in the row/`ᵥ*` convention pinned by `TauCeti.classMultMatrix`, with the
`k`-algebra homomorphisms out of the centre.

Everything rests on the **coordinate identity** `K_{Cᵢ} K_{Cⱼ} = ∑ₖ aᵢⱼₖ K_{Cₖ}` inside the centre,
which is `TauCeti.classSumCenter_mul`.

* `TauCeti.IsClassEigenrow v` says `v ᵥ* Mᵢ = v Cᵢ • v` for every class `Cᵢ`, and
  `TauCeti.isClassEigenrow_iff` unwinds it to the scalar identity
  `∑ₖ aᵢⱼₖ v Cₖ = v Cᵢ * v Cⱼ`.
* `TauCeti.isClassEigenrow_of_forall_exists_smul`: for a normalized `v` the eigenvalues need not be
  guessed — being a common left eigenvector at all forces them to be the values of `v`.
* `TauCeti.isClassEigenrow_classSumRow`: the values of an algebra homomorphism
  `φ : Z(k[G]) →ₐ[k] k` on the class sums form such an eigenrow.
* `TauCeti.eigenrowAlgHom`: conversely, a common left eigenrow `v` normalized by
  `v (ConjClasses.mk 1) = 1` extends from the class-sum basis to an algebra homomorphism.
* `TauCeti.isClassEigenrow_iff_exists_algHom` and `TauCeti.algHomEquivEigenrow` package the two
  directions as an equivalence between `Z(k[G]) →ₐ[k] k` and the normalized common left eigenrows.

The normalization cannot be dropped: `TauCeti.isClassEigenrow_zero` shows `0` is an eigenrow, while
`TauCeti.classSumRow_mk_one` shows every row of an algebra homomorphism is normalized. Over a ring
without zero divisors the normalization is exactly the exclusion of that zero row:
`TauCeti.IsClassEigenrow.mk_one_eq_one` shows that under `NoZeroDivisors k` every *nonzero* eigenrow
already satisfies `v (ConjClasses.mk 1) = 1`.

Nothing here uses representation theory: the statement is about the class algebra alone, so it holds
over any commutative ring `k`. In the Burnside--Dixon--Schneider algorithm it is the step that turns
a computed common eigenrow of the (integer, hence reducible mod `p`) matrices `Mᵢ` back into a
central character; that identification of the algebra homomorphisms with the central characters of
the irreducible representations is a separate statement, belonging to the layer that constructs
central characters.

## References

This is the milestone `normalized_eigenrow_iff_algHom` of Layer 5 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
and its
[suggested declarations](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/Suggested.lean),
stated over a general commutative ring and with the algebra homomorphism produced as a `def`.
-/

public section

namespace TauCeti

open scoped Matrix

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

variable {k : Type*} [CommRing k]

/-- The row of values of an algebra homomorphism out of the centre of `k[G]` on the class sums. -/
noncomputable def classSumRow (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    ConjClasses G → k :=
  fun C => φ (classSumCenter C)

@[simp]
theorem classSumRow_apply (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k)
    (C : ConjClasses G) : classSumRow φ C = φ (classSumCenter C) :=
  (rfl)

/-- The class sum of the class of `1` is the unit of the centre, so every algebra homomorphism
takes the value `1` there: the row of an algebra homomorphism is normalized. -/
theorem classSumRow_mk_one (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    classSumRow φ (ConjClasses.mk (1 : G)) = 1 := by
  simp [classSumRow]

/-- An algebra homomorphism out of the centre of `k[G]` is determined by its values on the class
sums, because those are a basis. -/
theorem classSumRow_injective :
    Function.Injective (classSumRow (G := G) (k := k)) := by
  intro φ ψ h
  refine AlgHom.toLinearMap_injective (Module.Basis.ext classSumBasis fun C => ?_)
  simpa only [classSumRow_apply, classSumBasis_apply, AlgHom.toLinearMap_apply] using congrFun h C

/-- A function on the conjugacy classes of `G` is a **common left eigenrow** of the
class-multiplication matrices when, for every class `Cᵢ`, it is a left eigenvector of
`classMultMatrix Cᵢ` with eigenvalue its own value at `Cᵢ`.

The row/`ᵥ*` orientation is the one pinned by `TauCeti.classMultMatrix`; the transposed matrix would
be needed for the column/`*ᵥ` convention. -/
def IsClassEigenrow (v : ConjClasses G → k) : Prop :=
  ∀ Cᵢ : ConjClasses G,
    v ᵥ* (classMultMatrix Cᵢ).map (Int.cast : ℤ → k) = v Cᵢ • v

/-- Acting with a class-multiplication matrix on a row vector from the left contracts the row
against the structure constants. -/
theorem vecMul_classMultMatrix_apply (v : ConjClasses G → k) (Cᵢ Cⱼ : ConjClasses G) :
    (v ᵥ* (classMultMatrix Cᵢ).map (Int.cast : ℤ → k)) Cⱼ =
      ∑ Cₖ : ConjClasses G, (structureConstant Cᵢ Cⱼ Cₖ : k) * v Cₖ := by
  rw [Matrix.vecMul_apply_eq_sum]
  refine Finset.sum_congr rfl fun Cₖ _ => ?_
  simp only [Matrix.map_apply, classMultMatrix_apply, Int.cast_natCast]
  ring

/-- The eigenrow condition, unwound into the scalar identity
`∑ₖ aᵢⱼₖ v Cₖ = v Cᵢ * v Cⱼ` on the structure constants. -/
theorem isClassEigenrow_iff (v : ConjClasses G → k) :
    IsClassEigenrow v ↔ ∀ Cᵢ Cⱼ : ConjClasses G,
      ∑ Cₖ : ConjClasses G, (structureConstant Cᵢ Cⱼ Cₖ : k) * v Cₖ = v Cᵢ * v Cⱼ := by
  refine forall_congr' fun Cᵢ => ?_
  rw [funext_iff]
  exact forall_congr' fun Cⱼ => by
    simp only [vecMul_classMultMatrix_apply, Pi.smul_apply, smul_eq_mul]

/-- The zero row is a common left eigenrow. This is why the correspondence with algebra
homomorphisms needs the normalization `v (ConjClasses.mk 1) = 1`. -/
theorem isClassEigenrow_zero : IsClassEigenrow (0 : ConjClasses G → k) := by
  intro Cᵢ
  simp

/-- The value of a common left eigenrow at the class of `1` acts as an identity on the row: the
class-multiplication matrix at the class of `1` is the identity matrix. -/
theorem IsClassEigenrow.mk_one_smul {v : ConjClasses G → k} (hv : IsClassEigenrow v) :
    v (ConjClasses.mk (1 : G)) • v = v := by
  have h := hv (ConjClasses.mk (1 : G))
  rw [classMultMatrix_mk_one] at h
  simpa using h.symm

/-- Over a ring without zero divisors, a **nonzero** common left eigenrow is automatically
normalized: its value at the class of `1` is `1`. -/
theorem IsClassEigenrow.mk_one_eq_one [NoZeroDivisors k] {v : ConjClasses G → k}
    (hv : IsClassEigenrow v) (hv₀ : v ≠ 0) : v (ConjClasses.mk (1 : G)) = 1 := by
  obtain ⟨C, hC⟩ : ∃ C, v C ≠ 0 := by
    by_contra h
    exact hv₀ (funext fun C => not_not.mp fun hC => h ⟨C, hC⟩)
  have h := congrFun hv.mk_one_smul C
  simp only [Pi.smul_apply, smul_eq_mul] at h
  exact mul_right_cancel₀ hC (by rw [h, one_mul])

/-- **The eigenvalue of a normalized common left eigenvector is forced.** If `v` takes the value `1`
at the class of `1` and `v ᵥ* Mᵢ = c • v` for some scalar `c`, then `c = v Cᵢ`: evaluating at the
class of `1` reads the eigenvalue off the row. -/
theorem eq_of_vecMul_classMultMatrix_eq_smul {v : ConjClasses G → k}
    (hv₁ : v (ConjClasses.mk (1 : G)) = 1) {Cᵢ : ConjClasses G} {c : k}
    (h : v ᵥ* (classMultMatrix Cᵢ).map (Int.cast : ℤ → k) = c • v) : c = v Cᵢ := by
  have h₁ := congrFun h (ConjClasses.mk (1 : G))
  rw [vecMul_classMultMatrix_apply] at h₁
  simp only [structureConstant_mk_one_right, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq' Finset.univ Cᵢ v, Finset.mem_univ, if_true,
    Pi.smul_apply, smul_eq_mul, hv₁, mul_one] at h₁
  exact h₁.symm

/-- **A normalized common left eigenvector of the class-multiplication matrices is an eigenrow.**
Only the existence of *some* eigenvalue for each matrix has to be checked; the normalization forces
it to be the row's own value. -/
theorem isClassEigenrow_of_forall_exists_smul {v : ConjClasses G → k}
    (hv₁ : v (ConjClasses.mk (1 : G)) = 1)
    (h : ∀ Cᵢ : ConjClasses G,
      ∃ c : k, v ᵥ* (classMultMatrix Cᵢ).map (Int.cast : ℤ → k) = c • v) :
    IsClassEigenrow v := fun Cᵢ => by
  obtain ⟨c, hc⟩ := h Cᵢ
  rwa [eq_of_vecMul_classMultMatrix_eq_smul hv₁ hc] at hc

/-- **The values of an algebra homomorphism on the class sums form a common left eigenrow.** This
is the coordinate identity `TauCeti.classSumCenter_mul` pushed through `φ`. -/
theorem isClassEigenrow_classSumRow (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    IsClassEigenrow (classSumRow φ) := by
  refine (isClassEigenrow_iff _).mpr fun Cᵢ Cⱼ => ?_
  have h := congrArg φ (classSumCenter_mul k Cᵢ Cⱼ)
  simp only [map_mul, map_sum, map_smul, smul_eq_mul] at h
  simpa only [classSumRow_apply] using h.symm

/-- The linear extension of a row of scalars along the class-sum basis is multiplicative as soon as
it is multiplicative on the basis itself. -/
private theorem map_mul_of_basis
    {f : Subalgebra.center k (MonoidAlgebra k G) →ₗ[k] k}
    (hf : ∀ Cᵢ Cⱼ : ConjClasses G,
      f (classSumCenter Cᵢ * classSumCenter Cⱼ) = f (classSumCenter Cᵢ) * f (classSumCenter Cⱼ))
    (x y : Subalgebra.center k (MonoidAlgebra k G)) : f (x * y) = f x * f y :=
  (LinearMap.map_mul_iff f).mpr
    (LinearMap.ext_basis classSumBasis classSumBasis fun Cᵢ Cⱼ => by
      simpa only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply,
        LinearMap.coe_comp, Function.comp_apply, classSumBasis_apply] using hf Cᵢ Cⱼ) x y

variable {v : ConjClasses G → k}

/-- **The algebra homomorphism attached to a normalized common left eigenrow**: the linear extension
of `v` along the class-sum basis. Multiplicativity is the eigenrow condition read through the
coordinate identity, and it is unital because the class sum at the class of `1` is `1`. -/
noncomputable def eigenrowAlgHom (hv₁ : v (ConjClasses.mk (1 : G)) = 1)
    (hv : IsClassEigenrow v) : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
  AlgHom.ofLinearMap (Module.Basis.constr classSumBasis k v)
    (by
      rw [← classSumCenter_mk_one, ← classSumBasis_apply, Module.Basis.constr_basis]
      exact hv₁)
    (map_mul_of_basis fun Cᵢ Cⱼ => by
      rw [classSumCenter_mul]
      simp only [map_sum, map_smul, smul_eq_mul, ← classSumBasis_apply,
        Module.Basis.constr_basis]
      exact (isClassEigenrow_iff v).mp hv Cᵢ Cⱼ)

@[simp]
theorem eigenrowAlgHom_classSumCenter (hv₁ : v (ConjClasses.mk (1 : G)) = 1)
    (hv : IsClassEigenrow v) (C : ConjClasses G) :
    eigenrowAlgHom hv₁ hv (classSumCenter C) = v C := by
  rw [eigenrowAlgHom, AlgHom.ofLinearMap_apply, ← classSumBasis_apply,
    Module.Basis.constr_basis]

@[simp]
theorem classSumRow_eigenrowAlgHom (hv₁ : v (ConjClasses.mk (1 : G)) = 1)
    (hv : IsClassEigenrow v) : classSumRow (eigenrowAlgHom hv₁ hv) = v :=
  funext fun C => eigenrowAlgHom_classSumCenter hv₁ hv C

/-- **Normalized common left eigenrows are exactly the class-algebra homomorphisms.** A function `v`
on the conjugacy classes with `v (ConjClasses.mk 1) = 1` is a common left eigenvector of every
class-multiplication matrix, with eigenvalue `v Cᵢ` at `Cᵢ`, if and only if it is the row of values
of a `k`-algebra homomorphism `Z(k[G]) →ₐ[k] k` on the class sums. -/
theorem isClassEigenrow_iff_exists_algHom (hv₁ : v (ConjClasses.mk (1 : G)) = 1) :
    IsClassEigenrow v ↔
      ∃ φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k, classSumRow φ = v :=
  ⟨fun hv => ⟨eigenrowAlgHom hv₁ hv, classSumRow_eigenrowAlgHom hv₁ hv⟩,
    fun ⟨φ, hφ⟩ => hφ ▸ isClassEigenrow_classSumRow φ⟩

/-- **The algebra homomorphisms out of the centre of `k[G]` are the normalized common left
eigenrows of the class-multiplication matrices**, bundled as an equivalence: a homomorphism goes to
its row of values on the class sums, and a row extends linearly along the class-sum basis. -/
noncomputable def algHomEquivEigenrow :
    (Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) ≃
      {v : ConjClasses G → k // v (ConjClasses.mk (1 : G)) = 1 ∧ IsClassEigenrow v} where
  toFun φ := ⟨classSumRow φ, classSumRow_mk_one φ, isClassEigenrow_classSumRow φ⟩
  invFun v := eigenrowAlgHom v.2.1 v.2.2
  left_inv _ := classSumRow_injective (classSumRow_eigenrowAlgHom _ _)
  right_inv v := Subtype.ext (classSumRow_eigenrowAlgHom v.2.1 v.2.2)

@[simp]
theorem algHomEquivEigenrow_apply_coe (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    (algHomEquivEigenrow φ : ConjClasses G → k) = classSumRow φ :=
  (rfl)

@[simp]
theorem algHomEquivEigenrow_symm_apply_classSumCenter
    (v : {v : ConjClasses G → k // v (ConjClasses.mk (1 : G)) = 1 ∧ IsClassEigenrow v})
    (C : ConjClasses G) :
    algHomEquivEigenrow.symm v (classSumCenter C) = (v : ConjClasses G → k) C :=
  eigenrowAlgHom_classSumCenter v.2.1 v.2.2 C

end TauCeti
