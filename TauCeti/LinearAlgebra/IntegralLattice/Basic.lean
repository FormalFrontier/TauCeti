/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Integral symmetric lattices

An integral symmetric lattice in a rational vector space consists of a full finitely generated
`ℤ`-submodule together with a symmetric `ℚ`-bilinear form whose values on the lattice are
integers.  The integrality condition is expressed using Mathlib's
`LinearMap.BilinForm.dualSubmodule`: the carrier is contained in its dual submodule.

The form restricts to a canonical `ℤ`-bilinear form on the carrier.  Conversely, a finite
`ℚ`-basis and an integral symmetric Gram matrix construct an integral lattice.

## References

* `TauCetiRoadmap/IntegralLattices/README.md`
* `TauCetiRoadmap/IntegralLattices/Suggested.lean`

## Main definitions

* `TauCeti.IntegralLattice`: an integral symmetric lattice in a rational vector space.
* `TauCeti.IntegralLattice.IsNondegenerate`: the nondegeneracy mixin for an integral lattice.
* `TauCeti.IntegralLattice.form_mem_one`: the rational form takes integer values on lattice vectors.
* `TauCeti.IntegralLattice.rationalBasis`: the ambient `ℚ`-basis extending a chosen `ℤ`-basis of
  the carrier.
* `TauCeti.IntegralLattice.integralForm`: the induced `ℤ`-bilinear form on the carrier.
* `TauCeti.IntegralLattice.ofSubmodule`: constructor from a full submodule, symmetric form, and
  integrality proof.
* `TauCeti.IntegralLattice.ofBasis`: the lattice spanned by a basis on which a given form is
  integral.
* `TauCeti.IntegralLattice.ofGramMatrix`: the lattice and form determined by an integral
  symmetric Gram matrix.
-/

public section

open Module

namespace TauCeti

universe u

variable (V : Type u) [AddCommGroup V] [Module ℚ V]

/-- An integral symmetric lattice in a rational vector space.

The field `le_dual` says exactly that the form takes integer values on pairs of vectors in
`carrier`. -/
structure IntegralLattice where
  /-- The full `ℤ`-submodule underlying the lattice. -/
  carrier : Submodule ℤ V
  /-- The rational symmetric bilinear form on the ambient vector space. -/
  form : LinearMap.BilinForm ℚ V
  /-- The carrier is finitely generated and spans the ambient rational vector space. -/
  isLattice : carrier.IsLattice ℚ
  /-- The rational bilinear form is symmetric. -/
  isSymm : form.IsSymm
  /-- Every vector of the carrier lies in its dual submodule. -/
  le_dual : carrier ≤ form.dualSubmodule carrier

namespace IntegralLattice

variable {V}

/-- The carrier of an integral lattice is a Mathlib lattice. -/
instance (L : IntegralLattice V) : L.carrier.IsLattice ℚ := L.isLattice

/-- An integral lattice coerces to the type of its vectors. -/
instance : CoeSort (IntegralLattice V) (Type u) := ⟨fun L ↦ L.carrier⟩

/-- An integral lattice coerces to its rational bilinear form. -/
instance : CoeFun (IntegralLattice V) fun _ ↦ V → V → ℚ :=
  ⟨fun L x y ↦ L.form x y⟩

@[simp]
theorem coe_form_apply (L : IntegralLattice V) (x y : V) : L x y = L.form x y := rfl

/-- The value of the rational form on lattice vectors is integral. -/
theorem form_mem_one (L : IntegralLattice V) (x y : L) :
    L.form x y ∈ (1 : Submodule ℤ ℚ) :=
  L.le_dual x.2 (y : V) y.2

/-- The chosen `ℤ`-basis of an integral lattice extends to a `ℚ`-basis of the ambient space. -/
@[expose]
noncomputable def rationalBasis (L : IntegralLattice V) :
    Basis (Module.Free.ChooseBasisIndex ℤ L) ℚ V :=
  (Module.Free.chooseBasis ℤ L).extendOfIsLattice ℚ

@[simp]
theorem rationalBasis_apply (L : IntegralLattice V) (i : Module.Free.ChooseBasisIndex ℤ L) :
    L.rationalBasis i = (Module.Free.chooseBasis ℤ L i : V) :=
  Basis.extendOfIsLattice_apply ℚ (Module.Free.chooseBasis ℤ L) i

/-- The `ℤ`-finrank of the carrier of an integral lattice equals the `ℚ`-finrank of the ambient
space. -/
theorem finrank_carrier (L : IntegralLattice V) :
    Module.finrank ℤ L = Module.finrank ℚ V :=
  congr_arg Cardinal.toNat (Submodule.IsLattice.rank' ℚ L.carrier)

/-- Two integral lattices are equal if their carriers and rational forms are equal. -/
@[ext]
theorem ext {L M : IntegralLattice V} (hcarrier : L.carrier = M.carrier)
    (hform : L.form = M.form) : L = M := by
  cases L
  cases M
  cases hcarrier
  cases hform
  rfl

/-- An integral lattice is nondegenerate when its ambient rational bilinear form is
nondegenerate. This is a mixin rather than a field of `IntegralLattice`, so degenerate lattices
remain objects of the same type. -/
class IsNondegenerate (L : IntegralLattice V) : Prop where
  /-- The rational bilinear form has trivial kernel. -/
  nondegenerate : L.form.Nondegenerate

/-- The ambient form of a nondegenerate integral lattice is nondegenerate. -/
theorem form_nondegenerate (L : IntegralLattice V) [L.IsNondegenerate] :
    L.form.Nondegenerate :=
  IsNondegenerate.nondegenerate

/-- The integral bilinear form induced on the carrier.

This is the integral-valued restriction of `L.form`, obtained from Mathlib's canonical pairing
between a submodule and its dual submodule. -/
noncomputable def integralForm (L : IntegralLattice V) : LinearMap.BilinForm ℤ L :=
  (L.form.dualSubmoduleToDual L.carrier).comp (Submodule.inclusion L.le_dual)

/-- The integral form recovers the rational form after coercion to `ℚ`. -/
@[simp]
theorem integralForm_cast (L : IntegralLattice V) (x y : L) :
    (L.integralForm x y : ℚ) = L.form x y := by
  rw [integralForm, LinearMap.comp_apply, LinearMap.BilinForm.dualSubmoduleToDual_apply_apply]
  exact L.form.dualSubmoduleParing_spec (Submodule.inclusion L.le_dual x) y

/-- The induced integral form is symmetric. -/
theorem isSymm_integralForm (L : IntegralLattice V) : L.integralForm.IsSymm := by
  constructor
  intro x y
  exact Int.cast_injective (by rw [L.integralForm_cast, L.integralForm_cast, L.isSymm.eq])

/-- Construct an integral lattice from a full submodule, a symmetric rational bilinear form, and
an integrality proof. -/
def ofSubmodule (S : Submodule ℤ V) [hS : S.IsLattice ℚ] (B : LinearMap.BilinForm ℚ V)
    (hB : B.IsSymm) (hle : S ≤ B.dualSubmodule S) : IntegralLattice V where
  carrier := S
  form := B
  isLattice := hS
  isSymm := hB
  le_dual := hle

@[simp]
theorem ofSubmodule_carrier (S : Submodule ℤ V) [hS : S.IsLattice ℚ] (B : LinearMap.BilinForm ℚ V)
    (hB : B.IsSymm) (hle : S ≤ B.dualSubmodule S) :
    (ofSubmodule S B hB hle).carrier = S := (rfl)

@[simp]
theorem ofSubmodule_form (S : Submodule ℤ V) [hS : S.IsLattice ℚ] (B : LinearMap.BilinForm ℚ V)
    (hB : B.IsSymm) (hle : S ≤ B.dualSubmodule S) :
    (ofSubmodule S B hB hle).form = B := (rfl)

section Basis

variable {ι : Type*} [Finite ι]

/-- The `ℤ`-span of a finite rational basis is a Mathlib lattice. -/
theorem isLattice_span_basis (b : Basis ι ℚ V) :
    (Submodule.span ℤ (Set.range b)).IsLattice ℚ := by
  constructor
  · exact Submodule.fg_span (Set.finite_range b)
  · simp [Submodule.span_span_of_tower]

/-- A symmetric rational form that is integral on basis vectors defines an integral lattice.

The carrier is the `ℤ`-span of the basis.  Bilinearity propagates the integral-value hypothesis
from basis vectors to their integral span. -/
noncomputable def ofBasis (b : Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) : IntegralLattice V where
  carrier := Submodule.span ℤ (Set.range b)
  form := B
  isLattice := isLattice_span_basis b
  isSymm := hB
  le_dual := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact hint i j
    | zero =>
      simp only [map_zero, Submodule.zero_mem]
    | add u v _ _ hu_mem hv_mem =>
      simp only [map_add, Submodule.add_mem _ hu_mem hv_mem]
    | smul c u _ hu_mem =>
      rw [map_zsmul]
      exact Submodule.smul_mem _ c hu_mem

@[simp]
theorem ofBasis_carrier (b : Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) :
    (ofBasis b B hB hint).carrier = Submodule.span ℤ (Set.range b) := (rfl)

@[simp]
theorem ofBasis_form (b : Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) :
    (ofBasis b B hB hint).form = B := (rfl)

/-- The canonical embedding of the basis vector `b i` into the carrier of `ofBasis b B hB hint`. -/
noncomputable def ofBasis.basisElem (b : Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) (i : ι) :
    ofBasis b B hB hint :=
  ⟨b i, by rw [ofBasis_carrier]; exact Submodule.subset_span (Set.mem_range_self i)⟩

@[simp]
theorem ofBasis.coe_basisElem (b : Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) (i : ι) :
    (ofBasis.basisElem b B hB hint i : V) = b i := by
  unfold ofBasis.basisElem
  rfl

end Basis

section GramMatrix

variable {ι : Type*} [Fintype ι]

open Classical in
/-- Construct an integral lattice from a finite rational basis and an integral symmetric Gram
matrix. -/
noncomputable def ofGramMatrix (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    IntegralLattice V :=
  ofBasis b (Matrix.toBilin b (G.map (algebraMap ℤ ℚ)))
    ((Matrix.isSymm_toBilin_iff_isSymm (b := b)).mpr (hG.map _)) fun i j ↦ by
      rw [← LinearMap.BilinForm.toMatrix_apply (b := b), LinearMap.BilinForm.toMatrix_toBilin,
        Matrix.map_apply]
      exact Submodule.mem_one.mpr ⟨G i j, rfl⟩

open Classical in
@[simp]
theorem ofGramMatrix_carrier (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).carrier = Submodule.span ℤ (Set.range b) := (rfl)

open Classical in
@[simp]
theorem ofGramMatrix_form (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).form = Matrix.toBilin b (G.map (algebraMap ℤ ℚ)) := (rfl)

open Classical in
/-- The canonical embedding of the basis vector `b i` into the carrier of
`ofGramMatrix b G hG`. -/
noncomputable def ofGramMatrix.basisElem (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm)
    (i : ι) : ofGramMatrix b G hG :=
  ⟨b i, by rw [ofGramMatrix_carrier]; exact Submodule.subset_span (Set.mem_range_self i)⟩

open Classical in
@[simp]
theorem ofGramMatrix.coe_basisElem (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm)
    (i : ι) : (ofGramMatrix.basisElem b G hG i : V) = b i := by
  unfold ofGramMatrix.basisElem
  rfl

open Classical in
/-- Evaluating the induced integral form of `ofGramMatrix` on embedded basis vectors recovers
the corresponding entry of the Gram matrix. -/
@[simp]
theorem integralForm_ofGramMatrix_apply (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm)
    (i j : ι) :
    (ofGramMatrix b G hG).integralForm (ofGramMatrix.basisElem b G hG i)
      (ofGramMatrix.basisElem b G hG j) = G i j := by
  apply Int.cast_injective (α := ℚ)
  rw [integralForm_cast, ofGramMatrix_form, ofGramMatrix.coe_basisElem,
    ofGramMatrix.coe_basisElem, ← LinearMap.BilinForm.toMatrix_apply (b := b),
    LinearMap.BilinForm.toMatrix_toBilin, Matrix.map_apply]
  rfl

end GramMatrix

end IntegralLattice

end TauCeti
