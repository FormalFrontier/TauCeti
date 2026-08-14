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

## Main definitions

* `TauCeti.IntegralLattice`: an integral symmetric lattice in a rational vector space.
* `TauCeti.IntegralLattice.integralForm`: the induced `ℤ`-bilinear form on the carrier.
* `TauCeti.IntegralLattice.ofBasis`: the lattice spanned by a basis on which a given form is
  integral.
* `TauCeti.IntegralLattice.ofGramMatrix`: the lattice and form determined by an integral
  symmetric Gram matrix.
-/

@[expose] public section

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

/-- Membership in an integral lattice means membership in its carrier. -/
instance : Membership V (IntegralLattice V) := ⟨fun L x ↦ x ∈ L.carrier⟩

/-- An integral lattice coerces to its rational bilinear form. -/
instance : CoeFun (IntegralLattice V) fun _ ↦ V → V → ℚ :=
  ⟨fun L x y ↦ L.form x y⟩

@[simp]
theorem mem_carrier {L : IntegralLattice V} {x : V} : x ∈ L.carrier ↔ x ∈ L := Iff.rfl

@[simp]
theorem coeFun_apply (L : IntegralLattice V) (x y : V) : L x y = L.form x y := rfl

/-- Two integral lattices are equal if their carriers and rational forms are equal. -/
@[ext]
theorem ext {L M : IntegralLattice V} (hcarrier : L.carrier = M.carrier)
    (hform : L.form = M.form) : L = M := by
  cases L
  cases M
  cases hcarrier
  cases hform
  rfl

/-- The symmetry equation for the rational form of an integral lattice. -/
theorem form_comm (L : IntegralLattice V) (x y : V) : L.form x y = L.form y x :=
  L.isSymm.eq x y

/-- The inclusion of the carrier into its dual submodule. -/
def toDualSubmodule (L : IntegralLattice V) :
    L.carrier →ₗ[ℤ] L.form.dualSubmodule L.carrier :=
  L.carrier.subtype.codRestrict (L.form.dualSubmodule L.carrier) fun x ↦ L.le_dual x.property

@[simp]
theorem coe_toDualSubmodule (L : IntegralLattice V) (x : L) :
    (L.toDualSubmodule x : V) = x := rfl

/-- The inclusion of an integral lattice into its dual submodule is injective. -/
theorem toDualSubmodule_injective (L : IntegralLattice V) :
    Function.Injective L.toDualSubmodule := by
  intro x y hxy
  apply Subtype.ext
  exact congr_arg (fun z : L.form.dualSubmodule L.carrier ↦ (z : V)) hxy

/-- The integral bilinear form induced on the carrier.

This is the integral-valued restriction of `L.form`, obtained from Mathlib's canonical pairing
between a submodule and its dual submodule. -/
noncomputable def integralForm (L : IntegralLattice V) : LinearMap.BilinForm ℤ L :=
  (L.form.dualSubmoduleToDual L.carrier).comp L.toDualSubmodule

/-- The integral form recovers the rational form after coercion to `ℚ`. -/
@[simp]
theorem integralForm_cast (L : IntegralLattice V) (x y : L) :
    (L.integralForm x y : ℚ) = L.form x y := by
  exact L.form.dualSubmoduleParing_spec (L.toDualSubmodule x) y

/-- The induced integral form is symmetric. -/
theorem integralForm_isSymm (L : IntegralLattice V) : L.integralForm.IsSymm := by
  constructor
  intro x y
  exact Int.cast_injective (by rw [L.integralForm_cast, L.integralForm_cast, L.form_comm])

/-- The rational form takes an integer value on every pair of lattice vectors. -/
theorem exists_int_eq_form (L : IntegralLattice V) (x y : L) :
    ∃ z : ℤ, (z : ℚ) = L.form x y :=
  Submodule.mem_one.mp (L.le_dual x.property y y.property)

/-- The rank of the carrier equals the rational rank of the ambient space. -/
theorem rank_carrier (L : IntegralLattice V) :
    Module.rank ℤ L.carrier = Module.rank ℚ V :=
  Submodule.IsLattice.rank' ℚ L.carrier

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
    rintro x ⟨i, rfl⟩ y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact hint i j
    | zero => simp
    | add x y _ _ hx hy =>
        simpa using (1 : Submodule ℤ ℚ).add_mem hx hy
    | smul z x _ hx =>
        simpa using (1 : Submodule ℤ ℚ).smul_mem z hx

@[simp]
theorem carrier_ofBasis (b : Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) :
    (ofBasis b B hB hint).carrier = Submodule.span ℤ (Set.range b) := rfl

@[simp]
theorem form_ofBasis (b : Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) :
    (ofBasis b B hB hint).form = B := rfl

section GramMatrix

variable [Fintype ι] [DecidableEq ι]

/-- Construct an integral lattice from a finite rational basis and an integral symmetric Gram
matrix. -/
noncomputable def ofGramMatrix (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
  IntegralLattice V :=
  ofBasis b (Matrix.toBilin b (G.map (algebraMap ℤ ℚ)))
    ((Matrix.isSymm_toBilin_iff_isSymm (b := b)).mpr (hG.map _)) fun i j ↦ by
      apply Submodule.mem_one.mpr
      refine ⟨G i j, ?_⟩
      simpa only [LinearMap.BilinForm.toMatrix_apply, Matrix.map_apply] using
        congr_fun (congr_fun
          (LinearMap.BilinForm.toMatrix_toBilin (b := b) (G.map (algebraMap ℤ ℚ))) i) j |>.symm

@[simp]
theorem carrier_ofGramMatrix (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).carrier = Submodule.span ℤ (Set.range b) := rfl

@[simp]
theorem form_ofGramMatrix (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).form = Matrix.toBilin b (G.map (algebraMap ℤ ℚ)) := rfl

end GramMatrix

end Basis

end IntegralLattice

end TauCeti
