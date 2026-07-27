/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Finrank

/-!
# Lagrangian subspaces of a tame pair are maximal totally real

The analytic Heegaard Floer roadmap keeps *totally real* and *Lagrangian* as separate named
hypotheses (a totally real subspace `L` is one disjoint from its `J`-image, `L ⊓ JL = ⊥`, and a
maximal totally real one is moreover complementary, `V = L ⊕ JL`; a Lagrangian subspace is one
equal to its symplectic complement, `L^ω = L`), because the two play
different roles downstream: totally real boundary conditions for the Cauchy--Riemann operator and
the tori `T_α`, `T_β` in `Sym^g(Σ)` (Lane F4), Lagrangian boundary conditions for exact Lagrangian
Floer homology (Lane F3). They are nevertheless tightly linked: on a finite-dimensional space, as
soon as a symplectic form `ω` *tames* an almost complex structure `J`, every Lagrangian subspace
is automatically maximal totally real. This file records that link in general, complementing the
standard-model statement in `Lagrangian.lean` where the coordinate factors of `V × V` are seen to
be simultaneously Lagrangian and maximal totally real.

The mechanism is the one classical computation behind "a compatible `J` makes a Lagrangian totally
real" (McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.6), split here
into its two genuinely separate pieces, following the roadmap's instruction to keep tame and
compatible distinct:

* **Disjointness** `L ⊓ JL = ⊥` needs only *taming*, not invariance: if `x = J y` lies in an
  isotropic `L` with `y ∈ L`, then `ω(y, J y) = ω(y, x) = 0` by isotropy, so `y = 0` by taming,
  hence `x = 0`. No finite-dimensionality is used.
* **Spanning** `L ⊔ JL = ⊤` is the half-dimension count: `J` is a linear isomorphism so
  `dim JL = dim L`, and a Lagrangian subspace is half-dimensional, so `dim L + dim JL = dim V`.

On a finite-dimensional space, taming alone therefore upgrades a Lagrangian subspace to a maximal
totally real one.

## Main declarations

* `TauCeti.SymplecticForm.IsIsotropic.disjoint_map_of_tames`: an isotropic subspace of a taming
  pair is disjoint from its `J`-image.
* `TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_tames`: a Lagrangian subspace of a
  taming pair on a finite-dimensional space is maximal totally real, i.e. `V = L ⊕ JL`.
* `TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_compatible`: the same for a
  compatible pair.
* `TauCeti.SymplecticForm.IsLagrangian.existsUnique_add_of_tames`: the resulting unique
  decomposition `x = (x ∈ L) + (x ∈ JL)`.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Sections 2.3 and 2.6.
-/

public section

namespace TauCeti

namespace SymplecticForm

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V} {L : Submodule ℝ V}

/-- An isotropic subspace of a taming pair is disjoint from its `J`-image: `L ⊓ JL = ⊥`.

This uses only taming, never invariance or finite-dimensionality. -/
theorem IsIsotropic.disjoint_map_of_tames (h : ω.IsIsotropic L) (htame : ω.Tames J) :
    Disjoint L (L.map J.toLinearMap) := by
  rw [Submodule.disjoint_def]
  intro x hxL hxJL
  obtain ⟨y, hyL, hyx⟩ := hxJL
  have hJyx : J y = x := hyx
  have hyx_zero : ω y x = 0 := isIsotropic_iff.1 h y hyL x hxL
  have hyy : ω y (J y) = 0 := by rw [hJyx]; exact hyx_zero
  have hy0 : y = 0 := by
    by_contra hne
    exact (htame y hne).ne' hyy
  rw [← hJyx, hy0]
  simp

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- A Lagrangian subspace of a taming pair on a finite-dimensional space is maximal totally real:
`V = L ⊕ JL`.

Note that only taming is required, not the full compatibility of `(ω, J)`. -/
theorem IsLagrangian.isMaximalTotallyReal_of_tames (hL : ω.IsLagrangian L) (htame : ω.Tames J) :
    IsMaximalTotallyReal J.toLinearMap L :=
  IsTotallyReal.isMaximalTotallyReal
    ((isTotallyReal_iff _ _).2 (hL.isIsotropic.disjoint_map_of_tames htame))
    (J.injective.comp L.subtype_injective) hL.two_mul_finrank

/-- A Lagrangian subspace of a compatible pair on a finite-dimensional space is maximal totally
real. -/
theorem IsLagrangian.isMaximalTotallyReal_of_compatible (hL : ω.IsLagrangian L)
    (h : ω.Compatible J) : IsMaximalTotallyReal J.toLinearMap L :=
  hL.isMaximalTotallyReal_of_tames h.tames

/-- The unique decomposition of every vector as an element of a Lagrangian subspace `L` plus an
element of its `J`-image, for a taming pair on a finite-dimensional space. -/
theorem IsLagrangian.existsUnique_add_of_tames (hL : ω.IsLagrangian L) (htame : ω.Tames J)
    (x : V) : ∃! y : L × L.map J.toLinearMap, (y.1 : V) + y.2 = x :=
  (hL.isMaximalTotallyReal_of_tames htame).existsUnique_add x

end FiniteDimensional

end SymplecticForm

end TauCeti
