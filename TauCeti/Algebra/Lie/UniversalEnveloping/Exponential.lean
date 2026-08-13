/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.KostantForm
public import TauCeti.RingTheory.Nilpotent.Exp

/-!
# Root subgroup elements of a Kostant integral form

Let `L` be a Lie algebra over `ℚ` with distinguished root vectors `e : ι → L` and Cartan vectors
`h : κ → L`, and let `U_ℤ = kostantForm e h` be the integral form they generate inside
`UniversalEnvelopingAlgebra ℚ L`. A root vector `eᵢ` is never nilpotent in the enveloping algebra
itself, but its image under a representation `f` is, and there

```text
x_i(t) = exp (t • f (ι ℚ (eᵢ))) = ∑ n, tⁿ • f (eᵢ⁽ⁿ⁾)
```

makes sense and has integer coefficients on the images of the Kostant generators. These are the
**root subgroup elements** of the Chevalley--Demazure construction: the `t`-parameter family of
units by which the group scheme over `ℤ` is generated.

The two results below record what integrality buys. First, `x_i(t)` lies in the image of the
Kostant form, so conjugation by it preserves that image. Second, and this is the form the
construction of a Chevalley group actually uses, `x_i(t)` preserves any additive subgroup of a
representation that the Kostant form preserves — an *admissible lattice*. Both statements are for
an arbitrary integer `t`, which is exactly the range of scalars for which the rational
coefficients `tⁿ/n!` of the ordinary exponential series recombine into integers.

The divided-power expansion and the one-parameter group law
`x_i(t) x_i(u) = x_i(t + u)` are `TauCeti/RingTheory/Nilpotent/Exp.lean`; nothing here re-proves
them. Nothing here assumes the Chevalley relations either: the results hold for any families of
distinguished vectors, and a pinned root datum will supply the specific ones.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.exp_zsmul_mem_map_kostantForm`: a root subgroup element lies
  in the image of the Kostant form.
* `TauCeti.UniversalEnvelopingAlgebra.exp_zsmul_conj_mem_map_kostantForm`: conjugation by a root
  subgroup element preserves that image.
* `TauCeti.UniversalEnvelopingAlgebra.coe_expSMulHom_mem_map_kostantForm`: the whole one-parameter
  group of root subgroup elements takes values there.
* `TauCeti.UniversalEnvelopingAlgebra.exp_zsmul_apply_mem`: a root subgroup element preserves every
  additive subgroup of a representation that the Kostant form preserves.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {A : Type v} [Ring A] [Algebra ℚ A]

/-! ## Root subgroup elements inside the integral form -/

/-- A **root subgroup element** `exp (t • f (eᵢ))` lies in the image of the Kostant integral form.

The exponential is an a priori rational combination of powers of `f (eᵢ)`; the content is that it
is an integral combination of the images of the Kostant generators `eᵢ⁽ⁿ⁾`. -/
theorem exp_zsmul_mem_map_kostantForm (e : ι → L) (h : κ → L)
    (f : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] A) {i : ι}
    (hnil : IsNilpotent (f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))) (t : ℤ) :
    IsNilpotent.exp ((t : ℚ) • f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ∈
      (kostantForm e h).map (f : _root_.UniversalEnvelopingAlgebra ℚ L →+* A) := by
  refine exp_zsmul_mem hnil (fun n => ?_) t
  rw [← Associative.map_dividedPower f n]
  exact Subring.mem_map.2 ⟨_, dividedPower_mem_kostantForm e h i n, rfl⟩

/-- Conjugation by a root subgroup element preserves the image of the Kostant integral form: the
root subgroups normalize the integral form. -/
theorem exp_zsmul_conj_mem_map_kostantForm (e : ι → L) (h : κ → L)
    (f : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] A) {i : ι}
    (hnil : IsNilpotent (f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))) (t : ℤ)
    {b : A} (hb : b ∈ (kostantForm e h).map (f : _root_.UniversalEnvelopingAlgebra ℚ L →+* A)) :
    IsNilpotent.exp ((t : ℚ) • f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) * b *
        IsNilpotent.exp (((-t : ℤ) : ℚ) • f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ∈
      (kostantForm e h).map (f : _root_.UniversalEnvelopingAlgebra ℚ L →+* A) :=
  mul_mem (mul_mem (exp_zsmul_mem_map_kostantForm e h f hnil t) hb)
    (exp_zsmul_mem_map_kostantForm e h f hnil (-t))

/-- The one-parameter group of units `t ↦ exp (t • f (eᵢ))` takes values in the image of the
Kostant integral form. This is the root subgroup map `x_i` of the Chevalley--Demazure
construction, evaluated on the integral points of the additive group. -/
theorem coe_expSMulHom_mem_map_kostantForm (e : ι → L) (h : κ → L)
    (f : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] A) {i : ι}
    (hnil : IsNilpotent (f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (t : Multiplicative ℤ) :
    ((expSMulHom hnil t : Aˣ) : A) ∈
      (kostantForm e h).map (f : _root_.UniversalEnvelopingAlgebra ℚ L →+* A) := by
  rw [coe_expSMulHom]
  exact exp_zsmul_mem_map_kostantForm e h f hnil _

/-! ## Root subgroup elements act on admissible lattices -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- **A root subgroup element preserves an admissible lattice.** If an additive subgroup `M` of a
representation `V` of `L` is stable under the Kostant integral form, then it is stable under every
root subgroup element `exp (t • ρ (eᵢ))` with `t` an integer.

Stability of `M` under the whole group generated by these elements follows, since the inverse of
`exp (t • ρ (eᵢ))` is `exp (-t • ρ (eᵢ))`, of the same shape. This is how a Chevalley group is cut
out as a group of automorphisms of a lattice. -/
theorem exp_zsmul_apply_mem (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) {M : AddSubgroup V}
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) {i : ι}
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))) (t : ℤ)
    {v : V} (hv : v ∈ M) :
    IsNilpotent.exp ((t : ℚ) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) v ∈ M := by
  obtain ⟨k, hk⟩ := hnil
  rw [exp_zsmul_eq_sum_zsmul_dividedPower hk]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  refine AddSubgroup.sum_mem _ fun n _ => AddSubgroup.zsmul_mem _ ?_ _
  rw [← Associative.map_dividedPower ρ n]
  exact hM _ (dividedPower_mem_kostantForm e h i n) v hv

end TauCeti.UniversalEnvelopingAlgebra
