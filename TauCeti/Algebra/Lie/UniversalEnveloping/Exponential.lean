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
itself, but whenever its image under an algebra map `f` is nilpotent — an extra hypothesis
throughout, satisfied by the finite-dimensional representations the construction is applied to —

```text
x_i(t) = exp (t • f (ι ℚ (eᵢ))) = ∑ n, tⁿ • f (eᵢ⁽ⁿ⁾)
```

makes sense and has integer coefficients on the images of the Kostant generators. These are the
**root subgroup elements** of the Chevalley--Demazure construction: the `t`-parameter family of
units by which the group scheme over `ℤ` is generated.

The results below record what integrality buys. First, `x_i(t)` lies in the image of the Kostant
form, and so does the whole one-parameter group of which it is a member. Second, and this is the
form the construction of a Chevalley group actually uses, `x_i(t)` preserves any additive subgroup
of a representation that the Kostant form preserves — an *admissible lattice*. Both statements are
for an arbitrary integer `t`, which is exactly the range of scalars for which the rational
coefficients `tⁿ/n!` of the ordinary exponential series recombine into integers.

The divided-power expansion, the one-parameter group law `x_i(t) x_i(u) = x_i(t + u)` and the
general stability statements are `TauCeti/RingTheory/Nilpotent/Exp.lean`; nothing here re-proves
them. Nothing here assumes the Chevalley relations either: the results hold for any families of
distinguished vectors, and a pinned root datum will supply the specific ones.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.dividedPower_mem_map_kostantForm`: the divided powers of the
  image of a root vector lie in the image of the Kostant form.
* `TauCeti.UniversalEnvelopingAlgebra.exp_zsmul_mem_map_kostantForm`: a root subgroup element lies
  in the image of the Kostant form.
* `TauCeti.UniversalEnvelopingAlgebra.coe_expSMulHom_mem_map_kostantForm`: the whole one-parameter
  group of root subgroup elements takes values there.
* `TauCeti.UniversalEnvelopingAlgebra.exp_zsmul_apply_mem_of_kostantForm_apply_mem`: a root
  subgroup element preserves every additive subgroup of a representation that the Kostant form
  preserves.

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

/-- Every divided power of the image of a designated root vector lies in the image of the Kostant
integral form: the Kostant generators `eᵢ⁽ⁿ⁾` are carried there by any algebra map. -/
theorem dividedPower_mem_map_kostantForm (e : ι → L) (h : κ → L)
    (f : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] A) (i : ι) (n : ℕ) :
    Associative.dividedPower n (f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ∈
      (kostantForm e h).map (f : _root_.UniversalEnvelopingAlgebra ℚ L →+* A) := by
  rw [← Associative.map_dividedPower f n]
  exact Subring.mem_map.2 ⟨_, dividedPower_mem_kostantForm e h i n, rfl⟩

/-- A **root subgroup element** `exp (t • f (eᵢ))` lies in the image of the Kostant integral form.

The exponential is an a priori rational combination of powers of `f (eᵢ)`; the content is that it
is an integral combination of the images of the Kostant generators `eᵢ⁽ⁿ⁾`. -/
theorem exp_zsmul_mem_map_kostantForm (e : ι → L) (h : κ → L)
    (f : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] A) {i : ι}
    (hnil : IsNilpotent (f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))) (t : ℤ) :
    IsNilpotent.exp (t • f (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ∈
      (kostantForm e h).map (f : _root_.UniversalEnvelopingAlgebra ℚ L →+* A) :=
  exp_zsmul_mem hnil (dividedPower_mem_map_kostantForm e h f i) t

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

Only stability under the divided powers of the single root vector `eᵢ` is used; that weaker
statement is `TauCeti.exp_zsmul_apply_mem`.

Stability of `M` under the whole group generated by these elements follows, since the inverse of
`exp (t • ρ (eᵢ))` is `exp (-t • ρ (eᵢ))`, of the same shape. This is how a Chevalley group is cut
out as a group of automorphisms of a lattice. -/
theorem exp_zsmul_apply_mem_of_kostantForm_apply_mem (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) {M : AddSubgroup V}
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) {i : ι}
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))) (t : ℤ)
    {v : V} (hv : v ∈ M) :
    IsNilpotent.exp (t • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) v ∈ M :=
  exp_zsmul_apply_mem hnil (fun n w hw => by
    rw [← Associative.map_dividedPower ρ n]
    exact hM _ (dividedPower_mem_kostantForm e h i n) w hw) t hv

end TauCeti.UniversalEnvelopingAlgebra
