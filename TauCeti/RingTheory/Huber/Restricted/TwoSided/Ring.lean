/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.RingTheory.Huber.Restricted.TwoSided.Series

/-!
# The ring of two-sided restricted series `A⟨X, X⁻¹⟩`

`TauCeti.Huber.twoSidedRestrictedSubmodule` is the `A`-*module* of coefficient families
underlying Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39). This module equips it with the convolution
multiplication, making the coefficient object a ring — a commutative `A`-algebra when `A` is
commutative, as the source states.

## Why this is not the one-sided argument

For the one-sided `A⟨X₁, …, Xₖ⟩` the coefficient convolution `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ` is a
**finite** sum, because `MvPowerSeries.coeff_mul` runs over the antidiagonal of `Fin k →₀ ℕ`, which
is a `Finset`; that is what `TauCeti.Huber.IsRestricted.mul` rearranges. Over `ℤ` the antidiagonal
`{(i, j) | i + j = n}` is **infinite**, so the coefficient is a genuine infinite sum and there is
no rearrangement to perform. Concretely `ℤ` carries no `Finset.HasAntidiagonal` instance and can
carry none, so the `Finset`-indexed Cauchy-product lemmas do not apply here at all.

## The facts that replace it

* *Restrictedness is summability.* In a **complete** nonarchimedean group, a family is summable
  exactly when it tends to `0` along the cofinite filter
  (`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`), which is precisely the
  restrictedness condition: `mem_twoSidedRestrictedSubmodule_iff_summable`.
* *Existence.* Hence `Summable.mul_of_nonarchimedean` makes `(i, j) ↦ aᵢbⱼ` summable on `ℤ × ℤ`,
  and each antidiagonal, being a subfamily, is summable too — this is the source's "convergent
  series `∑_{k + l = n} aₖ bₗ`".
* *Closure.* That the product is again restricted needs neither completeness nor summability. It is
  `NonarchimedeanAddGroup.zeroAtFilter_cofinite_tsum_fiberwise` applied to addition `ℤ × ℤ → ℤ`: an
  open subgroup omits only finitely many `aᵢbⱼ`, hence meets only finitely many antidiagonals, and
  an antidiagonal all of whose terms lie in an open — hence closed — subgroup sums back into it.
* *Associativity.* Both `((fg)h)ₙ` and `(f(gh))ₙ` are the sum of `aᵢ bⱼ cₗ` over
  `{i + j + l = n}`, an infinite family summable by two applications of
  `Summable.mul_of_nonarchimedean`; summing it fibrewise in the degree of the partial product
  (`HasSum.prod_fiberwise`) gives the two bracketings, and uniqueness of limits identifies them.
  Nothing of the sort is in Mathlib's `DiscreteConvolution`, which supplies the unit, the
  annihilation laws, distributivity, scalar compatibility and commutativity — every ring axiom
  except associativity.

## Main definitions

* `TauCeti.Huber.twoSidedRestrictedSubmodule.instMul` and `instOne`: the product and the unit on
  `A⟨X, X⁻¹⟩`; the product is Mathlib's
  `DiscreteConvolution.addConvolution` along the bilinear map `LinearMap.mul ℤ A`.
* `TauCeti.Huber.twoSidedRestrictedSubmodule.instRing`, `instCommRing`, `instAlgebra`: **the ring
  structure**, and the `A`-algebra structure of Example 6.39 when `A` is commutative.
* `TauCeti.Huber.twoSidedMonomial`: the monomial `a Xⁿ`. The Laurent variable Wedhorn writes `ζ`
  is `twoSidedMonomial 1 1` and its inverse is `twoSidedMonomial (-1) 1`; neither gets a
  separate definition, so the only body this file exposes is the monomial's.

## Main results

* `TauCeti.Huber.addConvolution_mul_apply`: the coefficient formula `(fg)ₙ = ∑' k, aₖ b_{n-k}`.
* `TauCeti.Huber.addConvolution_mem_twoSidedRestrictedSubmodule`: **the closure result** — a
  convolution of restricted families is restricted.
* `TauCeti.Huber.mem_twoSidedRestrictedSubmodule_iff_summable`: over a complete group,
  restrictedness is summability.
* `TauCeti.Huber.summable_mul_sub_of_mem_twoSidedRestrictedSubmodule` and
  `TauCeti.Huber.addConvolutionExists_of_mem_twoSidedRestrictedSubmodule`: over a complete ring the
  coefficient series of a product converge.
* `TauCeti.Huber.twoSidedMonomial_mul_twoSidedMonomial`: **monomials add degrees**,
  `(a Xᵐ)(b Xⁿ) = ab X^{m+n}`. It holds with no completeness, summability or separation hypothesis,
  since only one term of the coefficient series survives, so it is stated well above the ring
  axioms.
* `TauCeti.Huber.isUnit_twoSidedMonomial_one`: **the Laurent variable is a unit**, with inverse the
  degree-`(-1)` monomial — the content of Example 6.39. Both inverse identities are instances of the
  degree-addition rule, so they get no separate lemmas; `IsUnit` itself needs the monoid that
  arrives with the ring structure.
* `TauCeti.Huber.coe_mul_apply`: the coefficient of a product read off an element of the submodule,
  `(fg)ₙ = ∑' k, aₖ b_{n-k}`.
* `TauCeti.Huber.coe_mul_twoSidedRestrictedSubmodule`,
  `TauCeti.Huber.coe_one_twoSidedRestrictedSubmodule`,
  `TauCeti.Huber.coe_twoSidedMonomial` and
  `TauCeti.Huber.coe_algebraMap_twoSidedRestrictedSubmodule`: the computation API. The instance
  bodies are not exposed, so these are how a product, the unit, a monomial and the structure map are
  computed outside this module.

## Implementation notes

The product is *not* the pointwise product of `ℤ → A`, so `A⟨X, X⁻¹⟩` is not a subring of `ℤ → A`
and there is no ambient convolution ring to take a subring of — unlike the one-sided case, where
`MvPowerSeries` already supplies one and `TauCeti.Huber.restrictedMvPowerSeriesSubring` is a genuine
`Subring`. The multiplication is therefore installed directly on the submodule's coercion to a type,
where nothing else claims a `Mul`.

We reuse Mathlib's `DiscreteConvolution.addConvolution` rather than defining a `ℤ`-indexed
convolution: it is the same sum over the same fibre, `addFiber n = {(i, j) | i + j = n}`.

The multiplication and the closure result need only a nonarchimedean ring topology. The ring
axioms are proved here from the coefficient ring being complete **and** Hausdorff
(`[CompleteSpace A] [T0Space A]`): the proofs of distributivity and associativity use completeness
so that the coefficient series converge at all, and Hausdorffness so that `tsum` is a limit rather
than a choice among limits. This is exactly Wedhorn's convention, whose "complete" means
"Hausdorff and every Cauchy filter basis converges" (Definition 5.31(4)–(5)), and it is the
hypothesis list the neighbouring `TauCeti.RingTheory.Huber.Restricted.Laurent` already carries.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39.
-/

public section

open Filter Topology DiscreteConvolution

namespace TauCeti.Huber

section Convolution

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

-- The antidiagonal `{(i, j) | i + j = n}` in `ℤ × ℤ`, parametrised by its first coordinate. This
-- is where the `ℤ`-indexed picture and Mathlib's fibre picture meet, and it is an `Equiv` rather
-- than a `Finset` precisely because the antidiagonal is infinite.
private def addFiberEquivInt (n : ℤ) : ℤ ≃ (addFiber n : Set (ℤ × ℤ)) where
  toFun k := ⟨(k, n - k), by grind⟩
  invFun ab := ab.1.1
  left_inv _ := rfl
  right_inv ab := by grind

omit [NonarchimedeanRing A] in
/-- **The coefficient formula for the two-sided product**: `(fg)ₙ = ∑' k, aₖ b_{n-k}`, the familiar
Laurent convolution. -/
theorem addConvolution_mul_apply (f g : ℤ → A) (n : ℤ) :
    addConvolution (LinearMap.mul ℤ A) f g n = ∑' k : ℤ, f k * g (n - k) :=
  -- Reindexing Mathlib's sum over `addFiber n` by the first coordinate is exactly
  -- `addFiberEquivInt`.
  ((addFiberEquivInt n).tsum_eq fun ab ↦ f ab.1.1 * g ab.1.2).symm

/-- **The product of two restricted families is restricted**, so `A⟨X, X⁻¹⟩` is closed under the
convolution. This is what makes it a ring rather than merely a module, and it needs neither
completeness nor summability. -/
theorem addConvolution_mem_twoSidedRestrictedSubmodule {f g : ℤ → A}
    (hf : f ∈ twoSidedRestrictedSubmodule A A) (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    addConvolution (LinearMap.mul ℤ A) f g ∈ twoSidedRestrictedSubmodule A A := by
  rw [mem_twoSidedRestrictedSubmodule] at hf hg ⊢
  -- Summing along the fibres of addition `ℤ × ℤ → ℤ` preserves cofinite nullity, and the family
  -- `(i, j) ↦ aᵢbⱼ` is cofinitely null because `f` and `g` are. Where a fibre's sum fails to
  -- converge it is `0` by the `tsum` convention, and `0` lies in every subgroup, so the degenerate
  -- case costs nothing and no completeness hypothesis is needed to state closure.
  refine (NonarchimedeanAddGroup.zeroAtFilter_cofinite_tsum_fiberwise
    (tendsto_mul_cofinite_nhds_zero hf hg) fun ab ↦ ab.1 + ab.2).congr fun _ ↦ ?_
  -- Mathlib's fibre `addFiber n` is the antidiagonal `{(i, j) | i + j = n}`.
  exact tsum_congr_set_coe (fun ab : ℤ × ℤ ↦ f ab.1 * g ab.2) <| Set.ext fun _ ↦ mem_addFiber.symm

/-- **The product on `A⟨X, X⁻¹⟩`**: the coefficient convolution `(fg)ₙ = ∑' k, aₖ b_{n-k}`, which
lands back in the submodule by `addConvolution_mem_twoSidedRestrictedSubmodule`. Only a
nonarchimedean ring topology is needed to *define* it; the ring axioms are
`twoSidedRestrictedSubmodule.instRing`. -/
noncomputable instance twoSidedRestrictedSubmodule.instMul :
    Mul (twoSidedRestrictedSubmodule A A) where
  mul f g := ⟨addConvolution (LinearMap.mul ℤ A) f g,
    addConvolution_mem_twoSidedRestrictedSubmodule f.2 g.2⟩

/-- **The unit of `A⟨X, X⁻¹⟩`** is the constant series `1 = 1 · X⁰`, i.e. the family supported at
degree `0`. -/
instance twoSidedRestrictedSubmodule.instOne : One (twoSidedRestrictedSubmodule A A) where
  one := ⟨Pi.single 0 1, single_mem_twoSidedRestrictedSubmodule 0 1⟩

/-- The product is the convolution of the coefficient families. The `Mul` instance's body is not
exposed, so this is how a product is computed outside this module. -/
@[simp, norm_cast]
theorem coe_mul_twoSidedRestrictedSubmodule (f g : twoSidedRestrictedSubmodule A A) :
    (↑(f * g) : ℤ → A) = addConvolution (LinearMap.mul ℤ A) f g := rfl

/-- The unit is the family supported at degree `0` with value `1`. The `One` instance's body is
not exposed, so this is how the unit is computed outside this module. -/
@[simp, norm_cast]
theorem coe_one_twoSidedRestrictedSubmodule :
    ((1 : twoSidedRestrictedSubmodule A A) : ℤ → A) = Pi.single 0 1 := rfl

/-- **The coefficient formula for a product**, on the submodule rather than on raw families:
`(fg)ₙ = ∑' k, aₖ b_{n-k}`. This is the form a consumer computing with elements of `A⟨X, X⁻¹⟩`
wants, and it needs no completeness — where the series fails to converge both sides are `0` by the
`tsum` convention. -/
@[simp]
theorem coe_mul_apply (f g : twoSidedRestrictedSubmodule A A) (n : ℤ) :
    ((f * g : twoSidedRestrictedSubmodule A A) : ℤ → A) n
      = ∑' k : ℤ, (f : ℤ → A) k * (g : ℤ → A) (n - k) := by
  rw [coe_mul_twoSidedRestrictedSubmodule, addConvolution_mul_apply]

/-- **The monomial `a Xⁿ`** of `A⟨X, X⁻¹⟩`: the family supported at degree `n` with value `a`.
Restrictedness is `single_mem_twoSidedRestrictedSubmodule`. -/
def twoSidedMonomial (n : ℤ) (a : A) : twoSidedRestrictedSubmodule A A :=
  ⟨Pi.single n a, single_mem_twoSidedRestrictedSubmodule n a⟩

/-- The coefficient family of the monomial `a Xⁿ` is `Pi.single n a`: the value `a` in degree `n`
and `0` elsewhere. The definition's body is not exposed, so this is how a monomial's coefficients
are read outside this module. -/
@[simp, norm_cast]
theorem coe_twoSidedMonomial (n : ℤ) (a : A) :
    (twoSidedMonomial n a : ℤ → A) = Pi.single n a := (rfl)

/-- The unit is the degree-`0` monomial `1 = 1 · X⁰`. -/
@[simp]
theorem twoSidedMonomial_zero_one : twoSidedMonomial 0 (1 : A) = 1 := (rfl)

end Convolution

section Monomial

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **Monomials multiply by adding degrees**: `(a Xᵐ)(b Xⁿ) = ab X^{m+n}`.

Only one term of the coefficient series is nonzero, so this needs neither completeness,
summability, nor a separation axiom — unlike the ring axioms themselves. It is the computation rule
for the Laurent expressions Wedhorn's §8.2.1 is written in. -/
@[simp]
theorem twoSidedMonomial_mul_twoSidedMonomial (m n : ℤ) (a b : A) :
    twoSidedMonomial m a * twoSidedMonomial n b = twoSidedMonomial (m + n) (a * b) := by
  ext p
  -- Only `k = m` contributes to `∑' k, (a Xᵐ)ₖ (b Xⁿ)_{p-k}`.
  rw [coe_mul_apply, coe_twoSidedMonomial, coe_twoSidedMonomial, coe_twoSidedMonomial,
    tsum_eq_single m fun k hk ↦ by simp [Pi.single_eq_of_ne hk]]
  -- What survives is `a · (b Xⁿ)_{p-m}`, which is `ab` exactly when `p = m + n`.
  rcases eq_or_ne p (m + n) with rfl | hp
  · simp
  · rw [Pi.single_eq_of_ne hp, Pi.single_eq_of_ne (by grind : p - m ≠ n), mul_zero]

end Monomial

section Summable

variable {A M : Type*} [Semiring A] [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [Module A M] [ContinuousConstSMul A M]

/-- **Restrictedness is summability** over a complete nonarchimedean group: a family lies in the
submodule exactly when it is summable. It is what turns Wedhorn's "the product of two such series
is well defined" into a theorem. -/
theorem mem_twoSidedRestrictedSubmodule_iff_summable {f : ℤ → M} :
    f ∈ twoSidedRestrictedSubmodule A M ↔ Summable f :=
  -- `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` read through the membership
  -- criterion: membership unfolds to cofinite nullity, which is that lemma's right-hand side.
  mem_twoSidedRestrictedSubmodule.trans
    (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f).symm

end Summable

section Ring

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A]

/-- **Each coefficient of a product is a convergent series** (Wedhorn's "the convergent series
`∑_{k + l = n} aₖ bₗ`"). -/
theorem summable_mul_sub_of_mem_twoSidedRestrictedSubmodule {f g : ℤ → A}
    (hf : f ∈ twoSidedRestrictedSubmodule A A) (hg : g ∈ twoSidedRestrictedSubmodule A A) (n : ℤ) :
    Summable fun k ↦ f k * g (n - k) :=
  -- Restrictedness *is* summability over a complete nonarchimedean ring, so
  -- `Summable.mul_of_nonarchimedean` makes `(i, j) ↦ aᵢbⱼ` summable on all of `ℤ × ℤ`.
  ((mem_twoSidedRestrictedSubmodule_iff_summable.mp hf).mul_of_nonarchimedean
    (mem_twoSidedRestrictedSubmodule_iff_summable.mp hg)).comp_injective
    -- The antidiagonal `k ↦ (k, n - k)` is a subfamily of `ℤ × ℤ`.
    (i := fun k ↦ (k, n - k)) fun _ _ hab ↦ (Prod.mk.inj hab).1

/-- **The convolution of two restricted families exists**, in the form Mathlib's distributivity
lemmas for `DiscreteConvolution.addConvolution` consume. -/
theorem addConvolutionExists_of_mem_twoSidedRestrictedSubmodule {f g : ℤ → A}
    (hf : f ∈ twoSidedRestrictedSubmodule A A) (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    AddConvolutionExists (LinearMap.mul ℤ A) f g :=
  -- The same subfamily argument as `summable_mul_sub_of_mem_twoSidedRestrictedSubmodule`, now on
  -- Mathlib's fibre `addFiber n`: `(i, j) ↦ aᵢbⱼ` is summable on all of `ℤ × ℤ`.
  fun _ ↦ ((mem_twoSidedRestrictedSubmodule_iff_summable.mp hf).mul_of_nonarchimedean
    (mem_twoSidedRestrictedSubmodule_iff_summable.mp hg)).subtype _

variable [T0Space A]

namespace twoSidedRestrictedSubmodule

/-- **`A⟨X, X⁻¹⟩` is a ring** (Wedhorn, Example 6.39). -/
noncomputable instance instRing : Ring (twoSidedRestrictedSubmodule A A) where
  __ := Submodule.addCommGroup _
  __ := instMul
  __ := instOne
  -- Associativity is the one ring axiom Mathlib's `DiscreteConvolution` lacks, so it is proved
  -- here rather than inherited. Both bracketings of `fgh` are the sum of `aᵢ bⱼ cₗ` over
  -- `{i + j + l = n}`; the proof is inline because the statement, once this instance exists, is
  -- exactly the standard `mul_assoc`.
  mul_assoc f g h := by
    ext n
    simp only [coe_mul_twoSidedRestrictedSubmodule, addConvolution_mul_apply]
    -- Index that fibre by `(m, k) ↦ (k, m - k, n - m)`, with `m` the degree of the partial product
    -- `fg`. It is a subfamily of `(i, j, l) ↦ aᵢbⱼcₗ`, which is summable on all of `ℤ × ℤ × ℤ`.
    have hF : Summable fun p : ℤ × ℤ ↦
        (f : ℤ → A) p.2 * (g : ℤ → A) (p.1 - p.2) * (h : ℤ → A) (n - p.1) :=
      (((mem_twoSidedRestrictedSubmodule_iff_summable.mp f.2).mul_of_nonarchimedean
        (mem_twoSidedRestrictedSubmodule_iff_summable.mp g.2)).mul_of_nonarchimedean
        (mem_twoSidedRestrictedSubmodule_iff_summable.mp h.2)).comp_injective
        (i := fun p : ℤ × ℤ ↦ ((p.2, p.1 - p.2), n - p.1)) fun p q hpq ↦ by grind
    -- Both bracketings are that single sum, summed in two orders: fibring over `m` gives `((fg)h)ₙ`
    -- by summing first over `k`, and fibring the reindexed family gives `(f(gh))ₙ`.
    refine (hF.hasSum.prod_fiberwise fun m ↦ ?_).tsum_eq.trans (HasSum.prod_fiberwise
        (f := fun q : ℤ × ℤ ↦ (f : ℤ → A) q.1 * ((g : ℤ → A) q.2 * (h : ℤ → A) (n - q.1 - q.2)))
        ?_ fun k ↦ ?_).tsum_eq.symm
    -- Fibre of `((fg)h)ₙ` over `m`: the `k`-series computing `(fg)ₘ`, scaled on the right by `h`.
    · exact (summable_mul_sub_of_mem_twoSidedRestrictedSubmodule f.2 g.2 m).hasSum.mul_right
        ((h : ℤ → A) (n - m))
    -- The reindexing `(m, k) ↦ (k, m - k)` is `Equiv.prodComm` followed by a shear; it carries `hF`
    -- to the family whose fibres give `(f(gh))ₙ`, with `mul_assoc` rebracketing each term.
    · refine ((Equiv.prodComm ℤ ℤ).trans ((Equiv.refl ℤ).prodShear Equiv.subRight)).hasSum_iff.mp ?_
      simpa [Function.comp_def, mul_assoc] using hF.hasSum
    -- Fibre of `(f(gh))ₙ` over `k`: the series computing `(gh)_{n - k}`, scaled on the left by `f`.
    · exact (summable_mul_sub_of_mem_twoSidedRestrictedSubmodule g.2 h.2 (n - k)).hasSum.mul_left
        ((f : ℤ → A) k)
  -- The unit laws are Mathlib's `single_addConvolution` and `addConvolution_single`, reached
  -- through the two coercion `simp` lemmas above.
  one_mul _ := Subtype.ext <| by simp
  mul_one _ := Subtype.ext <| by simp
  -- Distributivity is Mathlib's, fed by `addConvolutionExists_of_mem_twoSidedRestrictedSubmodule`:
  -- the coefficient series converge, so each sum may be split in two.
  left_distrib f g h := Subtype.ext <|
    (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2).distrib_add _
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 h.2)
  right_distrib f g h := Subtype.ext <|
    (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 h.2).add_distrib _
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule g.2 h.2)
  -- The two annihilation laws are Mathlib's, and need no convergence hypothesis.
  zero_mul _ := Subtype.ext <| zero_addConvolution _ _
  mul_zero _ := Subtype.ext <| addConvolution_zero _ _

end twoSidedRestrictedSubmodule

/-- **The Laurent variable is a unit**, with inverse the degree-`(-1)` monomial. This is the form
Wedhorn's Example 6.39 is used in — `A⟨X, X⁻¹⟩` is the ring in which `X` becomes invertible — and it
is stated here rather than beside the two multiplication identities because `IsUnit` needs a monoid,
which arrives only with `twoSidedRestrictedSubmodule.instRing`. -/
theorem isUnit_twoSidedMonomial_one : IsUnit (twoSidedMonomial 1 (1 : A)) :=
  -- both inverse identities are `twoSidedMonomial_mul_twoSidedMonomial` at `(1, -1)` and `(-1, 1)`,
  -- finished by `twoSidedMonomial_zero_one`
  ⟨⟨twoSidedMonomial 1 1, twoSidedMonomial (-1) 1, by simp, by simp⟩, rfl⟩

end Ring

section CommRing

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A]

namespace twoSidedRestrictedSubmodule

/-- **`A⟨X, X⁻¹⟩` is commutative when `A` is** (Wedhorn, Example 6.39). -/
noncomputable instance instCommRing : CommRing (twoSidedRestrictedSubmodule A A) where
  __ := instRing
  -- Commutativity is Mathlib's `addRingConvolution_comm`, which swaps the two coordinates of each
  -- antidiagonal.
  mul_comm f g := Subtype.ext <| addRingConvolution_comm (f : ℤ → A) g

/-- **`A⟨X, X⁻¹⟩` is an `A`-algebra** (Wedhorn, Example 6.39), with the scalar action it already
carries as a submodule of `ℤ → A`. The instance's body is not exposed; its structure map is
`coe_algebraMap_twoSidedRestrictedSubmodule`. -/
noncomputable instance instAlgebra : Algebra A (twoSidedRestrictedSubmodule A A) :=
  -- Scalars pass through each coefficient series: our product is definitionally Mathlib's
  -- `addRingConvolution`,
  -- so `smul_addRingConvolution` and `addRingConvolution_smul` are the two hypotheses, fed by
  -- `addConvolutionExists_of_mem_twoSidedRestrictedSubmodule`.
  Algebra.ofModule
    (fun r f g ↦ Subtype.ext <| smul_addRingConvolution r _ _ <|
      addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2)
    fun r f g ↦ Subtype.ext <| addRingConvolution_smul r _ _ <|
      addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2

end twoSidedRestrictedSubmodule

/-- The structure map sends `a` to the constant series `a = a · X⁰`. It characterises
`twoSidedRestrictedSubmodule.instAlgebra`, whose body is not exposed. -/
@[simp, norm_cast]
theorem coe_algebraMap_twoSidedRestrictedSubmodule (a : A) :
    (algebraMap A (twoSidedRestrictedSubmodule A A) a : ℤ → A) = Pi.single 0 a := by
  -- The structure map is `a • 1` for the submodule's own scalar action, so it is a `Pi.single`.
  simp [Algebra.algebraMap_eq_smul_one, ← Pi.single_smul]

end CommRing

end TauCeti.Huber
