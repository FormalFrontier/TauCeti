/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.TameMetric

/-!
# Metrics of direct sums of tame and compatible pairs

`TauCeti.Geometry.Symplectic.Prod.Basic` records that direct sums preserve tameness and
compatibility. This file records the matching normal forms: the symmetrized bilinear form of a
direct sum is the sum of the factor symmetrized forms, the symmetric metric of a tame direct sum is
the sum of the factor symmetric metrics, and the compatible metric of a compatible direct sum is the
sum of the factor compatible metrics.

These are pointwise linear-algebra facts for the analytic Heegaard Floer roadmap. Product
compatible triples are the local models used before passing to product manifolds and, later,
symmetric-product geometry; the lemmas here let downstream energy and metric estimates reduce a
direct-sum target to its two factors without unfolding the product symplectic form or either
inner-product core.

## Main declarations

* `TauCeti.SymplecticForm.prod_symmetrizedBilinForm_apply`: the symmetrized bilinear form of a
  direct sum is the sum of the factor symmetrized bilinear forms.
* `TauCeti.SymplecticForm.Tames.prod_innerProductCore_inner`: the packaged tame inner product
  of a direct sum evaluates as the sum of the two factor packaged tame inner products.
* `TauCeti.SymplecticForm.Tames.prod_innerProductCore_inner_inl` and
  `TauCeti.SymplecticForm.Tames.prod_innerProductCore_inner_inr`: the coordinate inclusions
  recover the factor tame metrics.
* `TauCeti.SymplecticForm.Tames.prod_innerProductCore_inner_inl_inr`: the two coordinate
  summands are orthogonal for the direct-sum tame metric.
* `TauCeti.SymplecticForm.Compatible.prod_innerProductCore_inner`: the analogous formula for
  compatible metrics.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: products of compatible triples carry the product metric.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}
variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}

/-- The symmetrized bilinear form of a direct sum is the direct sum of the factor symmetrized
bilinear forms.

Not a `simp` lemma: the `simp` lemma `symmetrizedBilinForm_apply` already rewrites the
left-hand side, and the two rewrites reach sums grouped differently, so marking both would
make the `simp` normal form depend on which lemma fires first. -/
lemma prod_symmetrizedBilinForm_apply (p q : V × W) :
    (ω₁.prod ω₂).symmetrizedBilinForm (J₁.prod J₂) p q =
      ω₁.symmetrizedBilinForm J₁ p.1 q.1 + ω₂.symmetrizedBilinForm J₂ p.2 q.2 := by
  rw [symmetrizedBilinForm_apply, symmetrizedBilinForm_apply, symmetrizedBilinForm_apply,
    prod_apply, prod_apply, AlmostComplexStructure.prod_apply, AlmostComplexStructure.prod_apply]
  abel

namespace Tames

variable (h₁ : ω₁.Tames J₁) (h₂ : ω₂.Tames J₂)

/-- The packaged tame inner product of a direct sum is the sum of the two packaged tame inner
products.

Not a `simp` lemma: the `simp` lemma `Tames.innerProductCore_inner` already rewrites the
left-hand side, and the two rewrites reach sums grouped differently, so marking both would
make the `simp` normal form depend on which lemma fires first. Use this as a named reduction
to the factor metrics. -/
lemma prod_innerProductCore_inner (p q : V × W) :
    @inner ℝ (V × W) (prod_tames h₁ h₂).innerProductCore.toInner p q =
      @inner ℝ V h₁.innerProductCore.toInner p.1 q.1 +
        @inner ℝ W h₂.innerProductCore.toInner p.2 q.2 := by
  calc
    @inner ℝ (V × W) (prod_tames h₁ h₂).innerProductCore.toInner p q =
        (ω₁.prod ω₂) p ((J₁.prod J₂) q) + (ω₁.prod ω₂) q ((J₁.prod J₂) p) :=
      Tames.innerProductCore_inner (prod_tames h₁ h₂) p q
    _ =
        (ω₁.prod ω₂).symmetrizedBilinForm (J₁.prod J₂) p q := by
      rw [symmetrizedBilinForm_apply]
    _ = ω₁.symmetrizedBilinForm J₁ p.1 q.1 + ω₂.symmetrizedBilinForm J₂ p.2 q.2 :=
      prod_symmetrizedBilinForm_apply p q
    _ = @inner ℝ V h₁.innerProductCore.toInner p.1 q.1 +
          @inner ℝ W h₂.innerProductCore.toInner p.2 q.2 := by
      rw [Tames.innerProductCore_inner, Tames.innerProductCore_inner,
        symmetrizedBilinForm_apply, symmetrizedBilinForm_apply]

/-- The first coordinate inclusion is isometric for the packaged tame product metric. -/
lemma prod_innerProductCore_inner_inl (v v' : V) :
    @inner ℝ (V × W) (prod_tames h₁ h₂).innerProductCore.toInner (v, 0) (v', 0) =
      @inner ℝ V h₁.innerProductCore.toInner v v' := by
  simp [prod_innerProductCore_inner h₁ h₂]

/-- The second coordinate inclusion is isometric for the packaged tame product metric. -/
lemma prod_innerProductCore_inner_inr (w w' : W) :
    @inner ℝ (V × W) (prod_tames h₁ h₂).innerProductCore.toInner (0, w) (0, w') =
      @inner ℝ W h₂.innerProductCore.toInner w w' := by
  simp [prod_innerProductCore_inner h₁ h₂]

/-- The two coordinate summands are orthogonal for the packaged tame product metric. -/
lemma prod_innerProductCore_inner_inl_inr (v : V) (w : W) :
    @inner ℝ (V × W) (prod_tames h₁ h₂).innerProductCore.toInner (v, 0) (0, w) = 0 := by
  simp [prod_innerProductCore_inner h₁ h₂]

/-- The reverse coordinate orthogonality for the packaged tame product metric. -/
lemma prod_innerProductCore_inner_inr_inl (w : W) (v : V) :
    @inner ℝ (V × W) (prod_tames h₁ h₂).innerProductCore.toInner (0, w) (v, 0) = 0 := by
  simp [prod_innerProductCore_inner h₁ h₂]

end Tames

namespace Compatible

variable (h₁ : ω₁.Compatible J₁) (h₂ : ω₂.Compatible J₂)

/-- The packaged compatible inner product of a direct sum is the sum of the two factor packaged
compatible inner products.

Not a `simp` lemma: the `simp` lemma `Compatible.innerProductCore_inner` already rewrites the
left-hand side, so this lemma would never fire from the default `simp` set. Use it as a named
reduction to the factor metrics. -/
lemma prod_innerProductCore_inner (p q : V × W) :
    @inner ℝ (V × W) (prod_compatible h₁ h₂).innerProductCore.toInner p q =
      @inner ℝ V h₁.innerProductCore.toInner p.1 q.1 +
        @inner ℝ W h₂.innerProductCore.toInner p.2 q.2 := by
  calc
    @inner ℝ (V × W) (prod_compatible h₁ h₂).innerProductCore.toInner p q =
        (ω₁.prod ω₂) p ((J₁.prod J₂) q) :=
      Compatible.innerProductCore_inner (prod_compatible h₁ h₂) p q
    _ =
        (ω₁.prod ω₂).associatedBilinForm (J₁.prod J₂) p q := by
      rw [associatedBilinForm_apply]
    _ = ω₁.associatedBilinForm J₁ p.1 q.1 + ω₂.associatedBilinForm J₂ p.2 q.2 :=
      prod_associatedBilinForm_apply ω₁ ω₂ p q
    _ = @inner ℝ V h₁.innerProductCore.toInner p.1 q.1 +
          @inner ℝ W h₂.innerProductCore.toInner p.2 q.2 := by
      rw [Compatible.innerProductCore_inner, Compatible.innerProductCore_inner,
        associatedBilinForm_apply, associatedBilinForm_apply]

/-- The first coordinate inclusion is isometric for the packaged compatible product metric. -/
lemma prod_innerProductCore_inner_inl (v v' : V) :
    @inner ℝ (V × W) (prod_compatible h₁ h₂).innerProductCore.toInner (v, 0) (v', 0) =
      @inner ℝ V h₁.innerProductCore.toInner v v' := by
  simp [prod_innerProductCore_inner h₁ h₂]

/-- The second coordinate inclusion is isometric for the packaged compatible product metric. -/
lemma prod_innerProductCore_inner_inr (w w' : W) :
    @inner ℝ (V × W) (prod_compatible h₁ h₂).innerProductCore.toInner (0, w) (0, w') =
      @inner ℝ W h₂.innerProductCore.toInner w w' := by
  simp [prod_innerProductCore_inner h₁ h₂]

/-- The two coordinate summands are orthogonal for the packaged compatible product metric. -/
lemma prod_innerProductCore_inner_inl_inr (v : V) (w : W) :
    @inner ℝ (V × W) (prod_compatible h₁ h₂).innerProductCore.toInner (v, 0) (0, w) = 0 := by
  simp [prod_innerProductCore_inner h₁ h₂]

/-- The reverse coordinate orthogonality for the packaged compatible product metric. -/
lemma prod_innerProductCore_inner_inr_inl (w : W) (v : V) :
    @inner ℝ (V × W) (prod_compatible h₁ h₂).innerProductCore.toInner (0, w) (v, 0) = 0 := by
  simp [prod_innerProductCore_inner h₁ h₂]

end Compatible

end SymplecticForm

end TauCeti
