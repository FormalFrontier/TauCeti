/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Path
public import TauCeti.Topology.JordanCurve.Basic
import TauCeti.Topology.JordanCurve.Path

/-!
# The coincident-end case of an image crosscut

A genuine circular crosscut of a disc is carried by a conformal map to a simple open arc in the
image domain. When its image has finite length,
`TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn` packages the closure of
that arc as the range of a path. The path's interior is injective, its interior values lie in the
image domain, and its two endpoints lie on the image boundary, so the only repetition it may have
is a common value of those endpoints.

This file settles that exceptional case. If the closed image crosscut meets the boundary of the
image domain in a subsingleton, both path endpoints must be that same boundary point. The path is
therefore closed, and `TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints` identifies its range —
the closure of the image crosscut — as a Jordan curve.

The subsingleton hypothesis is deliberately literal. The endpoint theorem in
`Conformal/Crosscut/BoundaryEnds.lean` shows that the boundary intersection is a pair `{u, v}`, but
does not prove the two points distinct; asserting distinctness here would assume the planar
separation argument that remains to be formalized. Instead this theorem gives the exact conclusion
in the coincident-end branch, with no weakened or surrogate separation claim. The complementary
branch, in which the boundary intersection is *not* a subsingleton and the closed image crosscut is
an arc, is `Conformal/Crosscut/Arc.lean`.

## Main result

* `TauCeti.isJordanCurve_closure_image_ball_inter_sphere_of_subsingleton` — if a finite-length
  image crosscut has at most one boundary end, its closure is a Jordan curve.

## Roadmap role

This advances layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, the Jordan-domain case of
the Carathéodory boundary correspondence. The existing length-area machinery produces arbitrarily
short image crosscuts and the existing path theorem supplies their simple parametrisations. The
remaining step after this file is the planar separation argument: treat the Jordan curve produced
here when the ends coincide, and join the crosscut to one of the two boundary arcs when they are
distinct, in order to bound the whole boundary of the cut-off image piece. The joining itself is
`Conformal/Crosscut/Arc.lean`; what is left is the choice of boundary arc.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Complex Metric Set

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-- **A finite-length image crosscut with a single boundary end closes to a Jordan curve.**
Let `f` be holomorphic and injective on `ball c r`, and let `ball c r ∩ sphere ζ ρ` be a genuine
circular crosscut whose image has finite length. If the intersection

`frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))`

is a subsingleton, then the closure of the image crosscut is a Jordan curve.

The hypothesis says only that the two endpoint limits supplied by the finite-length theorem agree.
It makes no assertion about the rest of the image boundary or about which planar region the closed
curve encloses. -/
theorem isJordanCurve_closure_image_ball_inter_sphere_of_subsingleton
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤)
    (hends : (frontier (f '' ball c r) ∩
      closure (f '' (ball c r ∩ sphere ζ ρ))).Subsingleton) :
    IsJordanCurve (closure (f '' (ball c r ∩ sphere ζ ρ))) := by
  obtain ⟨u, v, γ, hγrange, -, -, hu, hv, hγsimple, -⟩ :=
    exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn hζ hρ hρr hf hinj hfin
  have hu' : u ∈ frontier (f '' ball c r) ∩
      closure (f '' (ball c r ∩ sphere ζ ρ)) := by
    refine ⟨hu, ?_⟩
    rw [← hγrange]
    exact ⟨0, γ.source⟩
  have hv' : v ∈ frontier (f '' ball c r) ∩
      closure (f '' (ball c r ∩ sphere ζ ρ)) := by
    refine ⟨hv, ?_⟩
    rw [← hγrange]
    exact ⟨1, γ.target⟩
  have huv : u = v := hends hu' hv'
  subst v
  rw [← hγrange]
  exact isJordanCurve_range_of_eq_or_eq_endpoints γ hγsimple

end TauCeti
