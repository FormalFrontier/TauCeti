/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean spheres

This module defines standard Euclidean unit spheres $S^n \subset \mathbb{R}^{n+1}$.

## Main definitions

* `TauCeti.EuclideanSphere`: the unit sphere $S^n = \mathrm{sphere}(0, 1)$ in $\mathbb{R}^{n+1}$.
* `TauCeti.Sphere3`: the standard 3-sphere $S^3 \subset \mathbb{R}^4$.
-/

public section

noncomputable section

open Metric

namespace TauCeti

/-- The standard $n$-sphere $S^n \subset \mathbb{R}^{n+1}$ as a subset of Euclidean space. -/
public abbrev EuclideanSphere (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The standard 3-sphere $S^3 \subset \mathbb{R}^4$ as a subset of Euclidean space. -/
public abbrev Sphere3 : Type := EuclideanSphere 3

end TauCeti
