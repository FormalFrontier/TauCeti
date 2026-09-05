/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# The shift `c • x - A x` of a partial linear map as a linear map on its domain

For a partial linear map `A : E →ₗ.[R] E` and a scalar `c`, the shift `x ↦ c • x - A x` is a
linear map from the domain of `A` to `E`.  Bundling it (`LinearPMap.smulSub`) gives access to the
`LinearMap` API, in particular to its range as a submodule, for arguments about resolvents,
deficiency shifts and dissipativity, where surjectivity or density of this range is the question.
Up to sign it is the scalar shift `TauCeti.LinearPMap.subScalar A c = A - c • 1` of
`TauCeti.Analysis.Normed.Operator.LinearPMap.Shift`, regarded as a linear map on the domain; the
relation is recorded next to that file, in
`TauCeti.Analysis.Normed.Operator.LinearPMap.SmulSub` (`smulSub_apply_eq_neg_subScalar`).

## Main declarations

* `LinearPMap.smulSub`: the bundled shift `x ↦ c • x - A x` on the domain of `A`.
* `LinearPMap.smulSub_apply` and `LinearPMap.coe_range_smulSub`: its values and its range.
-/

public section

namespace LinearPMap

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- The shift `x ↦ c • x - A x` of a partial linear map, as a linear map on the domain of `A`. -/
def smulSub (c : R) (A : E →ₗ.[R] E) : A.domain →ₗ[R] E :=
  c • A.domain.subtype - A.toFun

@[simp]
theorem smulSub_apply (c : R) (A : E →ₗ.[R] E) (x : A.domain) :
    A.smulSub c x = c • (x : E) - A x :=
  (rfl)

/-- The range of the bundled shift is the range of the shift. -/
theorem coe_range_smulSub (c : R) (A : E →ₗ.[R] E) :
    ((A.smulSub c).range : Set E) = Set.range (fun x : A.domain => c • (x : E) - A x) := by
  ext y
  simp only [SetLike.mem_coe, LinearMap.mem_range, smulSub_apply, Set.mem_range]

end LinearPMap

end
