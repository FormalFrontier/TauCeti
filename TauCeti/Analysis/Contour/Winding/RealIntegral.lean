/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.RealIntegral.Basic
public import TauCeti.Analysis.Contour.Winding.RealIntegral.OnCurve

/-!
# The real bounded-integrand formula for the winding number

This module re-exports the real bounded-integrand formula for the winding number: the avoiding
case (`TauCeti.Analysis.Contour.Winding.RealIntegral.Basic`) and the case allowing interior
crossings (`TauCeti.Analysis.Contour.Winding.RealIntegral.OnCurve`). It declares nothing of its
own, and keeps the import path `TauCeti.Analysis.Contour.Winding.RealIntegral` — which named the
single file before it split into a directory — working.
-/
