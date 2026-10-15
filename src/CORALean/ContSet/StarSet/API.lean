module

public import CORALean.ContSet.StarSet.Real.API
public import CORALean.ContSet.StarSet.Float.API

/-!
# Star sets

The star set `{c + G α | C α ≤ d, l ≤ α ≤ u}` of CORA's neural-network evaluation of a
constrained zonotope: a zonotope's generators over factors cut down by linear rows and boxed by
`l` and `u`. The predicate is linear, so the set is a bounded polytope, exactly the sets a
`ConZonotope` denotes (`Conversion/`); what the representation adds is the form a network layer
steps through, a factor appended with its rows.

Over ℝ and over a floating-point scalar. The float layer stores the same fields in `𝕋` and an
error box, and an operation pays its rounding into the box.
-/
