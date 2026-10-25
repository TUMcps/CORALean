module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.OfEntryBounds

@[expose] public section

/-!
# `Zonotope.minkDiffStretch`, over a floating-point scalar

The float counterpart of `Real.Zonotope.minkDiffStretch`: the generator representation [1, Thm. 4]
and [1, Thm. 5] share, the centers subtracted and each generator of the minuend stretched by its own
factor `μᵢ`. Rounded *outward*: the center and every scaled generator entry are bracketed by their
two directed roundings, and `ofEntryBounds` stores the lower bounds and pays the gaps into the box.
So the result encloses the real stretched zonotope at the same `μ`, which [1, Thm. 5]'s
over-approximation needs (`minkDiffStretch_outer`). The under-approximation [1, Thm. 4] needs the
opposite direction, which no outward rounding gives: `minkDiffStretchInner` certifies this result
instead. `μ` is an argument, as at the real layer; the guarantees ask only that it be feasible.

## Inputs
* `Z₁` – minuend zonotope
* `Z₂` – subtrahend zonotope
* `μ` – stretch per generator

## Output
* difference center with the stretched generators

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(c⁽ᵐ⁾ - c⁽ˢ⁾, Ĝ⁽ᵐ⁾µ)`, [1, Thm. 4] and [1, Thm. 5]'s shared generator representation, each
entry bracketed and the gaps paid into the box. -/
def Zonotope.minkDiffStretch (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (μ : Fin Z₁.h → 𝕋) : Zonotope (Vec 𝕋 n) :=
  let cLo := fun r => subDown (Z₁.c r) (Z₂.c r)  -- c₁ - c₂, rounded down
  let cHi := fun r => subUp (Z₁.c r) (Z₂.c r)  -- c₁ - c₂, rounded up
  let GLo : Mat 𝕋 n Z₁.h := fun r i => mulDown (μ i) (Z₁.G i r)  -- μᵢ gᵢ, rounded down
  let GHi : Mat 𝕋 n Z₁.h := fun r i => mulUp (μ i) (Z₁.G i r)  -- μᵢ gᵢ, rounded up
  Zonotope.ofEntryBounds cLo cHi GLo GHi (Interval.origin n)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
