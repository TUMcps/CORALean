module

public import CORALean.ContSet.Capsule.Real.Operations.SupportBound
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Capsule.supportBoundCost`

Asserted, not proved: `Operations/SupportBound.lean` bounds `f` over the
capsule by `f c + |f g| + r * ‖w‖₂`, where `w` is `f` read on the `n` basis
vectors. Evaluating `f` is a parameter `cf`, as for `mapCost`: `f c`, `f g` and
the `n` basis evaluations, `n + 2` in all; then `n` squares, `n - 1` additions,
a `sqrt`, an `abs`, a product and two additions, bounded by `2 * n + 5`, and one write of the bound.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.supportBound` costs at `Vec ℝ n`, one evaluation of `f` costing at most `cf`:
the evaluations, the arithmetic and one write of the bound. -/
def Capsule.supportBoundCost (cf : Cost) (n : ℕ) : Cost := (n + 2) • cf + ⟨2 * n + 6⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
