module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Ellipsoid.plusCost`

Asserted, not proved: `Operations/Plus.lean` squares the two scalings (2 multiplications),
multiplies every entry of both shape matrices by one (`2 n²`), adds the two (`n²` additions) and
adds the centers (`n` more). Every computed entry is also written once: `2 + 3 n² + n` writes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Ellipsoid.plus` costs at `Vec ℝ n`: its arithmetic, `3 n² + n + 2`, and one write per
computed entry, as many again. -/
def Ellipsoid.plusCost (n : ℕ) : Cost := ⟨2 * (3 * (n * n) + n + 2)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
