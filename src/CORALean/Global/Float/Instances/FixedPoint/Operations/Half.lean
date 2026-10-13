import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

/-!
# Halving

Exact, at one more digit: `⟨m, d⟩ ↦ ⟨5m, d + 1⟩`, since `m / 10 ^ d / 2 = 5m /
10 ^ (d + 1)`. `FloatOps.half` has to stay exact, so the interface leaves no
other way to halve a decimal mantissa without inventing a digit `10` does not
already have.

Digits only grow this way -- every other rounded operation below cuts back to
`f` -- so repeated halving adds one digit per call (`half^[k] x` sits at
`x.d + k`) and the next `addUp`/`mulDown`/`divUp`/... applied to the result
rounds it back to `f`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace FixedPoint

variable {f : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact, at one more digit: `m / 10 ^ d / 2 = 5m / 10 ^ (d + 1)`. -/
def half (x : FixedPoint f) : FixedPoint f := ⟨5 * x.m, x.d + 1⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
