module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.compactCost`

Asserted, not proved, by reading `Operations/Compact.lean` and the files under it. `rep` finds
each column's least equal column, `h` columns against `h` at `p` exponents each; `fiberSum`
gathers each class, at most `h` additions at `Vec ℝ n` per column; `compactKeep` tests each
generator against zero; `usedFactors` scans every exponent once. Everything is bounded at the
*full* width, which keeps it an upper bound without a hypothesis on collisions. The writes are
those of the operand's size: the center, both generator blocks and the exponent matrix.

## Inputs
* `n` – dimension
* `p` – number of factors
* `h` – dependent generator count
* `q` – independent generator count

## Output
* operation count of compacting
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.compact` costs at `Vec ℝ n` over `p` factors, `h` dependent and `q`
independent generators: the pairwise merge, the class sums and the factor scan, and
`n * (1 + h + q) + p * h` writes for the result. -/
def PolyZonotope.compactCost (n p h q : ℕ) : Cost :=
  ⟨(p + n + 1) * (h * h) + (p + n) * h + (n * (1 + h + q) + p * h)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
