module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.dependentCost`

Asserted, not proved, and no longer zero: `Operations/Dependent.lean` concatenates the two
generator blocks and lays `identE` beside the exponent matrix. Every entry of either is one the
operand already held or a literal `0` or `1`, so nothing is computed, but the result is a new
object and each of its entries is a write: the center and `h + q` generators of `n` entries, and
the `(p + q)` by `(h + q)` exponent matrix, zeros included.

`quadMapCost` is `dependentCost` plus `quadMapDepCost` at the shifted counts. What the
conversion does cost the caller is also size — `p + q` factors and `h + q` dependent generators,
proved in `Complexity/Space/Theorems/DependentP.lean` — and every count downstream is evaluated
there.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.dependent` costs at `Vec ℝ n` over `p` factors, `h` dependent and `q`
independent generators: one write for each of the `n * (1 + h + q) + (p + q) * (h + q)` entries
of the result. -/
def PolyZonotope.dependentCost (n p h q : ℕ) : Cost :=
  ⟨n * (1 + h + q) + (p + q) * (h + q)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
