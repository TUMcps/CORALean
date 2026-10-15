module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.compactCost`

Asserted, not proved, by reading `Operations/Compact.lean` and the four files
under it. `rep` finds each column's least equal column, which is `h` columns
compared against `h` at `p` exponents each; `fiberSum` gathers each class, `h`
index tests and at most `h` generator additions at `Vec ℝ n` per column;
`compactKeep` tests each merged generator against zero, `n` comparisons a
column; and `usedFactors` scans every exponent once, `p * h`.

Everything here is bounded at the *full* width rather than the class's, which
is what keeps it an upper bound without a hypothesis on how the columns
happen to collide. Quadratic in `h` either way: this is a pairwise merge, and a
sorted or hashed one would be a different definition and a different count.

The result has at most as many generators as the operand, so the writes are those of the
operand's size: the center, both generator blocks and the exponent matrix.
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
