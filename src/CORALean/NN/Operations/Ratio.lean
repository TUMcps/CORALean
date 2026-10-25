module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `n̂_k / n_k`: a count over a count, in the scalar

[1, Alg. 1] compares the fraction of neurons a bucket leaves against the rate `ρ`, and
`FloatOps` has counts only through repeated addition. The numerator rounds down and the
denominator up, so the quotient is never above the exact one; nothing depends on that
direction — the fraction only decides which buckets come out, never whether they are sound.

## Inputs
* `a` – numerator count
* `b` – denominator count

## Output
* quotient of the two counts as a scalar

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a / b` for two counts, as a scalar. -/
def ratio (a b : ℕ) : 𝕋 := divDown (nsmulDown a one) (nsmulUp b one)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
