import CORALean.Global.Float.FloatOps

/-!
# `n̂_k / n_k`: a count over a count, in the scalar

[1, Alg. 1] compares the fraction of neurons a bucket leaves against the rate `ρ`, and
`FloatOps` has counts only through repeated addition. The numerator rounds down and the
denominator up, so the quotient is never above the exact one; nothing depends on that
direction — the fraction only decides which buckets come out, never whether they are sound.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a / b` for two counts, as a scalar. -/
def ratio (a b : ℕ) : 𝕋 := divDown (nsmulDown a one) (nsmulUp b one)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
