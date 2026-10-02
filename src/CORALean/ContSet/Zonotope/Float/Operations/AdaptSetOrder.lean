import CORALean.ContSet.Zonotope.Float.Operations.AdaptSetOrderLoop

/-!
# `Alg. 3` in floats: the order to reduce the particular solution to

`Real.Zonotope.adaptSetOrder` computed in `𝕋`: the share `ε_S,max,i` of
eq. (13) for a step of length `Δt`, the loop from `param(PR)` (`Z.h`, which
drops no generator), and the error `ε_S` accumulates, eq. (12). The times and
errors are ℚ, exact; the step is read back through `ToRat`. Which order comes
out affects how tight the result is, never whether it is sound: every order is
a `reduce`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the order to reduce `PR([0,t_{i+1}])` to, and the `ε_S` that
reduction accumulates. -/
def Zonotope.adaptSetOrder (Z : Zonotope 𝕋 n) (εSmax εSacc tf ti : ℚ) (Δt : 𝕋) : ℕ × ℚ :=
  let εSi := (εSmax - εSacc) / (tf - ti) * ToRat.toRat Δt   -- 1. the admissible share, eq. (13)
  let Φset := Z.h                                          -- 2. param(PR), reducing nothing
  let Φset' := Z.adaptSetOrderLoop εSi Φset Φset           -- 3.-7. decrement while admissible
  (Φset', εSacc + ToRat.toRat (Z.reduceGirardBox Φset').errOp)  -- 8. accumulate, eq. (12)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
