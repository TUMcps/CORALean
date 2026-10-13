import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# A continuous-time system paired with an input set anywhere

`LinearSys.WithInput` without `0 ∈ U`: [1, Alg. 3]'s case, the input set taken
apart into a constant `ũ` and a remainder `Ũ` holding the origin before any
window is computed. The split is the representation's, by `Recentre`, so no
field here names it; `Reach LinearSys.WithInputSplit` asks the representation
for `Recentre` and `OfPoint` instead. `WithInput` stays for representations
without a centre, where `0 ∈ U` is the precondition [1, Alg. 2] asks.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A `LinearSys` paired with the input set every run draws from, wherever it
sits. -/
structure LinearSys.WithInputSplit (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  sys : LinearSys 𝕋 n
  U : S n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
