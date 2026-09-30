import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# A continuous-time system paired with its input set

The input set `U` a `Trajectory` draws from is bundled with the system rather
than taken from CORA's `params.U`, because `0 ∈ U` is a proof about it that
`params` cannot carry; `Reach LinearSys.WithInput` reads it off the system it is
asked about, exactly as it reads `sys.A`.

`0 ∈ U` is a field, being [1, Alg. 2]'s own precondition: with the origin
admissible, what the input contributes only grows with time (`inputReach_mono`),
so one accumulated set serves a whole window. An input set off the origin is
[1, Alg. 3], a constant split off first: `LinearSys.WithInputSplit`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- A `LinearSys` paired with the input set every run draws from, which holds
the origin. -/
structure LinearSys.WithInput (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  sys : LinearSys 𝕋 n
  U : S n
  zero_mem_U : (0 : Vec ℝ n) ∈ construct U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
