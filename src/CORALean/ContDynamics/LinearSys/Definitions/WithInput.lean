module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# A continuous-time system paired with its input set

The input set `U` a `IsTrajectory` draws from is bundled with the system rather than taken from
CORA's `params.U`, because `0 ∈ U` is a proof about it that `params` cannot carry;
`Reach LinearSys.WithInput` reads it off the system it is asked about, exactly as it reads `sys.A`.
`0 ∈ U` is a field, the hypothesis [1, Prop. 4]'s proof takes: with the origin admissible, what
the input contributes only grows with time (`inputReach_mono`), so one accumulated set serves a
whole window. An input set off the origin is split as in [2, Eq. 4], a constant first:
`LinearSys.WithInputSplit`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". In Proc. of the European Control Conference
      (ECC), pp. 625-630, 2009.
* [2] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


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
