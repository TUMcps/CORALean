module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# The set a continuous run visits over an interval

The definition is [1, Def. 3.2]: the union of `LinearSys.reachSetExact` at every time in
`[0, r]`. `timeIntervalReachSetExact_eq_iUnion` is that union, read back off this definition.
Written the same way `reachSetExact` is, an existential over a trajectory, rather than as a
literal `Set.iUnion`: a caller already holding a trajectory and a time reaches either with
the same pair. `[0, r]` only, as `timeInterval` and the whole-step theorems it is the
exact counterpart of, rather than an arbitrary sub-interval of `T`.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `r` – interval end

## Output
* states some trajectory is in at some time of the interval, exactly

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some trajectory of `sys` on `T` from `R₀` with inputs in `U` is
at, at some time in `[0, r]`: the exact reachable set over the interval, and
not an enclosure of it. -/
def LinearSys.timeIntervalReachSetExact (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n) (r : ℝ) :
    Set (Vec ℝ n) :=
  {y | ∃ x u : ℝ → Vec ℝ n, sys.IsCanonicalTrajectory T R₀ U x u ∧ ∃ t ∈ Set.Icc (0:ℝ) r, x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
