module

@[expose] public section

/-!
# What `oneStep` returns

`StepSets`: the two sets CORA's `oneStep` computes for one step `Δt` of a linear system
[1, Sec. 3.3], the time-point set `Rtp` of the state at the end of the step and the
time-interval set `Rti` of the states at every time of it.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The time-point and the time-interval set of one step, in the set family `S`. -/
structure LinearSys.StepSets (S : Type) where
  /-- `Rtp`: contains the state at the end of the step. -/
  Rtp : S
  /-- `Rti`: contains the state at every time of the step. -/
  Rti : S

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
