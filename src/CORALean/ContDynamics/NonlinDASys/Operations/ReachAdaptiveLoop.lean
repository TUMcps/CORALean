module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAdaptive
public import CORALean.ContDynamics.NonlinDASys.Operations.AdaptPassLinPoint
public import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptState

@[expose] public section

/-!
# `NonlinDASys.reachAdaptiveLoop`

The `while` loop of CORA's `reach_adaptive` ([1, Alg. 1]) until the final time is
reached to within `tol`, the time-interval sets collected in a union. A step that is not
positive or overshoots ends the loop with `none` (CORA asserts `timeStep > 0` and caps the
horizon by the time left); `fuel` replaces the unbounded loop. The order reduction (`reduce`,
which only enlarges), `aux_checkForAbortion` and the algebraic and time-point lists are left
out.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop of `reach_adaptive` from the state `st` with the union `Runion` so far. -/
noncomputable def NonlinDASys.reachAdaptiveLoop (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (U : Zonotope (Vec ℝ m)) (tFinal tol : ℝ)
    (η fuelErr fuelHalf : ℕ) :
    ℕ → NonlinDASys.AdaptState n p → Set (Vec ℝ n) → Option (Set (Vec ℝ n) × ℝ)
  | 0, st, Runion => if tFinal - st.t ≤ tol then some (Runion, st.t) else none
  | fuel + 1, st, Runion =>
    if tol < tFinal - st.t then                                            -- tFinal - t > 1e-12
      let lastStep : Bool := decide (tFinal - st.t < st.h)                 -- Δt > tFinal - t
      let h : ℝ := min st.h (tFinal - st.t)                                -- capped by time left
      match sys.linReachAdaptive T st.R U η fuelErr fuelHalf st.adm_x st.adm_y h lastStep with
      | none => none
      | some pass =>
        if 0 < pass.Δt ∧ pass.Δt ≤ tFinal - st.t then
          let L := T.taylor st.R                                           -- priv_linearize
          let Rnext := NonlinDASys.linReachAt sys (pass.linPoint L)        -- Rnext.ti, Rnext.tp
            st.R U pass.Δt η
          sys.reachAdaptiveLoop T U tFinal tol η fuelErr fuelHalf fuel     -- while
            { t := st.t + pass.Δt, R := Rnext.1, h := T.nextH h pass,      -- t, R = Rnext.tp
              adm_x := pass.err.errorInt_x, adm_y := pass.err.errorInt_y }
            (Runion ∪ Rnext.2.1.construct)                                  -- timeInt.set
        else none
    else some (Runion, st.t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
