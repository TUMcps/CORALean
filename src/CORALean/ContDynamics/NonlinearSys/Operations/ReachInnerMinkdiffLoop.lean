import CORALean.ContDynamics.NonlinearSys.Operations.LinReachInner

/-!
# `reachInnerMinkdiffLoop`, the time steps of CORA's `'minkdiff'` inner reachability

The loop `for k=1:steps` of CORA's `nonlinearSys/private/priv_reachInnerMinkdiff.m`, lines 2-17
of [1, Alg. 1]: from step
`k` (0-based here) and the start `Rtp` with its error guess, `j` more steps of
`linReachInner`, each storing its time-interval set at `timeInt.set{k}` and its time-point set
at `timePoint.set{k+1}`, and stopping (`break`) when a step reports `options.empty`. The cell
arrays are functions `ℕ → Set`; the cells a run does not reach keep what they held, the empty
set CORA's `cell(steps+1,1)` preallocates. `outputSet` is the identity, the system having no
output equation. `none` as soon as one step's error loop runs out of fuel.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `j` steps of CORA's `priv_reachInnerMinkdiff` from step `k` and the start `Rtp` with the
error `err`, on top of the cells `timePoint` and `timeInt`. -/
noncomputable def NonlinearSys.reachInnerMinkdiffLoop (ops : NonlinearSys.LinReachInnerOps n 𝓛)
    (f : Vec ℝ n → Vec ℝ n) (Δt : ℝ) (fuel : ℕ) :
    ℕ → ℕ → Set (Vec ℝ n) → Vec ℝ n → (ℕ → Set (Vec ℝ n)) → (ℕ → Set (Vec ℝ n)) →
      Option ((ℕ → Set (Vec ℝ n)) × (ℕ → Set (Vec ℝ n)))
  | 0, _, _, _, timePoint, timeInt => some (timePoint, timeInt)
  | j + 1, k, Rtp, err, timePoint, timeInt =>
    (NonlinearSys.linReachInner ops f Δt fuel Rtp err).bind fun r =>  -- linReachInner(...)
      match r with
      | none => some (timePoint, timeInt)                             -- if options.empty, break
      | some st =>
        let timeInt' := Function.update timeInt k st.Rti              -- timeInt.set{k} = Rti
        let timePoint' := Function.update timePoint (k + 1) st.Rtp    -- timePoint.set{k+1}
        NonlinearSys.reachInnerMinkdiffLoop ops f Δt fuel j (k + 1) st.Rtp st.err timePoint'
          timeInt'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
