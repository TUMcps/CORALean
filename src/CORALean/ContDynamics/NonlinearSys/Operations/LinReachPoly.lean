import CORALean.ContDynamics.LinearSys.Operations.DeltaReach
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolyCandidates
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolySearch
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatError
import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack

/-!
# One step of `linReach` at `alg = 'poly'`, end to end

CORA's `linReach` for [1, Alg. 1], lines 3-10, linearization to accepted error:
`aux_deltaReach` for `Rdiff`, `relinDeltaReach`'s shape at this step with the input
taken error-free; `priv_precompStatError` for `VerrorStat`; and the `while` loop,
whose candidates `abstrErrPolyCandidates` computes and `abstrErrPolySearch` tests.
Only what CORA takes as data is supplied: the expansion point, `A`, `B`, the Hessian
`H`, the third-order bound `E`, and the previous step's `abstrerr`.

Candidate `k` is certified by CORA's split of the second-order term: over the region
`Rinit.dependent ⊞ (Rdiff + RallError)`, start factors first, `L` is the start's
static error read over them by `padBack`, so what `W` must cover at `x = z + δ` is
exactly `VerrorDyn`'s: the products carrying `δ` and the cubic remainder. CORA's
reduction of the start before its static error is skipped, since it re-indexes the
factors `L` is read at. No termination is claimed; `linReachPoly_outer` says what a
`some` means.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of CORA's `linReach` at `alg = 'poly'` from the start set `Rinit`: the
first candidate the certificate accepts, as a `LinStep`, or `none` past `fuel`. -/
noncomputable def NonlinearSys.linReachPoly (sys : NonlinearSys n m)
    (U : PolyZonotope (Vec ℝ m)) (A : Mat ℝ n n) (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m)
    (H : Fin n → Mat ℝ (n + m) (n + m)) (E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m))
    (Δt : ℝ) (η errorOrder intermediateOrder : ℕ) (Rinit : PolyZonotope (Vec ℝ n))
    (abstrerr : Vec ℝ n) (fuel : ℕ) : Option (sys.LinStep (S := 𝒫𝒵) U) :=
  let linsys := NonlinearSys.linearize A                                  -- linearize
  let Ulin := linInput (S := 𝒫𝒵) sys.f A B xs us U (PolyZonotope.ofPoint 0) -- linParams.U
  let Rdiff := (linsys.deltaReach (S := 𝒫𝒵) Δt η Rinit).plus
    (linsys.inputSolution (S := 𝒫𝒵) Δt η Ulin)                           -- aux_deltaReach
  -- priv_precompStatError, at `Ustat = 0`: half the Hessian's state block
  let Rstat := Rinit.dependent
  let Hstat : Fin n → Mat ℝ n n :=
    fun i => (2 : ℝ)⁻¹ • (H i).submatrix (Fin.castAdd m) (Fin.castAdd m)
  let VerrorStat := precompStatError Hstat xs Rstat                       -- 0.5*quadMap(Z,H)
  let cand := NonlinearSys.abstrErrPolyCandidates A xs us H E Δt η errorOrder
    intermediateOrder U Rinit Rdiff VerrorStat abstrerr
  -- the loop: candidate `k` certified over `Rinit ⊞ (Rdiff + RallError)`
  sys.abstrErrPolySearch U A B xs us (fun k => Rstat.plus (cand k).1)
    (fun _ => {a | ∀ j, |a j| ≤ 1}) (fun k => VerrorStat.padBack (cand k).1.p) (fun _ => rfl)
    (fun _ _ ha => ha) (fun k => (cand k).2) fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
